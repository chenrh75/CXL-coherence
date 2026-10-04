----------------------------- MODULE msi_opt -----------------------------
\* Corrected, message-oriented model of the operations in msi_opt.m.
\* Non-device-attached memory; each device has one cacheline and one command.
\* A value denotes an entire line. Link packetization and errors are abstracted.
EXTENDS Integers, FiniteSets, Sequences, Bags, TLC

CONSTANTS ProcCount, ValueCount, MaxUQID, Undefined
ASSUME /\ ProcCount \in Nat \ {0} /\ ValueCount \in Nat \ {0}
       /\ MaxUQID \in Nat \ {0}
Home0 == "Home0"
Home1 == "Home1"
Home == {Home0, Home1}
Proc == {"Proc" \o ToString(i) : i \in 0..ProcCount-1}
Node == Home \cup Proc
Address == 0..1
Value == 0..ValueCount-1
UQIDType == {"UQID" \o ToString(i) : i \in 0..MaxUQID-1}
HomeFor(ad) == IF ad = 0 THEN Home0 ELSE Home1
AddressFor(h) == IF h = Home0 THEN 0 ELSE 1
WithUndefined(S) == S \cup {Undefined}
D2H_REQ == 0
H2D_REQ == 1
D2H_DATA == 2
D2H_RSP == 3
H2D_DATA == 4
H2D_RSP == 5
VCType == 0..5
\* There is no separate eviction wire channel. Capacity is an abstract bound
\* large enough for the reserved responses/data of the modeled transactions.
NetMax == 4*ProcCount+4
Reads == {"RdOwn", "RdShared", "RdAny"}
Evicts == {"CleanEvict", "DirtyEvict"}
Writes == {"WrInv", "WrCur", "ItoMWr"}
Read0 == {"RdOwnNoData", "CLFlush", "CacheFlushed", "CleanEvictNoData"}
Requests == Reads \cup Evicts \cup Writes \cup Read0 \cup {"RdCurr"}
Snoops == {"SnpInv", "SnpData", "SnpCur"}
SnoopResponses == {"RspIHitI", "RspIHitSE", "RspSHitSE", "RspVHitV",
                   "RspIFwdM", "RspSFwdM", "RspVFwdV"}
ForwardResponses == {"RspIFwdM", "RspSFwdM", "RspVFwdV"}
Pulls == {"WritePull", "GO_WritePull", "GO_WritePull_Drop"}
MessageTypes == Requests \cup Snoops \cup SnoopResponses \cup Pulls \cup {"GO", "Data"}
MESIType == {"I", "S", "E", "M"}
ProcStates == {"P_I", "P_S", "P_E", "P_M"}
HomeStates == {"H_I", "H_S", "H_E", "H_BUSY"}

\* addr on response/data records is an internal line annotation, derived from
\* the tracker. It is not an extra wire field in H2D responses or H2D data.
Message(t, src, vc, ad, cqid, uqid, val, rspdata, bogus) ==
    [mtype |-> t, src |-> src, vc |-> vc, addr |-> ad, cqid |-> cqid,
     uqid |-> uqid, val |-> val, rspdata |-> rspdata, bogus |-> bogus]
MessageSet == [mtype: MessageTypes, src: Node, vc: VCType,
    addr: WithUndefined(Address), cqid: WithUndefined(UQIDType),
    uqid: WithUndefined(UQIDType), val: WithUndefined(Value),
    rspdata: WithUndefined(MESIType \cup UQIDType), bogus: 0..1]
CmdRecord == [kind: Requests, addr: WithUndefined(Address), cqid: UQIDType,
    payload: WithUndefined(Value), raced: BOOLEAN, go: BOOLEAN, data: BOOLEAN,
    pulled: BOOLEAN]
TxnRecord == [request: MessageSet, phase: {"snoop", "pull"},
    snoop: Snoops, targets: SUBSET Proc,
    ids: [Proc -> WithUndefined(UQIDType)],
    responses: [Proc -> WithUndefined(SnoopResponses)],
    data: [Proc -> WithUndefined(Value)]]
HomeRecord == [state: HomeStates, owner: WithUndefined(Proc),
    sharers: SUBSET Proc, val: Value, txn: TxnRecord \cup {Undefined}]
ProcRecord == [state: ProcStates, addr: WithUndefined(Address),
    val: WithUndefined(Value), cmd: CmdRecord \cup {Undefined}]
VARIABLES HomeNodes, Procs, Net, LastWrites, error
vars == <<HomeNodes, Procs, Net, LastWrites, error>>
Snapshot == [HomeNodes |-> HomeNodes, Procs |-> Procs, Net |-> Net,
             LastWrites |-> LastWrites, error |-> error]
Fail(r, why) == IF r.error # "" THEN r ELSE [r EXCEPT !.error = why]
Require(r, condition, why) == IF condition THEN r ELSE Fail(r, why)
Push(r, dst, m) ==
    IF r.error # "" THEN r
    ELSE IF m \notin MessageSet THEN Fail(r, "Invalid message fields")
    ELSE IF BagCardinality(r.Net[dst]) >= NetMax THEN Fail(r, "Network capacity exceeded")
    ELSE [r EXCEPT !.Net[dst] = @ (+) SetToBag({m})]
Commit(r) == /\ HomeNodes' = r.HomeNodes /\ Procs' = r.Procs
             /\ Net' = r.Net /\ LastWrites' = r.LastWrites /\ error' = r.error

Init ==
    /\ HomeNodes = [h \in Home |-> [state |-> "H_I", owner |-> Undefined,
         sharers |-> {}, val |-> 0, txn |-> Undefined]]
    /\ Procs = [p \in Proc |-> [state |-> "P_I", addr |-> Undefined,
                               val |-> Undefined, cmd |-> Undefined]]
    /\ Net = [n \in Node |-> EmptyBag]
    /\ LastWrites = [ad \in Address |-> 0]
    /\ error = ""

DirectoryState(d) == IF d.owner # Undefined THEN "H_E"
                     ELSE IF d.sharers # {} THEN "H_S" ELSE "H_I"
Refresh(r, h) == [r EXCEPT !.HomeNodes[h].state = DirectoryState(r.HomeNodes[h])]
RemoveHolder(r, h, p) ==
    [r EXCEPT !.HomeNodes[h].sharers = @ \ {p},
              !.HomeNodes[h].owner = IF @ = p THEN Undefined ELSE @]
Holders(r, h) == r.HomeNodes[h].sharers \cup
    (IF r.HomeNodes[h].owner = Undefined THEN {} ELSE {r.HomeNodes[h].owner})

\* Host UQIDs are unique within a device link, across both address homes.
\* Reservation is atomic: a transaction cannot hold one link while waiting
\* to allocate the other. CQID and UQID are separate namespaces/lifetimes.
UsedIDs(r, p) == UNION {IF r.HomeNodes[h].txn = Undefined THEN {}
    ELSE IF r.HomeNodes[h].txn.ids[p] = Undefined THEN {}
    ELSE {r.HomeNodes[h].txn.ids[p]} : h \in Home}
FreeIDs(r, p) == UQIDType \ UsedIDs(r, p)
SnoopKind(kind) == CASE kind = "RdCurr" -> "SnpCur"
    [] kind \in {"RdShared", "RdAny"} -> "SnpData"
    [] OTHER -> "SnpInv"
Targets(r, h, m) ==
    IF m.mtype \in Evicts \cup {"CleanEvictNoData", "CacheFlushed"} THEN {}
    ELSE IF m.mtype \in {"RdCurr", "RdShared", "RdAny"} THEN
        IF r.HomeNodes[h].owner = Undefined THEN {} ELSE {r.HomeNodes[h].owner}
    ELSE Holders(r, h) \ {m.src}
Reservations(r, h, m) == Targets(r, h, m) \cup
    (IF m.mtype \in Writes \cup Evicts THEN {m.src} ELSE {})
CanStart(r, h, m) == /\ r.HomeNodes[h].txn = Undefined
                     /\ \A p \in Reservations(r, h, m): FreeIDs(r, p) # {}

Command(kind, ad, id, v) ==
    [kind |-> kind, addr |-> ad, cqid |-> id, payload |-> v, raced |-> FALSE,
     go |-> FALSE, data |-> FALSE, pulled |-> FALSE]
IssueResult(r, p, ad, id, kind, v) ==
    LET line == IF kind \in Evicts \cup {"CleanEvictNoData"}
                   \/ (kind = "RdOwnNoData" /\ r.Procs[p].state = "P_S")
                THEN r.Procs[p].addr ELSE ad
        cacheDropped == IF kind = "CleanEvictNoData" THEN
            [r EXCEPT !.Procs[p].state = "P_I", !.Procs[p].val = Undefined,
                      !.Procs[p].addr = Undefined] ELSE r
        addressed == IF kind = "CacheFlushed" THEN Undefined ELSE line
        payload == IF kind \in Evicts THEN r.Procs[p].val ELSE v
        tracked == [cacheDropped EXCEPT
            !.Procs[p].cmd = Command(kind, addressed, id, payload)]
        dst == IF kind = "CacheFlushed" THEN Home0 ELSE HomeFor(line)
    IN Push(tracked, dst, Message(kind, p, D2H_REQ, addressed, id,
                                 Undefined, Undefined, Undefined, 0))
Eligible(r, p, kind) ==
    /\ r.Procs[p].cmd = Undefined
    /\ CASE kind = "CleanEvict" -> r.Procs[p].state = "P_E" /\ r.Procs[p].val \in Value
         [] kind = "DirtyEvict" -> r.Procs[p].state = "P_M"
         [] kind = "CleanEvictNoData" -> r.Procs[p].state \in {"P_E", "P_S"}
         [] kind = "RdOwnNoData" -> r.Procs[p].state \in {"P_I", "P_S"}
         [] OTHER -> r.Procs[p].state = "P_I"
Issue(p, ad, id, kind, v) ==
    /\ error = "" /\ Eligible(Snapshot, p, kind)
    /\ Commit(IssueResult(Snapshot, p, ad, id, kind, v))
\* Retain the source rule names for scripts and human-readable traces.
DeviceRule1(p, ad, id) == Issue(p, ad, id, "RdOwn", Undefined)
DeviceRule2(p, ad, id) == Issue(p, ad, id, "RdAny", Undefined)
DeviceRule3(p, ad, id, v) == Issue(p, ad, id, "WrInv", v)
DeviceRule4(p, ad, id) == Issue(p, ad, id, "CleanEvict", Undefined)
DeviceRule5(p, ad, id) == /\ Procs[p].state = "P_E"
                          /\ Issue(p, ad, id, "CleanEvictNoData", Undefined)
DeviceRule6(p, ad, id, v) == Issue(p, ad, id, "WrCur", v)
DeviceRule7(p, ad, id, v) == Issue(p, ad, id, "ItoMWr", v)
DeviceRule8(p, ad, id) == Issue(p, ad, id, "RdShared", Undefined)
DeviceRule9(p, ad, id) == Issue(p, ad, id, "RdCurr", Undefined)
DeviceRule10(p, ad, id) == /\ Procs[p].state = "P_S"
                           /\ Issue(p, ad, id, "CleanEvictNoData", Undefined)
DeviceRule11(p, ad, id) == Issue(p, ad, id, "RdOwnNoData", Undefined)
DeviceRule12(p, ad, id) == Issue(p, ad, id, "CLFlush", Undefined)
DeviceRule13(p, ad, id) == Issue(p, ad, id, "CacheFlushed", Undefined)
DeviceRule14(p, ad, id) == Issue(p, ad, id, "DirtyEvict", Undefined)
DeviceRule15(p, ad, v) ==
    /\ error = "" /\ Procs[p].state = "P_E" /\ Procs[p].cmd = Undefined
    /\ Commit([Snapshot EXCEPT !.Procs[p].state = "P_M", !.Procs[p].val = v,
                              !.LastWrites[Procs[p].addr] = v])

NewTxn(r, h, m) ==
    LET reserved == Reservations(r, h, m)
    IN [request |-> m, phase |-> "snoop", snoop |-> SnoopKind(m.mtype),
        targets |-> Targets(r, h, m),
        ids |-> [p \in Proc |-> IF p \in reserved THEN
                   CHOOSE id \in FreeIDs(r, p): TRUE ELSE Undefined],
        responses |-> [p \in Proc |-> Undefined],
        data |-> [p \in Proc |-> Undefined]]
SendSnoops(r, h) ==
    LET t == r.HomeNodes[h].txn
        additions == [p \in Proc |-> IF p \in t.targets THEN
            SetToBag({Message(t.snoop, h, H2D_REQ, t.request.addr,
                              Undefined, t.ids[p], Undefined, Undefined, 0)})
            ELSE EmptyBag]
    IN [r EXCEPT !.Net = [n \in Node |-> IF n \in Proc THEN
                                             r.Net[n] (+) additions[n] ELSE r.Net[n]]]
SnoopsDone(t) == \A p \in t.targets:
    IF t.responses[p] = Undefined THEN FALSE
    ELSE t.responses[p] \notin ForwardResponses \/ t.data[p] # Undefined
SnoopValue(d) ==
    LET forwarded == {p \in d.txn.targets: d.txn.responses[p] \in ForwardResponses}
    IN IF forwarded = {} THEN d.val
       ELSE d.txn.data[CHOOSE p \in forwarded: TRUE]
SendGO(r, h, m, grant) ==
    Push(r, m.src, Message("GO", h, H2D_RSP, m.addr, m.cqid,
                          Undefined, Undefined, grant, 0))
SendReadDataValue(r, h, m, value) ==
    Push(r, m.src, Message("Data", h, H2D_DATA, m.addr, m.cqid,
                          Undefined, value, Undefined, 0))
SendReadData(r, h, m) == SendReadDataValue(r, h, m, r.HomeNodes[h].val)
BeginPull(r, h) ==
    LET t == r.HomeNodes[h].txn
        m == t.request
        removed == RemoveHolder(r, h, m.src)
        pulling == [removed EXCEPT !.HomeNodes[h].txn.phase = "pull"]
        op == IF m.mtype = "WrInv" THEN "WritePull" ELSE "GO_WritePull"
    IN Push(pulling, m.src, Message(op, h, H2D_RSP, m.addr, m.cqid,
                                   Undefined, Undefined, t.ids[m.src], 0))
FinishSnoops(r, h) ==
    LET t == r.HomeNodes[h].txn
        m == t.request
        \* SnpCur/RspVFwdV is a one-use snapshot, not a home cache fill.
        current == IF m.mtype = "RdCurr" THEN r
                   ELSE [r EXCEPT !.HomeNodes[h].val = SnoopValue(r.HomeNodes[h])]
        retired == [current EXCEPT !.HomeNodes[h].txn = Undefined]
    IN CASE m.mtype \in Writes \cup Evicts -> BeginPull(current, h)
       [] m.mtype = "RdCurr" ->
           SendReadDataValue(Refresh(retired, h), h, m, SnoopValue(r.HomeNodes[h]))
       [] m.mtype = "CLFlush" -> SendGO(Refresh(retired, h), h, m, "I")
       [] m.mtype \in Reads \cup {"RdOwnNoData"} ->
          LET shared == m.mtype = "RdShared"
                        \/ (m.mtype = "RdAny" /\ Holders(current, h) # {})
              grant == IF shared THEN "S" ELSE "E"
              installed == IF shared THEN
                  [retired EXCEPT !.HomeNodes[h].sharers = @ \cup {m.src}]
                  ELSE [retired EXCEPT !.HomeNodes[h].owner = m.src,
                                      !.HomeNodes[h].sharers = {}]
              permitted == SendGO(Refresh(installed, h), h, m, grant)
          IN IF m.mtype = "RdOwnNoData" THEN permitted ELSE SendReadData(permitted, h, m)
       [] OTHER -> Fail(r, "Unsupported transaction completion")
TryComplete(r, h) ==
    IF r.error # "" THEN r
    ELSE IF r.HomeNodes[h].txn = Undefined THEN r
    ELSE IF r.HomeNodes[h].txn.phase = "snoop" /\ SnoopsDone(r.HomeNodes[h].txn)
         THEN FinishSnoops(r, h) ELSE r

\* CacheFlushed is global for this device's one cacheline. It removes directory
\* entries at BOTH homes but keeps previously launched snoop obligations alive.
CacheFlushedResult(r, m) ==
    LET cleared == [r EXCEPT !.HomeNodes = [h \in Home |->
        LET d == r.HomeNodes[h]
            removed == [d EXCEPT !.owner = IF @ = m.src THEN Undefined ELSE @,
                                !.sharers = @ \ {m.src}]
        IN IF d.txn = Undefined THEN [removed EXCEPT !.state = DirectoryState(removed)]
           ELSE removed]]
    IN SendGO(cleared, Home0, m, "I")
StartRequest(r, h, m) ==
    IF m.mtype = "CacheFlushed" THEN CacheFlushedResult(r, m)
    ELSE IF m.addr # AddressFor(h) THEN Fail(r, "Request routed to wrong home")
    ELSE IF m.mtype = "CleanEvictNoData" THEN
        SendGO(Refresh(RemoveHolder(r, h, m.src), h), h, m, "I")
    ELSE LET started == [r EXCEPT !.HomeNodes[h].txn = NewTxn(r, h, m),
                                 !.HomeNodes[h].state = "H_BUSY"]
         IN TryComplete(SendSnoops(started, h), h)

ResponseLegal(snoop, rsp) ==
    CASE snoop = "SnpInv" -> rsp \in {"RspIHitI", "RspIHitSE", "RspIFwdM"}
      [] snoop = "SnpData" -> rsp \in {"RspIHitI", "RspSHitSE", "RspSFwdM", "RspIFwdM"}
      [] snoop = "SnpCur" -> rsp \in {"RspIHitI", "RspVHitV", "RspSHitSE",
                                      "RspSFwdM", "RspIFwdM", "RspVFwdV"}
MatchSnoop(t, m) == /\ m.src \in t.targets /\ m.uqid = t.ids[m.src]
                    /\ m.addr = t.request.addr /\ t.phase = "snoop"
HostResponse(r, h, m) ==
    LET t == r.HomeNodes[h].txn
    IN IF t = Undefined THEN Fail(r, "Snoop response without transaction")
       ELSE IF ~MatchSnoop(t, m) THEN Fail(r, "Snoop response tracker mismatch")
       ELSE IF t.responses[m.src] # Undefined THEN Fail(r, "Duplicate snoop response")
       ELSE IF ~ResponseLegal(t.snoop, m.mtype) THEN Fail(r, "Illegal snoop response")
       ELSE IF m.mtype \notin ForwardResponses /\ t.data[m.src] # Undefined
            THEN Fail(r, "Unexpected data for no-data snoop response")
       ELSE LET recorded == [r EXCEPT !.HomeNodes[h].txn.responses[m.src] = m.mtype]
                directory == CASE m.mtype \in {"RspIHitI", "RspIHitSE", "RspIFwdM"} ->
                                      RemoveHolder(recorded, h, m.src)
                   [] m.mtype \in {"RspSHitSE", "RspSFwdM"} ->
                      [recorded EXCEPT !.HomeNodes[h].owner =
                           IF @ = m.src THEN Undefined ELSE @,
                                       !.HomeNodes[h].sharers = @ \cup {m.src}]
                   [] OTHER -> recorded
            IN TryComplete(directory, h)
HostData(r, h, m) ==
    LET t == r.HomeNodes[h].txn
    IN IF t = Undefined THEN Fail(r, "Data without host tracker")
       ELSE IF m.val \notin Value THEN Fail(r, "Undefined device data")
       ELSE IF t.phase = "snoop" THEN
           IF ~MatchSnoop(t, m) \/ m.bogus # 0 THEN Fail(r, "Invalid forwarded data tracker/Bogus")
           ELSE IF t.data[m.src] # Undefined THEN Fail(r, "Duplicate forwarded data")
           ELSE IF t.responses[m.src] # Undefined /\ t.responses[m.src] \notin ForwardResponses
                THEN Fail(r, "Data for no-data snoop response")
           ELSE TryComplete([r EXCEPT !.HomeNodes[h].txn.data[m.src] = m.val], h)
       ELSE IF m.src # t.request.src \/ m.uqid # t.ids[m.src]
                    \/ m.addr # t.request.addr THEN Fail(r, "Pull data tracker mismatch")
       ELSE IF t.request.mtype \notin Evicts /\ m.bogus # 0
            THEN Fail(r, "Bogus on non-eviction write")
       ELSE LET written == IF m.bogus = 1 THEN r
                            ELSE [r EXCEPT !.HomeNodes[h].val = m.val]
                observed == IF t.request.mtype \in Writes THEN
                               [written EXCEPT !.LastWrites[m.addr] = m.val] ELSE written
                complete == Refresh([observed EXCEPT !.HomeNodes[h].txn = Undefined], h)
            IN IF t.request.mtype = "WrInv" THEN SendGO(complete, h, t.request, "I")
               ELSE complete
HomeReceive(r, m, h) ==
    CASE m.vc = D2H_REQ -> StartRequest(r, h, m)
      [] m.vc = D2H_RSP -> HostResponse(r, h, m)
      [] m.vc = D2H_DATA -> HostData(r, h, m)
      [] OTHER -> Fail(r, "Invalid host input channel")

DropCache(r, p) == [r EXCEPT !.Procs[p].state = "P_I", !.Procs[p].val = Undefined,
                            !.Procs[p].addr = Undefined]
RetireRead(r, p) ==
    LET c == r.Procs[p].cmd
    IN IF c.data /\ (c.go \/ c.kind = "RdCurr")
          THEN [r EXCEPT !.Procs[p].cmd = Undefined] ELSE r
GOAllowed(kind, grant) ==
    CASE kind = "RdShared" -> grant = "S"
      [] kind = "RdOwn" -> grant \in {"E", "M"}
      [] kind = "RdAny" -> grant \in {"S", "E", "M"}
      [] kind = "RdOwnNoData" -> grant = "E"
      [] kind \in {"CLFlush", "CacheFlushed", "CleanEvictNoData", "WrInv"} -> grant = "I"
      [] OTHER -> FALSE
DeviceGO(r, p, m) ==
    LET c == r.Procs[p].cmd
    IN IF ~GOAllowed(c.kind, m.rspdata) \/ c.go THEN Fail(r, "Illegal/duplicate GO")
       ELSE IF c.kind = "WrInv" /\ ~c.pulled THEN Fail(r, "GO before WrInv pull/data")
       ELSE LET granted == [r EXCEPT !.Procs[p].cmd.go = TRUE]
                permission == IF m.rspdata = "I" THEN DropCache(granted, p)
                    ELSE [granted EXCEPT !.Procs[p].state = "P_" \o m.rspdata,
                                         !.Procs[p].addr = c.addr]
            IN IF c.kind \in Reads THEN RetireRead(permission, p)
               ELSE [permission EXCEPT !.Procs[p].cmd = Undefined]
DeviceData(r, p, m) ==
    LET c == r.Procs[p].cmd
    IN IF c.kind \notin Reads \cup {"RdCurr"} \/ c.data \/ m.val \notin Value
          THEN Fail(r, "Illegal/duplicate H2D data")
       ELSE LET tracked == [r EXCEPT !.Procs[p].cmd.data = TRUE,
                                    !.Procs[p].cmd.payload = m.val]
                cached == IF c.kind = "RdCurr" THEN tracked
                    ELSE IF ~c.go THEN tracked
                    ELSE IF r.Procs[p].state = "P_I" THEN tracked
                    ELSE [tracked EXCEPT !.Procs[p].val = m.val]
            IN RetireRead(cached, p)
DevicePull(r, p, m) ==
    LET c == r.Procs[p].cmd
    IN IF m.rspdata \notin UQIDType \/ c.pulled THEN Fail(r, "Illegal/duplicate pull")
       ELSE IF (c.kind = "WrInv" /\ m.mtype # "WritePull")
                \/ (c.kind \in Evicts \cup {"WrCur", "ItoMWr"} /\ m.mtype = "WritePull")
                \/ c.kind \notin Writes \cup Evicts
                \/ (m.mtype = "GO_WritePull_Drop" /\ c.kind # "CleanEvict")
            THEN Fail(r, "Pull opcode/request mismatch")
       ELSE LET dropped == DropCache(r, p)
                marked == [dropped EXCEPT !.Procs[p].cmd.pulled = TRUE]
                sent == IF m.mtype = "GO_WritePull_Drop" THEN marked
                    ELSE Push(marked, m.src,
                        Message("Data", p, D2H_DATA, c.addr, Undefined, m.rspdata,
                                c.payload, Undefined,
                                IF c.kind \in Evicts /\ c.raced THEN 1 ELSE 0))
            IN IF c.kind = "WrInv" THEN sent ELSE [sent EXCEPT !.Procs[p].cmd = Undefined]
DeviceResponse(r, p, m) ==
    LET c == r.Procs[p].cmd
    IN IF c = Undefined THEN Fail(r, "Response without device command")
       ELSE IF m.cqid # c.cqid \/ m.addr # c.addr
               \/ m.src # (IF c.kind = "CacheFlushed" THEN Home0 ELSE HomeFor(c.addr))
            THEN Fail(r, "Device response CQID/address/source mismatch")
       ELSE CASE m.mtype = "GO" ->
                LET permitted == DeviceGO(r, p, m)
                IN IF permitted.error # "" THEN permitted
                   ELSE IF c.kind \in Reads /\ c.data /\ m.rspdata # "I" THEN
                           [permitted EXCEPT !.Procs[p].val = c.payload]
                        ELSE permitted
         [] m.mtype \in Pulls -> DevicePull(r, p, m)
         [] OTHER -> Fail(r, "Invalid device response opcode")
DeviceReadData(r, p, m) ==
    LET c == r.Procs[p].cmd
    IN IF c = Undefined THEN Fail(r, "Read data without device command")
       ELSE IF m.cqid # c.cqid \/ m.addr # c.addr \/ m.src # HomeFor(c.addr)
            THEN Fail(r, "Read data CQID/address/source mismatch")
       ELSE DeviceData(r, p, m)
SnoopHit(r, p, m) == r.Procs[p].addr = m.addr /\ r.Procs[p].state # "P_I"
SnoopReply(r, p, m) ==
    IF ~SnoopHit(r, p, m) THEN "RspIHitI"
    ELSE CASE m.mtype = "SnpInv" ->
                  IF r.Procs[p].state = "P_M" THEN "RspIFwdM" ELSE "RspIHitSE"
       [] m.mtype = "SnpData" ->
                  IF r.Procs[p].state = "P_M" THEN "RspSFwdM" ELSE "RspSHitSE"
       [] m.mtype = "SnpCur" ->
                  IF r.Procs[p].state = "P_S"
                     \/ (r.Procs[p].val = Undefined /\ r.Procs[p].state # "P_M")
                  THEN "RspVHitV" ELSE "RspVFwdV"
DeviceSnoop(r, p, m) ==
    LET rsp == SnoopReply(r, p, m)
        hit == SnoopHit(r, p, m)
        changing == hit /\ (m.mtype = "SnpInv"
                           \/ (m.mtype = "SnpData" /\ r.Procs[p].state # "P_S"))
        raced == IF r.Procs[p].cmd = Undefined THEN r
                 ELSE IF changing /\ r.Procs[p].cmd.kind \in Evicts THEN
                      [r EXCEPT !.Procs[p].cmd.raced = TRUE] ELSE r
        changed == IF ~hit THEN raced
                   ELSE IF m.mtype = "SnpInv" THEN DropCache(raced, p)
                   ELSE IF m.mtype = "SnpData" THEN
                       [raced EXCEPT !.Procs[p].state = "P_S"] ELSE raced
        response == Push(changed, m.src, Message(rsp, p, D2H_RSP, m.addr,
                                                Undefined, m.uqid, Undefined, Undefined, 0))
    IN IF rsp \in ForwardResponses THEN
           Push(response, m.src, Message("Data", p, D2H_DATA, m.addr, Undefined,
                                        m.uqid, r.Procs[p].val, Undefined, 0))
       ELSE response
ProcReceive(r, m, p) ==
    CASE m.vc = H2D_REQ -> DeviceSnoop(r, p, m)
      [] m.vc = H2D_RSP -> DeviceResponse(r, p, m)
      [] m.vc = H2D_DATA -> DeviceReadData(r, p, m)
      [] OTHER -> Fail(r, "Invalid device input channel")

\* A snoop cannot bypass a queued same-line GO. Permission is updated on GO,
\* even if data is still in flight. Only data-dependent snoop work waits for
\* missing data; response and data channels can always pass the snoop.
CanSnoop(r, p, m) ==
    /\ ~\E go \in DOMAIN r.Net[p]: go.mtype = "GO" /\ go.addr = m.addr
    /\ IF SnoopReply(r, p, m) \in ForwardResponses THEN r.Procs[p].val \in Value ELSE TRUE
Ready(r, n, m) ==
    IF n \in Home THEN
        IF m.vc = D2H_REQ THEN
            IF m.mtype = "CacheFlushed" THEN TRUE ELSE CanStart(r, n, m)
        ELSE TRUE
    ELSE IF m.vc = H2D_REQ THEN CanSnoop(r, n, m) ELSE TRUE
DeliverNetwork(n, m) ==
    /\ error = "" /\ m \in DOMAIN Net[n] /\ Ready(Snapshot, n, m)
    /\ LET removed == [Snapshot EXCEPT !.Net[n] = @ (-) SetToBag({m})]
           received == IF n \in Home THEN HomeReceive(removed, m, n)
                       ELSE ProcReceive(removed, m, n)
       IN Commit(received)
DeliverChannel(vc) == \E n \in Node: \E m \in DOMAIN Net[n]:
    m.vc = vc /\ DeliverNetwork(n, m)
DeviceToHomeRequest == DeliverChannel(D2H_REQ)
HomeToDeviceRequest == DeliverChannel(H2D_REQ)
DeviceToHomeData == DeliverChannel(D2H_DATA)
DeviceToHomeResponse == DeliverChannel(D2H_RSP)
HomeToDeviceData == DeliverChannel(H2D_DATA)
HomeToDeviceResponse == DeliverChannel(H2D_RSP)
DrainNext == \E n \in Node: \E m \in DOMAIN Net[n]: DeliverNetwork(n, m)
Next ==
    \/ \E p \in Proc, ad \in Address, id \in UQIDType:
        \/ DeviceRule1(p, ad, id) \/ DeviceRule2(p, ad, id)
        \/ DeviceRule4(p, ad, id) \/ DeviceRule5(p, ad, id)
        \/ DeviceRule8(p, ad, id) \/ DeviceRule9(p, ad, id)
        \/ DeviceRule10(p, ad, id) \/ DeviceRule11(p, ad, id)
        \/ DeviceRule12(p, ad, id) \/ DeviceRule13(p, ad, id)
        \/ DeviceRule14(p, ad, id)
    \/ \E p \in Proc, ad \in Address, id \in UQIDType, v \in Value:
        \/ DeviceRule3(p, ad, id, v) \/ DeviceRule6(p, ad, id, v)
        \/ DeviceRule7(p, ad, id, v)
    \/ \E p \in Proc, ad \in Address, v \in Value: DeviceRule15(p, ad, v)
    \/ DrainNext
Spec == Init /\ [][Next]_vars
DeliverFrom(n, src, vc) == \E m \in DOMAIN Net[n]:
    m.src = src /\ m.vc = vc /\ DeliverNetwork(n, m)
DeliverDeviceRequest(p) == \E h \in Home: DeliverFrom(h, p, D2H_REQ)
\* A device has at most one queued request. Strong fairness prevents repeated
\* competing requests from starving it when a home/resource becomes free.
\* Responses and data become continuously enabled; weak fairness suffices.
FairSpec ==
    /\ Spec
    /\ (\A p \in Proc: SF_vars(DeliverDeviceRequest(p)))
    /\ (\A h \in Home, p \in Proc:
        /\ WF_vars(DeliverFrom(p, h, H2D_RSP))
        /\ WF_vars(DeliverFrom(p, h, H2D_DATA))
        /\ WF_vars(DeliverFrom(p, h, H2D_REQ))
        /\ WF_vars(DeliverFrom(h, p, D2H_RSP))
        /\ WF_vars(DeliverFrom(h, p, D2H_DATA)))
RequestProgress == \A p \in Proc: (Procs[p].cmd # Undefined) ~> (Procs[p].cmd = Undefined)
Quiescent == /\ \A n \in Node: Net[n] = EmptyBag
             /\ \A p \in Proc: Procs[p].cmd = Undefined
             /\ \A h \in Home: HomeNodes[h].txn = Undefined

TypeOK ==
    /\ HomeNodes \in [Home -> HomeRecord] /\ Procs \in [Proc -> ProcRecord]
    /\ LastWrites \in [Address -> Value] /\ error \in STRING
    /\ DOMAIN Net = Node
    /\ \A n \in Node: IsABag(Net[n]) /\ DOMAIN Net[n] \subseteq MessageSet
                        /\ BagCardinality(Net[n]) <= NetMax
NoErrors == error = ""
SingleWriter == \A p, q \in Proc:
    p # q /\ Procs[p].addr = Procs[q].addr /\ Procs[p].state \in {"P_E", "P_M"}
        => Procs[q].state = "P_I"
ReadableCopiesFresh == \A p \in Proc:
    IF Procs[p].state = "P_I" \/ Procs[p].val = Undefined THEN TRUE
    ELSE Procs[p].val = LastWrites[Procs[p].addr]
CacheShape == \A p \in Proc:
    /\ (Procs[p].state = "P_I" => Procs[p].val = Undefined /\ Procs[p].addr = Undefined)
    /\ (Procs[p].state # "P_I" => Procs[p].addr \in Address)
    /\ (Procs[p].state = "P_M" => Procs[p].val \in Value
          \/ (IF Procs[p].cmd = Undefined THEN FALSE
              ELSE Procs[p].cmd.kind \in Reads /\ Procs[p].cmd.go /\ ~Procs[p].cmd.data))
DirectoryShape == \A h \in Home:
    /\ (HomeNodes[h].owner # Undefined => HomeNodes[h].sharers = {})
    /\ (HomeNodes[h].txn = Undefined => HomeNodes[h].state = DirectoryState(HomeNodes[h]))
    /\ (HomeNodes[h].txn # Undefined => HomeNodes[h].state = "H_BUSY")
DirectoryCoversCaches == \A p \in Proc:
    IF Procs[p].state = "P_I" THEN TRUE
    ELSE LET h == HomeFor(Procs[p].addr)
             t == HomeNodes[h].txn
         IN p \in Holders(Snapshot, h)
            \/ (IF t = Undefined THEN FALSE
                ELSE t.phase = "pull" /\ t.request.src = p /\ t.request.mtype \in Evicts)
QueuedMessages == UNION {DOMAIN Net[n]: n \in Node}
ChannelCorrect == \A n \in Node: \A m \in DOMAIN Net[n]:
    CASE m.mtype \in Requests -> n \in Home /\ m.src \in Proc /\ m.vc = D2H_REQ
      [] m.mtype \in Snoops -> n \in Proc /\ m.src \in Home /\ m.vc = H2D_REQ
      [] m.mtype \in SnoopResponses -> n \in Home /\ m.src \in Proc /\ m.vc = D2H_RSP
      [] m.mtype \in Pulls \cup {"GO"} -> n \in Proc /\ m.src \in Home /\ m.vc = H2D_RSP
      [] m.mtype = "Data" ->
           (n \in Proc /\ m.src \in Home /\ m.vc = H2D_DATA)
           \/ (n \in Home /\ m.src \in Proc /\ m.vc = D2H_DATA)
DefinedIDs == \A m \in QueuedMessages:
    /\ (m.vc \in {D2H_REQ, H2D_RSP, H2D_DATA} => m.cqid \in UQIDType)
    /\ (m.vc \in {H2D_REQ, D2H_RSP, D2H_DATA} => m.uqid \in UQIDType)
    /\ (m.mtype \in {"WritePull", "GO_WritePull"} => m.rspdata \in UQIDType)
CorrectHomeAddress == \A h \in Home: \A m \in DOMAIN Net[h]:
    m.mtype # "CacheFlushed" => m.addr = AddressFor(h)
DeviceCorrelation == \A p \in Proc: \A m \in DOMAIN Net[p]:
    IF m.vc \notin {H2D_RSP, H2D_DATA} THEN TRUE
    ELSE IF Procs[p].cmd = Undefined THEN FALSE
    ELSE /\ m.cqid = Procs[p].cmd.cqid /\ m.addr = Procs[p].cmd.addr
         /\ IF m.mtype = "GO" THEN GOAllowed(Procs[p].cmd.kind, m.rspdata) ELSE TRUE
HostCorrelation == \A h \in Home: \A m \in DOMAIN Net[h]:
    IF m.vc \notin {D2H_RSP, D2H_DATA} THEN TRUE
    ELSE IF HomeNodes[h].txn = Undefined THEN FALSE
    ELSE LET t == HomeNodes[h].txn
         IN /\ m.uqid = t.ids[m.src] /\ m.addr = t.request.addr
            /\ IF t.phase = "pull" THEN m.src = t.request.src /\ m.vc = D2H_DATA
               ELSE m.src \in t.targets /\ m.bogus = 0
UniqueHostIDs == \A p \in Proc:
    LET active == {h \in Home: IF HomeNodes[h].txn = Undefined THEN FALSE
                              ELSE HomeNodes[h].txn.ids[p] # Undefined}
    IN Cardinality(UsedIDs(Snapshot, p)) = Cardinality(active)
NoEarlyGrant == \A h \in Home:
    IF HomeNodes[h].txn = Undefined THEN TRUE
    ELSE LET t == HomeNodes[h].txn
         IN IF t.phase # "snoop" THEN TRUE
            ELSE ~\E m \in DOMAIN Net[t.request.src]:
                m.src = h /\ m.addr = t.request.addr /\ m.cqid = t.request.cqid
                /\ m.mtype \in Pulls \cup {"GO"}
DataDefined == \A m \in QueuedMessages: m.mtype = "Data" => m.val \in Value
ForwardDataObligations == \A h \in Home:
    IF HomeNodes[h].txn = Undefined THEN TRUE
    ELSE LET t == HomeNodes[h].txn
         IN \A p \in t.targets: t.data[p] # Undefined =>
              t.responses[p] = Undefined \/ t.responses[p] \in ForwardResponses
NoSnoopPullOverlap == \A h \in Home:
    IF HomeNodes[h].txn = Undefined THEN TRUE
    ELSE LET t == HomeNodes[h].txn
         IN t.phase = "pull" =>
              ~\E p \in Proc: \E m \in DOMAIN Net[p]:
                 m.src = h /\ m.addr = t.request.addr /\ m.mtype \in Snoops
\* Unlike a global Next deadlock check, this does not count the ability to
\* issue unrelated new commands as progress on an existing transaction.
PendingWorkCanDrain == Quiescent \/
    (\E n \in Node: \E m \in DOMAIN Net[n]: Ready(Snapshot, n, m))
InvalidImpliesEmptyOwner == \A h \in Home:
    HomeNodes[h].state = "H_I" => HomeNodes[h].owner = Undefined
MemoryMatchesLastWrite(ad) ==
    HomeNodes[HomeFor(ad)].state \in {"H_I", "H_S"}
        => HomeNodes[HomeFor(ad)].val = LastWrites[ad]
Address0MemoryMatchesLastWrite == MemoryMatchesLastWrite(0)
Address1MemoryMatchesLastWrite == MemoryMatchesLastWrite(1)
ModifiedImpliesNoSharers == \A h \in Home: HomeNodes[h].owner # Undefined
                                               => HomeNodes[h].sharers = {}
InvalidImpliesNoSharers == \A h \in Home:
    HomeNodes[h].state = "H_I" => HomeNodes[h].sharers = {}
SharedValuesMatchMemory(ad) == \A p \in Proc:
    HomeNodes[HomeFor(ad)].state = "H_S" /\ Procs[p].state = "P_S"
        /\ Procs[p].addr = ad => Procs[p].val = Undefined
                                  \/ Procs[p].val = HomeNodes[HomeFor(ad)].val
Address0SharedValuesMatchMemory == SharedValuesMatchMemory(0)
Address1SharedValuesMatchMemory == SharedValuesMatchMemory(1)
Safety == /\ NoErrors /\ SingleWriter /\ ReadableCopiesFresh /\ CacheShape
          /\ DirectoryShape /\ DirectoryCoversCaches /\ ChannelCorrect
          /\ DefinedIDs /\ CorrectHomeAddress /\ DeviceCorrelation
          /\ HostCorrelation /\ UniqueHostIDs /\ NoEarlyGrant
          /\ DataDefined /\ ForwardDataObligations /\ NoSnoopPullOverlap /\ PendingWorkCanDrain
          /\ Address0MemoryMatchesLastWrite /\ Address1MemoryMatchesLastWrite
=============================================================================
