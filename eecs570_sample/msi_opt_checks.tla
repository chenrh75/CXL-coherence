------------------------- MODULE msi_opt_checks -------------------------
EXTENDS msi_opt
\* Legal input combinations not all chosen by the current host policy.
P0 == "Proc0"
P1 == "Proc1"
C0 == "UQID0"
HID == "UQID1"
HasOpcode(r, n, op) == \E m \in DOMAIN r.Net[n]: m.mtype = op
ReadBase(kind) == [Snapshot EXCEPT !.Procs[P0].cmd = Command(kind, 0, C0, Undefined)]
ReadGO(grant) == Message("GO", Home0, H2D_RSP, 0, C0, Undefined, Undefined, grant, 0)
ReadData == Message("Data", Home0, H2D_DATA, 0, C0, Undefined, 0, Undefined, 0)
Inv(ad) == Message("SnpInv", HomeFor(ad), H2D_REQ, ad, Undefined, HID, Undefined, Undefined, 0)
EveryLegalReadGrantInEitherOrder ==
    \A kind \in Reads, grant \in MESIType:
        IF ~GOAllowed(kind, grant) THEN TRUE
        ELSE LET base == ReadBase(kind)
                 df == ProcReceive(ProcReceive(base, ReadData, P0), ReadGO(grant), P0)
                 gf == ProcReceive(ProcReceive(base, ReadGO(grant), P0), ReadData, P0)
             IN /\ df.error = "" /\ gf.error = ""
                /\ df.Procs[P0].state = "P_" \o grant /\ gf.Procs[P0].state = "P_" \o grant
                /\ df.Procs[P0].val = 0 /\ gf.Procs[P0].val = 0
                /\ df.Procs[P0].cmd = Undefined /\ gf.Procs[P0].cmd = Undefined
GOBeforeDataSnoopSeesOwnership ==
    LET granted == ProcReceive(ReadBase("RdOwn"), ReadGO("E"), P0)
        invalidated == ProcReceive(granted, Inv(0), P0)
        drained == ProcReceive(invalidated, ReadData, P0)
    IN /\ granted.Procs[P0].state = "P_E" /\ granted.Procs[P0].val = Undefined
       /\ HasOpcode(invalidated, Home0, "RspIHitSE") /\ ~HasOpcode(invalidated, Home0, "Data")
       /\ invalidated.Procs[P0].cmd # Undefined
       /\ drained.error = "" /\ drained.Procs[P0].state = "P_I"
       /\ drained.Procs[P0].val = Undefined /\ drained.Procs[P0].cmd = Undefined
SnoopMissDoesNotInvalidateAnotherAddress ==
    LET cached == [Snapshot EXCEPT !.Procs[P0].state = "P_E", !.Procs[P0].addr = 0,
                                  !.Procs[P0].val = 0]
        missed == ProcReceive(cached, Inv(1), P0)
    IN /\ missed.error = "" /\ missed.Procs = cached.Procs
       /\ HasOpcode(missed, Home1, "RspIHitI") /\ ~HasOpcode(missed, Home1, "Data")
CleanResponsesHaveNoData ==
    \A op \in {"SnpInv", "SnpData"}:
       LET cached == [Snapshot EXCEPT !.Procs[P0].state = "P_E", !.Procs[P0].addr = 0,
                                     !.Procs[P0].val = 0]
           result == ProcReceive(cached,
               Message(op, Home0, H2D_REQ, 0, Undefined, HID, Undefined, Undefined, 0), P0)
       IN /\ result.error = "" /\ ~HasOpcode(result, Home0, "Data")
          /\ HasOpcode(result, Home0, IF op = "SnpInv" THEN "RspIHitSE" ELSE "RspSHitSE")
PullUsesRspDataNotCQID ==
    LET pending == [Snapshot EXCEPT !.Procs[P0].cmd = Command("WrInv", 0, C0, 0)]
        pulled == ProcReceive(pending,
            Message("WritePull", Home0, H2D_RSP, 0, C0, Undefined, Undefined, HID, 0), P0)
    IN /\ pulled.error = "" /\ pulled.Procs[P0].cmd # Undefined
       /\ \A m \in DOMAIN pulled.Net[Home0]: m.mtype = "Data" /\ m.uqid = HID
                                             /\ m.cqid = Undefined /\ m.bogus = 0
EvictionBase(kind) == [Snapshot EXCEPT
    !.Procs[P0].state = IF kind = "CleanEvict" THEN "P_E" ELSE "P_M",
    !.Procs[P0].addr = 0, !.Procs[P0].val = 0,
    !.Procs[P0].cmd = Command(kind, 0, C0, 0)]
DropMessage == Message("GO_WritePull_Drop", Home0, H2D_RSP, 0, C0,
                       Undefined, Undefined, HID, 0)
CleanEvictDropHasNoData ==
    LET dropped == ProcReceive(EvictionBase("CleanEvict"), DropMessage, P0)
    IN /\ dropped.error = "" /\ dropped.Procs[P0].state = "P_I"
       /\ dropped.Procs[P0].cmd = Undefined /\ ~HasOpcode(dropped, Home0, "Data")
DirtyEvictDropIsRejected == ProcReceive(EvictionBase("DirtyEvict"), DropMessage, P0).error # ""
WrongCQIDIsRejected ==
    LET rejected == ProcReceive(ReadBase("RdOwn"),
            Message("GO", Home0, H2D_RSP, 0, HID, Undefined, Undefined, "E", 0), P0)
    IN /\ rejected.error # "" /\ rejected.Procs[P0].cmd # Undefined
NoDataPermissionCanBeDroppedButNotPulled ==
    LET granted == [Snapshot EXCEPT !.Procs[P0].state = "P_E", !.Procs[P0].addr = 0]
        cur == ProcReceive(granted,
            Message("SnpCur", Home0, H2D_REQ, 0, Undefined, HID, Undefined, Undefined, 0), P0)
    IN /\ ~Eligible(granted, P0, "CleanEvict") /\ Eligible(granted, P0, "CleanEvictNoData")
       /\ cur.error = "" /\ HasOpcode(cur, Home0, "RspVHitV") /\ ~HasOpcode(cur, Home0, "Data")
CacheFlushedRetainsLaunchedSnoop ==
    LET request == Message("RdOwn", P1, D2H_REQ, 1, C0, Undefined, Undefined, Undefined, 0)
        filtered == [Snapshot EXCEPT !.HomeNodes[Home0].owner = P0,
              !.HomeNodes[Home0].state = "H_E", !.HomeNodes[Home1].sharers = {P0},
              !.HomeNodes[Home1].state = "H_S"]
        started == StartRequest(filtered, Home1, request)
        flushed == CacheFlushedResult(started,
            Message("CacheFlushed", P0, D2H_REQ, Undefined, C0, Undefined,
                    Undefined, Undefined, 0))
    IN /\ flushed.error = "" /\ flushed.HomeNodes[Home0].owner = Undefined
       /\ flushed.HomeNodes[Home1].sharers = {}
       /\ flushed.HomeNodes[Home1].txn = started.HomeNodes[Home1].txn
       /\ HasOpcode(flushed, P0, "SnpInv") /\ HasOpcode(flushed, P0, "GO")
SharedSnpCurDoesNotForward ==
    LET cached == [Snapshot EXCEPT !.Procs[P0].state = "P_S", !.Procs[P0].addr = 0,
                                  !.Procs[P0].val = 0]
        current == ProcReceive(cached,
            Message("SnpCur", Home0, H2D_REQ, 0, Undefined, HID, Undefined, Undefined, 0), P0)
    IN /\ current.error = "" /\ current.Procs = cached.Procs
       /\ HasOpcode(current, Home0, "RspVHitV") /\ ~HasOpcode(current, Home0, "Data")
RdCurrForwardsWithoutHomeFill ==
    LET owned == [Snapshot EXCEPT !.Procs[P0].state = "P_M", !.Procs[P0].addr = 0,
         !.Procs[P0].val = 1, !.LastWrites[0] = 1,
         !.HomeNodes[Home0].owner = P0, !.HomeNodes[Home0].state = "H_E",
         !.Procs[P1].cmd = Command("RdCurr", 0, C0, Undefined)]
        requested == StartRequest(owned, Home0,
            Message("RdCurr", P1, D2H_REQ, 0, C0, Undefined, Undefined, Undefined, 0))
        snoop == CHOOSE m \in DOMAIN requested.Net[P0]: m.mtype = "SnpCur"
        replied == ProcReceive(requested, snoop, P0)
        rsp == CHOOSE m \in DOMAIN replied.Net[Home0]: m.mtype = "RspVFwdV"
        data == CHOOSE m \in DOMAIN replied.Net[Home0]: m.mtype = "Data"
        complete == HomeReceive(HomeReceive(replied, rsp, Home0), data, Home0)
    IN /\ complete.error = "" /\ complete.HomeNodes[Home0].val = 0
       /\ complete.HomeNodes[Home0].owner = P0 /\ complete.Procs[P0].state = "P_M"
       /\ \A m \in DOMAIN complete.Net[P1]: m.mtype = "Data" /\ m.val = 1
ProtocolChecks == /\ EveryLegalReadGrantInEitherOrder /\ GOBeforeDataSnoopSeesOwnership
    /\ SnoopMissDoesNotInvalidateAnotherAddress /\ CleanResponsesHaveNoData
    /\ PullUsesRspDataNotCQID /\ CleanEvictDropHasNoData /\ DirtyEvictDropIsRejected
    /\ WrongCQIDIsRejected /\ NoDataPermissionCanBeDroppedButNotPulled
    /\ CacheFlushedRetainsLaunchedSnoop
    /\ SharedSnpCurDoesNotForward /\ RdCurrForwardsWithoutHomeFill
CheckNext == UNCHANGED vars
=============================================================================
