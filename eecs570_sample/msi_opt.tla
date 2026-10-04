----------------------------- MODULE msi_opt -----------------------------
\* Translation of eecs570_sample/msi_opt.m.
\* Sequential procedure statements are pure record transformations. Each
\* processor rule or delivery commits one such result as one atomic action.
EXTENDS Integers, FiniteSets, Sequences, Bags, TLC

CONSTANTS ProcCount, ValueCount, MaxUQID, Undefined
ASSUME /\ ProcCount > 0 /\ ValueCount > 0 /\ MaxUQID > 0
       /\ ProcCount \in Nat /\ ValueCount \in Nat /\ MaxUQID \in Nat
HomeCount == 2
AddrCount == 2
QMax == 6 \* Declared but unused in the source.
Home0 == "Home0"
Home1 == "Home1"
Home == {Home0, Home1}
HomeOrder == <<Home0, Home1>>
ProcOrder == [i \in 1..ProcCount |-> "Proc" \o ToString(i-1)]
Proc == {ProcOrder[i] : i \in DOMAIN ProcOrder}
Node == Home \cup Proc
NodeOrder == HomeOrder \o ProcOrder
UQIDType == {"UQID" \o ToString(i) : i \in 0..MaxUQID-1}
Value == 0..ValueCount-1
Address == 0..AddrCount-1
SharerNum == 0..ProcCount
MESIType == {"M", "E", "S", "I"}
RspData == UQIDType \cup MESIType
D2H_REQ == 0
H2D_REQ == 1
D2H_DATA == 2
D2H_RSP == 3
H2D_DATA == 4
H2D_RSP == 5
D2H_REQ2 == 6
NumVCs == 7
VCType == 0..NumVCs-1
NetMax == ProcCount*2+1
WithUndefined(S) == S \cup {Undefined}

MessageTypes == {
    "RdCurr", "RdOwn", "RdShared", "RdAny", "RdOwnNoData", "ItoMWr",
    "WrCur", "CLFlush", "CleanEvict", "DirtyEvict", "CleanEvictNoData", "WrInv",
    "CacheFlushed", "RspIHitI", "RspVHitV", "RspIHitSE", "RspSHitSE", "RspSFwdM",
    "RspIFwdM", "RspVFwdV", "WritePull", "GO", "GO_WritePull", "ExtCmp",
    "GO_WritePull_Drop", "Reserved", "Fast_GO_WritePull", "GO_ERR_WritePull", "SnpData", "SnpInv",
    "SnpCur", "Data"}
HomeStates == {
    "H_M", "H_E", "H_S", "H_I", "HT_SI_A", "HT_SI_D",
    "HT_SI_AD", "HT_SE_AD", "HT_II_A", "HT_II_D", "HT_II_AD", "HT_IS_AD",
    "HT_IS_A", "HT_IS_D", "HT_IE_AD", "HT_IE_D", "HT_IE_A", "HT_MM_AD",
    "HT_MM_A", "HT_MM_D", "HT_MI_AD", "HT_MI_D", "HT_MI_A", "HT_MI_AD1",
    "HT_MI_A1", "HT_MI_D1", "HT_ME_AD", "HT_ME_A", "HT_ME_D", "HT_EI_AD",
    "HT_EI_A", "HT_EI_D", "HT_EE_AD", "HT_EE_A", "HT_EE_D", "HT_ES_AD",
    "HT_ES_A", "HT_ES_D", "HT_MS_AD", "HT_MS_D", "HT_MS_A"}
ProcStates == {
    "P_M", "P_E", "P_S", "P_I", "PT_MI_GP", "PT_IM_A",
    "PT_IM_D", "PT_IM_AD", "PT_MI_A", "PT_II_GOI", "PT_II_WP", "PT_II_GO",
    "PT_EI_GOI", "PT_EI_GP", "PT_SE_GOE", "PT_IS_A", "PT_IS_D", "PT_IS_AD",
    "PT_SI_GOI", "PT_SI_GP", "PT_IE_AD", "PT_IE_D", "PT_IE_A", "PT_II_GP",
    "PT_II_D", "PT_SE_A", "PT_SM_GOE"}
Flags == {
    "flag_EM_D", "flag_EI_D", "flag_EE_D", "flag_ES_D", "flag_SI_A"}

MessageSet == [valid: WithUndefined(0..1), mtype: WithUndefined(MessageTypes),
    src: WithUndefined(Node), vc: WithUndefined(VCType), val: WithUndefined(Value),
    addr: WithUndefined(Address), cqid: WithUndefined(UQIDType), uqid: WithUndefined(UQIDType),
    nt: WithUndefined(0..1), chunkvalid: WithUndefined(0..1), poison: WithUndefined(0..1),
    bogus: WithUndefined(0..1), go_err: WithUndefined(0..1),
    rspdata: WithUndefined(RspData), rsp_pre: WithUndefined(0..3)]
HomeRecord == [state: WithUndefined(HomeStates), owner: WithUndefined(Node),
    sharers: SUBSET Node, val: WithUndefined(Value), requester: WithUndefined(Node),
    request_type: WithUndefined(MessageTypes), request_pre: WithUndefined(0..1),
    snp_data_sent: WithUndefined(0..1), snp_cur_sent: WithUndefined(0..1),
    flag: WithUndefined(Flags)]
ProcRecord == [state: WithUndefined(ProcStates), val: WithUndefined(Value),
    addr: WithUndefined(Address), mem_write_val: WithUndefined(Value)]

VARIABLES HomeNodes, Procs, Net, InBox, msg_processed, LastWrites, error
vars == <<HomeNodes, Procs, Net, InBox, msg_processed, LastWrites, error>>
Snapshot == [HomeNodes |-> HomeNodes, Procs |-> Procs, Net |-> Net,
    InBox |-> InBox, msg_processed |-> msg_processed, LastWrites |-> LastWrites,
    error |-> error, cnt |-> Undefined]

\* Failures stop the current procedure and remain visible to NoErrors.
Fail(r, reason) == IF r.error # "" THEN r ELSE [r EXCEPT !.error = reason]
Check(r, condition, reason, line) ==
    IF r.error # "" THEN r ELSE IF condition THEN r
    ELSE Fail(r, reason \o " (msi_opt.m:" \o ToString(line) \o ")")
ErrorUnhandledMsg(r, msg, n) == Fail(r, "Unhandled message type at " \o ToString(n) \o ": " \o msg.mtype)
ErrorUnhandledState(r) == Fail(r, "Unhandled state!")

\* Add one message at a time: the capacity assertion occurs before the
\* receive action removes its input message, matching the Murphi procedure.
Send(r, mtype, dst, src, vc, val, addr, cqid, uqid, nt, chunkvalid,
     poison, bogus, go_err, rspdata, rsp_pre) ==
    LET msg == [valid |-> 1, mtype |-> mtype, src |-> src, vc |-> vc,
                val |-> val, addr |-> addr, cqid |-> cqid, uqid |-> uqid,
                nt |-> nt, chunkvalid |-> chunkvalid, poison |-> poison,
                bogus |-> bogus, go_err |-> go_err, rspdata |-> rspdata,
                rsp_pre |-> rsp_pre]
    IN IF r.error # "" THEN r
       ELSE IF dst \notin Node THEN Fail(r, "Undefined or invalid send destination")
       ELSE IF msg \notin MessageSet THEN Fail(r, "Message field type/range error")
       ELSE IF BagCardinality(r.Net[dst]) >= NetMax THEN Fail(r, "Too many messages")
       ELSE [r EXCEPT !.Net[dst] = (@ (+) SetToBag({msg}))]

AddToSharersList(r, n, h) ==
    IF r.error # "" THEN r
    ELSE IF n \in r.HomeNodes[h].sharers THEN r
    ELSE IF n \notin Node THEN Fail(r, "Invalid sharer")
    ELSE IF Cardinality(r.HomeNodes[h].sharers) >= ProcCount THEN Fail(r, "Too many sharers")
    ELSE [r EXCEPT !.HomeNodes[h].sharers = @ \cup {n}]
RemoveFromSharersList(r, n, h) ==
    IF r.error # "" THEN r ELSE [r EXCEPT !.HomeNodes[h].sharers = @ \ {n}]

RECURSIVE Fold(_, _, _)
Fold(F(_, _), r, xs) ==
    IF Len(xs) = 0 THEN r ELSE Fold(F, F(r, Head(xs)), Tail(xs))


Home_H_I_RdCurr_5(r, msg, h) ==
    LET
        \* msi_opt.m:472
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_I" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:472")
        \* msi_opt.m:473
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "Data", msg.src, h, H2D_DATA, step1.HomeNodes[h].val, Undefined, msg.cqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
    IN step2

Home_H_I_RdOwn_6(r, msg, h) ==
    LET
        \* msi_opt.m:478
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_E" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_E"]
                ELSE Fail(r, "Type/range error at msi_opt.m:478")
        \* msi_opt.m:480
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step1, "Type/range error at msi_opt.m:480")
        \* msi_opt.m:481
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step2, "Type/range error at msi_opt.m:481")
        \* msi_opt.m:482
        step4 == IF step3.error # "" THEN step3
                 ELSE IF 1 \in (0..1) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_pre = 1]
                ELSE Fail(step3, "Type/range error at msi_opt.m:482")
        \* msi_opt.m:484
        step5 == IF step4.error # "" THEN step4
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].owner = msg.src]
                ELSE Fail(step4, "Type/range error at msi_opt.m:484")
        \* msi_opt.m:485
        step6 == IF step5.error # "" THEN step5
                 ELSE Send(step5, "GO", msg.src, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "E", 1)
        \* msi_opt.m:488
        step7 == IF step6.error # "" THEN step6
                 ELSE Send(step6, "Data", msg.src, h, H2D_DATA, step6.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:492
        step8 == IF step7.error # "" THEN step7
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step7 EXCEPT !.HomeNodes[h].owner = msg.src]
                ELSE Fail(step7, "Type/range error at msi_opt.m:492")
    IN step8

Home_H_I_DirtyEvict_7(r, msg, h) ==
    LET
        \* msi_opt.m:495
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_II_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_II_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:495")
        \* msi_opt.m:496
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO_WritePull", msg.src, h, H2D_REQ, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "I", 1)
        \* msi_opt.m:499
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step2, "Type/range error at msi_opt.m:499")
        \* msi_opt.m:500
        step4 == IF step3.error # "" THEN step3
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step3, "Type/range error at msi_opt.m:500")
        \* msi_opt.m:501
        step5 == IF step4.error # "" THEN step4
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(step4, "Type/range error at msi_opt.m:501")
    IN step5

Home_H_I_CleanEvict_8(r, msg, h) ==
    LET
        \* msi_opt.m:504
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_II_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_II_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:504")
        \* msi_opt.m:505
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO_WritePull", msg.src, h, H2D_REQ, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "I", 1)
        \* msi_opt.m:508
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step2, "Type/range error at msi_opt.m:508")
        \* msi_opt.m:509
        step4 == IF step3.error # "" THEN step3
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step3, "Type/range error at msi_opt.m:509")
        \* msi_opt.m:510
        step5 == IF step4.error # "" THEN step4
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(step4, "Type/range error at msi_opt.m:510")
    IN step5

Home_H_I_CleanEvictNoData_9(r, msg, h) ==
    LET
        \* msi_opt.m:513
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_I" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:513")
        \* msi_opt.m:514
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO", msg.src, h, H2D_RSP, Undefined, Undefined, msg.cqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "I", 1)
    IN step2

Home_H_I_CLFlush_10(r, msg, h) ==
    LET
        \* msi_opt.m:519
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_I" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:519")
        \* msi_opt.m:520
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO", msg.src, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "I", 1)
    IN step2

Home_H_I_ItoMWr_11(r, msg, h) ==
    LET
        \* msi_opt.m:524
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_II_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_II_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:524")
        \* msi_opt.m:526
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO_WritePull", msg.src, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
        \* msi_opt.m:529
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step2, "Type/range error at msi_opt.m:529")
        \* msi_opt.m:530
        step4 == IF step3.error # "" THEN step3
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step3, "Type/range error at msi_opt.m:530")
        \* msi_opt.m:531
        step5 == IF step4.error # "" THEN step4
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(step4, "Type/range error at msi_opt.m:531")
    IN step5

Home_H_I_RdShared_13(r, msg, h) ==
    LET
        \* msi_opt.m:542
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_S" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_S"]
                ELSE Fail(r, "Type/range error at msi_opt.m:542")
        \* msi_opt.m:543
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO", msg.src, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "S", 1)
        \* msi_opt.m:546
        step3 == IF step2.error # "" THEN step2
                 ELSE AddToSharersList(step2, msg.src, h)
    IN step3

Home_H_I_RdShared_14(r, msg, h) ==
    LET
        \* msi_opt.m:536
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_E" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_E"]
                ELSE Fail(r, "Type/range error at msi_opt.m:536")
        \* msi_opt.m:537
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO", msg.src, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "E", 1)
        \* msi_opt.m:540
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].owner = msg.src]
                ELSE Fail(step2, "Type/range error at msi_opt.m:540")
    IN step3

Home_H_I_RdShared_12(r, msg, h) ==
    LET
        \* msi_opt.m:535
        step1 == IF r.error # "" THEN r
                 ELSE IF ((r.HomeNodes[h].sharers = {})) THEN Home_H_I_RdShared_14(r, msg, h)
                ELSE Home_H_I_RdShared_13(r, msg, h)
        \* msi_opt.m:548
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "Data", msg.src, h, H2D_DATA, step1.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
    IN step2

Home_H_I_RdAny_16(r, msg, h) ==
    LET
        \* msi_opt.m:561
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_S" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_S"]
                ELSE Fail(r, "Type/range error at msi_opt.m:561")
        \* msi_opt.m:562
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO", msg.src, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "S", 1)
        \* msi_opt.m:565
        step3 == IF step2.error # "" THEN step2
                 ELSE AddToSharersList(step2, msg.src, h)
    IN step3

Home_H_I_RdAny_17(r, msg, h) ==
    LET
        \* msi_opt.m:555
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_M" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_M"]
                ELSE Fail(r, "Type/range error at msi_opt.m:555")
        \* msi_opt.m:556
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO", msg.src, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "M", 1)
        \* msi_opt.m:559
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].owner = msg.src]
                ELSE Fail(step2, "Type/range error at msi_opt.m:559")
    IN step3

Home_H_I_RdAny_15(r, msg, h) ==
    LET
        \* msi_opt.m:554
        step1 == IF r.error # "" THEN r
                 ELSE IF ((r.HomeNodes[h].sharers = {})) THEN Home_H_I_RdAny_17(r, msg, h)
                ELSE Home_H_I_RdAny_16(r, msg, h)
        \* msi_opt.m:567
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "Data", msg.src, h, H2D_DATA, step1.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
    IN step2

Home_H_I_RdOwnNoData_18(r, msg, h) ==
    LET
        \* msi_opt.m:573
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_E" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_E"]
                ELSE Fail(r, "Type/range error at msi_opt.m:573")
        \* msi_opt.m:574
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].owner = msg.src]
                ELSE Fail(step1, "Type/range error at msi_opt.m:574")
        \* msi_opt.m:575
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO", msg.src, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "E", 1)
    IN step3

Home_H_I_WrCur_19(r, msg, h) ==
    LET
        \* msi_opt.m:583
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_II_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_II_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:583")
        \* msi_opt.m:585
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO_WritePull", msg.src, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
        \* msi_opt.m:588
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step2, "Type/range error at msi_opt.m:588")
        \* msi_opt.m:589
        step4 == IF step3.error # "" THEN step3
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step3, "Type/range error at msi_opt.m:589")
        \* msi_opt.m:590
        step5 == IF step4.error # "" THEN step4
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(step4, "Type/range error at msi_opt.m:590")
    IN step5

Home_H_I_CacheFlushed_20(r, msg, h) ==
    LET
        \* msi_opt.m:594
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_I" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:594")
        \* msi_opt.m:599
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO", msg.src, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "I", 1)
    IN step2

Home_H_I_WrInv_21(r, msg, h) ==
    LET
        \* msi_opt.m:604
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_II_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_II_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:604")
        \* msi_opt.m:605
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "WritePull", msg.src, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
        \* msi_opt.m:608
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step2, "Type/range error at msi_opt.m:608")
        \* msi_opt.m:609
        step4 == IF step3.error # "" THEN step3
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step3, "Type/range error at msi_opt.m:609")
        \* msi_opt.m:610
        step5 == IF step4.error # "" THEN step4
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(step4, "Type/range error at msi_opt.m:610")
    IN step5

Home_H_I_22(r, msg, h) ==
    LET
        \* msi_opt.m:613
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_H_I_4(r, msg, h) ==
    LET
        \* msi_opt.m:461
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "RdCurr") -> Home_H_I_RdCurr_5(r, msg, h)
                 [] (msg.mtype = "RdOwn") -> Home_H_I_RdOwn_6(r, msg, h)
                 [] (msg.mtype = "DirtyEvict") -> Home_H_I_DirtyEvict_7(r, msg, h)
                 [] (msg.mtype = "CleanEvict") -> Home_H_I_CleanEvict_8(r, msg, h)
                 [] (msg.mtype = "CleanEvictNoData") -> Home_H_I_CleanEvictNoData_9(r, msg, h)
                 [] (msg.mtype = "CLFlush") -> Home_H_I_CLFlush_10(r, msg, h)
                 [] (msg.mtype = "ItoMWr") -> Home_H_I_ItoMWr_11(r, msg, h)
                 [] (msg.mtype = "RdShared") -> Home_H_I_RdShared_12(r, msg, h)
                 [] (msg.mtype = "RdAny") -> Home_H_I_RdAny_15(r, msg, h)
                 [] (msg.mtype = "RdOwnNoData") -> Home_H_I_RdOwnNoData_18(r, msg, h)
                 [] (msg.mtype = "WrCur") -> Home_H_I_WrCur_19(r, msg, h)
                 [] (msg.mtype = "CacheFlushed") -> Home_H_I_CacheFlushed_20(r, msg, h)
                 [] (msg.mtype = "WrInv") -> Home_H_I_WrInv_21(r, msg, h)
                 [] OTHER -> Home_H_I_22(r, msg, h)
    IN step1

Home_HT_II_AD_RspIHitI_25(r, msg, h) ==
    LET
        \* msi_opt.m:621
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_II_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_II_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:621")
        \* msi_opt.m:622
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].owner = msg.src]
                ELSE Fail(step1, "Type/range error at msi_opt.m:622")
        \* msi_opt.m:623
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO_WritePull", step2.HomeNodes[h].owner, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step3

Home_HT_II_AD_RspIHitI_26(r, msg, h) ==
    LET
        \* msi_opt.m:627
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_II_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_II_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:627")
        \* msi_opt.m:628
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO_WritePull", step1.HomeNodes[h].owner, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step2

Home_HT_II_AD_RspIHitI_27(r, msg, h) ==
    LET
        \* msi_opt.m:632
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_II_AD_RspIHitI_24(r, msg, h) ==
    LET
        \* msi_opt.m:619
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "ItoMWr") -> Home_HT_II_AD_RspIHitI_25(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "WrInv") -> Home_HT_II_AD_RspIHitI_26(r, msg, h)
                 [] OTHER -> Home_HT_II_AD_RspIHitI_27(r, msg, h)
    IN step1

Home_HT_II_AD_RspIFwdM_28(r, msg, h) ==
    LET
        \* msi_opt.m:636
        step1 == IF r.error # "" THEN r
                 ELSE IF FALSE \in (BOOLEAN) \cup {Undefined} THEN
                    [r EXCEPT !.msg_processed = FALSE]
                ELSE Fail(r, "Type/range error at msi_opt.m:636")
    IN step1

Home_HT_II_AD_29(r, msg, h) ==
    LET
        \* msi_opt.m:675
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_II_AD_23(r, msg, h) ==
    LET
        \* msi_opt.m:617
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "RspIHitI") -> Home_HT_II_AD_RspIHitI_24(r, msg, h)
                 [] (msg.mtype = "RspIFwdM" \/ msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed" \/ msg.mtype = "RspVHitV" \/ msg.mtype = "RspIHitSE" \/ msg.mtype = "RspSHitSE" \/ msg.mtype = "RspSFwdM" \/ msg.mtype = "RspVFwdV") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_II_AD_29(r, msg, h)
    IN step1

Home_HT_IS_D_Data_31(r, msg, h) ==
    LET
        \* msi_opt.m:681
        step1 == IF r.error # "" THEN r
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(r, "Type/range error at msi_opt.m:681")
        \* msi_opt.m:682
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO", step1.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "S", 1)
        \* msi_opt.m:685
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "Data", step2.HomeNodes[h].requester, h, H2D_DATA, step2.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
    IN step3

Home_HT_IS_D_32(r, msg, h) ==
    LET
        \* msi_opt.m:729
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_IS_D_30(r, msg, h) ==
    LET
        \* msi_opt.m:679
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "Data") -> Home_HT_IS_D_Data_31(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed" \/ msg.mtype = "RspIHitI" \/ msg.mtype = "RspVHitV" \/ msg.mtype = "RspIHitSE" \/ msg.mtype = "RspSHitSE" \/ msg.mtype = "RspSFwdM" \/ msg.mtype = "RspIFwdM" \/ msg.mtype = "RspVFwdV") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_IS_D_32(r, msg, h)
    IN step1

Home_HT_IE_AD_RspIHitSE_34(r, msg, h) ==
    LET
        \* msi_opt.m:735
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_IE_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_IE_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:735")
    IN step1

Home_HT_IE_AD_Data_35(r, msg, h) ==
    LET
        \* msi_opt.m:744
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_IE_A" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_IE_A"]
                ELSE Fail(r, "Type/range error at msi_opt.m:744")
        \* msi_opt.m:745
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:745")
    IN step2

Home_HT_IE_AD_36(r, msg, h) ==
    LET
        \* msi_opt.m:786
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_IE_AD_33(r, msg, h) ==
    LET
        \* msi_opt.m:733
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "RspIHitSE") -> Home_HT_IE_AD_RspIHitSE_34(r, msg, h)
                 [] (msg.mtype = "Data") -> Home_HT_IE_AD_Data_35(r, msg, h)
                 [] (msg.mtype = "RspIFwdM" \/ msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed" \/ msg.mtype = "RspIHitI" \/ msg.mtype = "RspVHitV" \/ msg.mtype = "RspSHitSE" \/ msg.mtype = "RspSFwdM" \/ msg.mtype = "RspVFwdV") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_IE_AD_36(r, msg, h)
    IN step1

Home_HT_IE_D_Data_39(r, msg, h) ==
    LET
        \* msi_opt.m:796
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_I" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:796")
        \* msi_opt.m:797
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:797")
        \* msi_opt.m:799
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "Data", step2.HomeNodes[h].requester, h, H2D_DATA, step2.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:802
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:802")
        \* msi_opt.m:803
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:803")
        \* msi_opt.m:804
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:804")
    IN step6

Home_HT_IE_D_Data_40(r, msg, h) ==
    LET
        \* msi_opt.m:806
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_E" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_E"]
                ELSE Fail(r, "Type/range error at msi_opt.m:806")
        \* msi_opt.m:807
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:807")
        \* msi_opt.m:810
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO", step2.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "E", 1)
        \* msi_opt.m:813
        step4 == IF step3.error # "" THEN step3
                 ELSE Send(step3, "Data", step3.HomeNodes[h].requester, h, H2D_DATA, step3.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:817
        step5 == IF step4.error # "" THEN step4
                 ELSE IF step4.HomeNodes[h].requester \in (Node) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].owner = step4.HomeNodes[h].requester]
                ELSE Fail(step4, "Type/range error at msi_opt.m:817")
        \* msi_opt.m:818
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:818")
        \* msi_opt.m:819
        step7 == IF step6.error # "" THEN step6
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step6 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step6, "Type/range error at msi_opt.m:819")
        \* msi_opt.m:820
        step8 == IF step7.error # "" THEN step7
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step7 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step7, "Type/range error at msi_opt.m:820")
    IN step8

Home_HT_IE_D_Data_41(r, msg, h) ==
    LET
        \* msi_opt.m:822
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:822")
        \* msi_opt.m:823
        step2 == IF step1.error # "" THEN step1
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(step1, "Type/range error at msi_opt.m:823")
        \* msi_opt.m:824
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step2, "Type/range error at msi_opt.m:824")
        \* msi_opt.m:826
        step4 == IF step3.error # "" THEN step3
                 ELSE Send(step3, "GO_WritePull", step3.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step4

Home_HT_IE_D_Data_42(r, msg, h) ==
    LET
        \* msi_opt.m:848
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:848")
        \* msi_opt.m:849
        step2 == IF step1.error # "" THEN step1
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(step1, "Type/range error at msi_opt.m:849")
        \* msi_opt.m:850
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step2, "Type/range error at msi_opt.m:850")
        \* msi_opt.m:852
        step4 == IF step3.error # "" THEN step3
                 ELSE Send(step3, "GO_WritePull", step3.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step4

Home_HT_IE_D_Data_43(r, msg, h) ==
    LET
        \* msi_opt.m:857
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_IE_D_Data_38(r, msg, h) ==
    LET
        \* msi_opt.m:792
        step1 == IF r.error # "" THEN r
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(r, "Type/range error at msi_opt.m:792")
        \* msi_opt.m:793
        step2 == IF step1.error # "" THEN step1
                 ELSE CASE (step1.HomeNodes[h].request_type = "RdCurr") -> Home_HT_IE_D_Data_39(step1, msg, h)
                 [] (step1.HomeNodes[h].request_type = "RdOwn") -> Home_HT_IE_D_Data_40(step1, msg, h)
                 [] (step1.HomeNodes[h].request_type = "ItoMWr") -> Home_HT_IE_D_Data_41(step1, msg, h)
                 [] (step1.HomeNodes[h].request_type = "WrCur") -> Home_HT_IE_D_Data_42(step1, msg, h)
                 [] OTHER -> Home_HT_IE_D_Data_43(step1, msg, h)
    IN step2

Home_HT_IE_D_44(r, msg, h) ==
    LET
        \* msi_opt.m:902
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_IE_D_37(r, msg, h) ==
    LET
        \* msi_opt.m:790
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "Data") -> Home_HT_IE_D_Data_38(r, msg, h)
                 [] (msg.mtype = "RspIHitSE" \/ msg.mtype = "RspIFwdM" \/ msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed" \/ msg.mtype = "RspIHitI" \/ msg.mtype = "RspVHitV" \/ msg.mtype = "RspSHitSE" \/ msg.mtype = "RspSFwdM" \/ msg.mtype = "RspVFwdV") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_IE_D_44(r, msg, h)
    IN step1

Home_HT_IE_A_RspIHitSE_47(r, msg, h) ==
    LET
        \* msi_opt.m:910
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_I" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:910")
        \* msi_opt.m:912
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "Data", step1.HomeNodes[h].requester, h, H2D_DATA, step1.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:915
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:915")
        \* msi_opt.m:916
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:916")
        \* msi_opt.m:917
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:917")
    IN step5

Home_HT_IE_A_RspIHitSE_48(r, msg, h) ==
    LET
        \* msi_opt.m:919
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_E" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_E"]
                ELSE Fail(r, "Type/range error at msi_opt.m:919")
        \* msi_opt.m:921
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO", step1.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "E", 1)
        \* msi_opt.m:924
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "Data", step2.HomeNodes[h].requester, h, H2D_DATA, step2.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:928
        step4 == IF step3.error # "" THEN step3
                 ELSE IF step3.HomeNodes[h].requester \in (Node) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].owner = step3.HomeNodes[h].requester]
                ELSE Fail(step3, "Type/range error at msi_opt.m:928")
        \* msi_opt.m:929
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:929")
        \* msi_opt.m:930
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:930")
        \* msi_opt.m:931
        step7 == IF step6.error # "" THEN step6
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step6 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step6, "Type/range error at msi_opt.m:931")
    IN step7

Home_HT_IE_A_RspIHitSE_49(r, msg, h) ==
    LET
        \* msi_opt.m:933
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:933")
        \* msi_opt.m:934
        step2 == IF step1.error # "" THEN step1
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(step1, "Type/range error at msi_opt.m:934")
        \* msi_opt.m:935
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step2, "Type/range error at msi_opt.m:935")
        \* msi_opt.m:937
        step4 == IF step3.error # "" THEN step3
                 ELSE Send(step3, "GO_WritePull", step3.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step4

Home_HT_IE_A_RspIHitSE_50(r, msg, h) ==
    LET
        \* msi_opt.m:941
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:941")
        \* msi_opt.m:942
        step2 == IF step1.error # "" THEN step1
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(step1, "Type/range error at msi_opt.m:942")
        \* msi_opt.m:943
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO_WritePull", step2.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step3

Home_HT_IE_A_RspIHitSE_51(r, msg, h) ==
    LET
        \* msi_opt.m:948
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_IE_A_RspIHitSE_46(r, msg, h) ==
    LET
        \* msi_opt.m:908
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "RdCurr") -> Home_HT_IE_A_RspIHitSE_47(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "RdOwn") -> Home_HT_IE_A_RspIHitSE_48(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "ItoMWr") -> Home_HT_IE_A_RspIHitSE_49(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "WrCur") -> Home_HT_IE_A_RspIHitSE_50(r, msg, h)
                 [] OTHER -> Home_HT_IE_A_RspIHitSE_51(r, msg, h)
    IN step1

Home_HT_IE_A_52(r, msg, h) ==
    LET
        \* msi_opt.m:993
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_IE_A_45(r, msg, h) ==
    LET
        \* msi_opt.m:906
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "RspIHitSE") -> Home_HT_IE_A_RspIHitSE_46(r, msg, h)
                 [] (msg.mtype = "RspIFwdM" \/ msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed" \/ msg.mtype = "RspIHitI" \/ msg.mtype = "RspVHitV" \/ msg.mtype = "RspSHitSE" \/ msg.mtype = "RspSFwdM" \/ msg.mtype = "RspVFwdV" \/ msg.mtype = "Data") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_IE_A_52(r, msg, h)
    IN step1

Home_HT_II_D_Data_55(r, msg, h) ==
    LET
        \* msi_opt.m:1005
        step1 == IF r.error # "" THEN r
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(r, "Type/range error at msi_opt.m:1005")
        \* msi_opt.m:1006
        step2 == IF step1.error # "" THEN step1
                 ELSE Check(step1, ((step1.HomeNodes[h].request_pre = 0)), "HT_II_D Data received, request_pre should be 0", 1006)
        \* msi_opt.m:1007
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1007")
        \* msi_opt.m:1008
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1008")
        \* msi_opt.m:1009
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:1009")
    IN step5

Home_HT_II_D_Data_56(r, msg, h) ==
    LET
        \* msi_opt.m:1011
        step1 == IF r.error # "" THEN r
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(r, "Type/range error at msi_opt.m:1011")
        \* msi_opt.m:1012
        step2 == IF step1.error # "" THEN step1
                 ELSE Check(step1, ((step1.HomeNodes[h].request_pre = 0)), "HT_II_D Data received, request_pre should be 0", 1012)
        \* msi_opt.m:1013
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1013")
        \* msi_opt.m:1014
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1014")
        \* msi_opt.m:1015
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:1015")
    IN step5

Home_HT_II_D_Data_57(r, msg, h) ==
    LET
        \* msi_opt.m:1017
        step1 == IF r.error # "" THEN r
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(r, "Type/range error at msi_opt.m:1017")
        \* msi_opt.m:1018
        step2 == IF step1.error # "" THEN step1
                 ELSE Check(step1, ((step1.HomeNodes[h].request_pre = 0)), "HT_II_D Data received, request_pre should be 0", 1018)
        \* msi_opt.m:1019
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO", step2.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "I", 1)
        \* msi_opt.m:1022
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1022")
        \* msi_opt.m:1023
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:1023")
        \* msi_opt.m:1024
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:1024")
    IN step6

Home_HT_II_D_Data_58(r, msg, h) ==
    LET
        \* msi_opt.m:1027
        step1 == IF r.error # "" THEN r
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(r, "Type/range error at msi_opt.m:1027")
        \* msi_opt.m:1028
        step2 == IF step1.error # "" THEN step1
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1028")
        \* msi_opt.m:1029
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1029")
    IN step3

Home_HT_II_D_Data_59(r, msg, h) ==
    LET
        \* msi_opt.m:1032
        step1 == IF r.error # "" THEN r
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(r, "Type/range error at msi_opt.m:1032")
        \* msi_opt.m:1033
        step2 == IF step1.error # "" THEN step1
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1033")
        \* msi_opt.m:1034
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1034")
    IN step3

Home_HT_II_D_Data_60(r, msg, h) ==
    LET
        \* msi_opt.m:1036
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_II_D_Data_54(r, msg, h) ==
    LET
        \* msi_opt.m:1001
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_I" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1001")
        \* msi_opt.m:1002
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1002")
        \* msi_opt.m:1003
        step3 == IF step2.error # "" THEN step2
                 ELSE CASE (step2.HomeNodes[h].request_type = "ItoMWr") -> Home_HT_II_D_Data_55(step2, msg, h)
                 [] (step2.HomeNodes[h].request_type = "WrCur") -> Home_HT_II_D_Data_56(step2, msg, h)
                 [] (step2.HomeNodes[h].request_type = "WrInv") -> Home_HT_II_D_Data_57(step2, msg, h)
                 [] (step2.HomeNodes[h].request_type = "CleanEvict") -> Home_HT_II_D_Data_58(step2, msg, h)
                 [] (step2.HomeNodes[h].request_type = "DirtyEvict") -> Home_HT_II_D_Data_59(step2, msg, h)
                 [] OTHER -> Home_HT_II_D_Data_60(step2, msg, h)
    IN step3

Home_HT_II_D_61(r, msg, h) ==
    LET
        \* msi_opt.m:1086
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_II_D_53(r, msg, h) ==
    LET
        \* msi_opt.m:998
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "Data") -> Home_HT_II_D_Data_54(r, msg, h)
                 [] (msg.mtype = "RspIFwdM" \/ msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed" \/ msg.mtype = "RspIHitI" \/ msg.mtype = "RspVHitV" \/ msg.mtype = "RspIHitSE" \/ msg.mtype = "RspSHitSE" \/ msg.mtype = "RspSFwdM" \/ msg.mtype = "RspVFwdV") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_II_D_61(r, msg, h)
    IN step1

Home_H_E_RdCurr_63(r, msg, h) ==
    LET
        \* msi_opt.m:1118
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EE_AD" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EE_AD"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1118")
        \* msi_opt.m:1119
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1119")
        \* msi_opt.m:1120
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1120")
        \* msi_opt.m:1121
        step4 == IF step3.error # "" THEN step3
                 ELSE IF 1 \in (0..1) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_pre = 1]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1121")
        \* msi_opt.m:1123
        step5 == IF step4.error # "" THEN step4
                 ELSE Send(step4, "SnpCur", step4.HomeNodes[h].owner, h, H2D_REQ, Undefined, msg.addr, Undefined, msg.cqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
        \* msi_opt.m:1127
        step6 == IF step5.error # "" THEN step5
                 ELSE IF 1 \in (0..1) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].snp_cur_sent = 1]
                ELSE Fail(step5, "Type/range error at msi_opt.m:1127")
    IN step6

Home_H_E_RdOwn_64(r, msg, h) ==
    LET
        \* msi_opt.m:1130
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EE_AD" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EE_AD"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1130")
        \* msi_opt.m:1131
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1131")
        \* msi_opt.m:1132
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1132")
        \* msi_opt.m:1133
        step4 == IF step3.error # "" THEN step3
                 ELSE IF 1 \in (0..1) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_pre = 1]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1133")
        \* msi_opt.m:1135
        step5 == IF step4.error # "" THEN step4
                 ELSE Send(step4, "SnpInv", step4.HomeNodes[h].owner, h, H2D_REQ, Undefined, msg.addr, Undefined, msg.cqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
        \* msi_opt.m:1138
        step6 == IF step5.error # "" THEN step5
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].owner = msg.src]
                ELSE Fail(step5, "Type/range error at msi_opt.m:1138")
    IN step6

Home_H_E_RdShared_65(r, msg, h) ==
    LET
        \* msi_opt.m:1142
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_ES_AD" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_ES_AD"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1142")
        \* msi_opt.m:1143
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1143")
        \* msi_opt.m:1144
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1144")
        \* msi_opt.m:1145
        step4 == IF step3.error # "" THEN step3
                 ELSE IF 1 \in (0..1) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_pre = 1]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1145")
        \* msi_opt.m:1147
        step5 == IF step4.error # "" THEN step4
                 ELSE IF 1 \in (0..1) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].snp_data_sent = 1]
                ELSE Fail(step4, "Type/range error at msi_opt.m:1147")
        \* msi_opt.m:1149
        step6 == IF step5.error # "" THEN step5
                 ELSE AddToSharersList(step5, msg.src, h)
        \* msi_opt.m:1150
        step7 == IF step6.error # "" THEN step6
                 ELSE AddToSharersList(step6, step6.HomeNodes[h].owner, h)
        \* msi_opt.m:1151
        step8 == IF step7.error # "" THEN step7
                 ELSE Send(step7, "SnpData", step7.HomeNodes[h].owner, h, H2D_REQ, Undefined, msg.addr, Undefined, msg.cqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
        \* msi_opt.m:1154
        step9 == IF step8.error # "" THEN step8
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step8 EXCEPT !.HomeNodes[h].owner = Undefined]
                ELSE Fail(step8, "Type/range error at msi_opt.m:1154")
    IN step9

Home_H_E_RdAny_66(r, msg, h) ==
    LET
        \* msi_opt.m:1158
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_ES_AD" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_ES_AD"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1158")
        \* msi_opt.m:1159
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1159")
        \* msi_opt.m:1160
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1160")
        \* msi_opt.m:1161
        step4 == IF step3.error # "" THEN step3
                 ELSE IF 1 \in (0..1) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_pre = 1]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1161")
        \* msi_opt.m:1163
        step5 == IF step4.error # "" THEN step4
                 ELSE IF 1 \in (0..1) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].snp_data_sent = 1]
                ELSE Fail(step4, "Type/range error at msi_opt.m:1163")
        \* msi_opt.m:1165
        step6 == IF step5.error # "" THEN step5
                 ELSE AddToSharersList(step5, msg.src, h)
        \* msi_opt.m:1166
        step7 == IF step6.error # "" THEN step6
                 ELSE AddToSharersList(step6, step6.HomeNodes[h].owner, h)
        \* msi_opt.m:1167
        step8 == IF step7.error # "" THEN step7
                 ELSE Send(step7, "SnpData", step7.HomeNodes[h].owner, h, H2D_REQ, Undefined, msg.addr, Undefined, msg.cqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
        \* msi_opt.m:1170
        step9 == IF step8.error # "" THEN step8
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step8 EXCEPT !.HomeNodes[h].owner = Undefined]
                ELSE Fail(step8, "Type/range error at msi_opt.m:1170")
    IN step9

Home_H_E_RdOwnNoData_67(r, msg, h) ==
    LET
        \* msi_opt.m:1175
        step1 == IF r.error # "" THEN r
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(r, "Type/range error at msi_opt.m:1175")
        \* msi_opt.m:1176
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1176")
        \* msi_opt.m:1177
        step3 == IF step2.error # "" THEN step2
                 ELSE IF 1 \in (0..1) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_pre = 1]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1177")
        \* msi_opt.m:1178
        step4 == IF step3.error # "" THEN step3
                 ELSE IF 1 \in (0..1) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].snp_data_sent = 1]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1178")
        \* msi_opt.m:1179
        step5 == IF step4.error # "" THEN step4
                 ELSE Check(step4, ((step4.HomeNodes[h].requester # step4.HomeNodes[h].owner)), "H_E should not receive RdOwnNoData from its owner", 1179)
        \* msi_opt.m:1180
        step6 == IF step5.error # "" THEN step5
                 ELSE IF "HT_EE_AD" \in (HomeStates) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].state = "HT_EE_AD"]
                ELSE Fail(step5, "Type/range error at msi_opt.m:1180")
        \* msi_opt.m:1181
        step7 == IF step6.error # "" THEN step6
                 ELSE Send(step6, "SnpData", step6.HomeNodes[h].owner, h, H2D_REQ, Undefined, msg.addr, Undefined, msg.cqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step7

Home_H_E_ItoMWr_68(r, msg, h) ==
    LET
        \* msi_opt.m:1186
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EE_AD" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EE_AD"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1186")
        \* msi_opt.m:1187
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1187")
        \* msi_opt.m:1188
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1188")
        \* msi_opt.m:1189
        step4 == IF step3.error # "" THEN step3
                 ELSE IF 1 \in (0..1) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_pre = 1]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1189")
        \* msi_opt.m:1192
        step5 == IF step4.error # "" THEN step4
                 ELSE Send(step4, "SnpInv", step4.HomeNodes[h].owner, h, H2D_REQ, Undefined, msg.addr, Undefined, msg.cqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
        \* msi_opt.m:1196
        step6 == IF step5.error # "" THEN step5
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].owner = msg.src]
                ELSE Fail(step5, "Type/range error at msi_opt.m:1196")
    IN step6

Home_H_E_WrCur_69(r, msg, h) ==
    LET
        \* msi_opt.m:1198
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EE_AD" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EE_AD"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1198")
        \* msi_opt.m:1199
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1199")
        \* msi_opt.m:1200
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1200")
        \* msi_opt.m:1201
        step4 == IF step3.error # "" THEN step3
                 ELSE IF 1 \in (0..1) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_pre = 1]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1201")
        \* msi_opt.m:1204
        step5 == IF step4.error # "" THEN step4
                 ELSE Send(step4, "SnpInv", step4.HomeNodes[h].owner, h, H2D_REQ, Undefined, msg.addr, Undefined, msg.cqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
        \* msi_opt.m:1208
        step6 == IF step5.error # "" THEN step5
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].owner = msg.src]
                ELSE Fail(step5, "Type/range error at msi_opt.m:1208")
    IN step6

Home_H_E_CLFlush_70(r, msg, h) ==
    LET
        \* msi_opt.m:1210
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_AD" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_AD"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1210")
        \* msi_opt.m:1211
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1211")
        \* msi_opt.m:1212
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1212")
        \* msi_opt.m:1213
        step4 == IF step3.error # "" THEN step3
                 ELSE IF 1 \in (0..1) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_pre = 1]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1213")
        \* msi_opt.m:1215
        step5 == IF step4.error # "" THEN step4
                 ELSE Send(step4, "SnpInv", step4.HomeNodes[h].owner, h, H2D_REQ, Undefined, msg.addr, Undefined, msg.cqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
        \* msi_opt.m:1218
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].owner = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:1218")
    IN step6

Home_H_E_CleanEvict_71(r, msg, h) ==
    LET
        \* msi_opt.m:1220
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1220")
        \* msi_opt.m:1221
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1221")
        \* msi_opt.m:1222
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1222")
        \* msi_opt.m:1223
        step4 == IF step3.error # "" THEN step3
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1223")
        \* msi_opt.m:1225
        step5 == IF step4.error # "" THEN step4
                 ELSE Send(step4, "GO_WritePull", step4.HomeNodes[h].owner, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step5

Home_H_E_DirtyEvict_72(r, msg, h) ==
    LET
        \* msi_opt.m:1230
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1230")
        \* msi_opt.m:1231
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1231")
        \* msi_opt.m:1232
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1232")
        \* msi_opt.m:1233
        step4 == IF step3.error # "" THEN step3
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1233")
        \* msi_opt.m:1235
        step5 == IF step4.error # "" THEN step4
                 ELSE Send(step4, "GO_WritePull", step4.HomeNodes[h].owner, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step5

Home_H_E_CleanEvictNoData_73(r, msg, h) ==
    LET
        \* msi_opt.m:1239
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_I" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1239")
        \* msi_opt.m:1242
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO", step1.HomeNodes[h].owner, h, H2D_RSP, Undefined, Undefined, msg.cqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "I", 1)
        \* msi_opt.m:1246
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].owner = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1246")
    IN step3

Home_H_E_WrInv_74(r, msg, h) ==
    LET
        \* msi_opt.m:1248
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_AD" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_AD"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1248")
        \* msi_opt.m:1249
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1249")
        \* msi_opt.m:1250
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1250")
        \* msi_opt.m:1251
        step4 == IF step3.error # "" THEN step3
                 ELSE IF 1 \in (0..1) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_pre = 1]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1251")
        \* msi_opt.m:1253
        step5 == IF step4.error # "" THEN step4
                 ELSE Send(step4, "SnpInv", step4.HomeNodes[h].owner, h, H2D_REQ, Undefined, msg.addr, Undefined, msg.cqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
        \* msi_opt.m:1257
        step6 == IF step5.error # "" THEN step5
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].owner = msg.src]
                ELSE Fail(step5, "Type/range error at msi_opt.m:1257")
    IN step6

Home_H_E_CacheFlushed_75(r, msg, h) ==
    LET
        \* msi_opt.m:1264
        step1 == IF r.error # "" THEN r
                 ELSE Check(r, ((msg.src # r.HomeNodes[h].owner)), "CacheFlushed msg from owner", 1264)
        \* msi_opt.m:1265
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "H_E" \in (HomeStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].state = "H_E"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1265")
        \* msi_opt.m:1270
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO", msg.src, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "I", 1)
    IN step3

Home_H_E_76(r, msg, h) ==
    LET
        \* msi_opt.m:1279
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_H_E_62(r, msg, h) ==
    LET
        \* msi_opt.m:1110
        step1 == IF r.error # "" THEN r
                 ELSE Check(r, (~((r.HomeNodes[h].owner = Undefined))), "HomeNodes has no owner, but line is Exclusive", 1110)
        \* msi_opt.m:1112
        step2 == IF step1.error # "" THEN step1
                 ELSE Check(step1, ((step1.cnt = 0)), "HomeNodes has sharer, but line is Exclusive", 1112)
        \* msi_opt.m:1114
        step3 == IF step2.error # "" THEN step2
                 ELSE CASE (msg.mtype = "RdCurr") -> Home_H_E_RdCurr_63(step2, msg, h)
                 [] (msg.mtype = "RdOwn") -> Home_H_E_RdOwn_64(step2, msg, h)
                 [] (msg.mtype = "RdShared") -> Home_H_E_RdShared_65(step2, msg, h)
                 [] (msg.mtype = "RdAny") -> Home_H_E_RdAny_66(step2, msg, h)
                 [] (msg.mtype = "RdOwnNoData") -> Home_H_E_RdOwnNoData_67(step2, msg, h)
                 [] (msg.mtype = "ItoMWr") -> Home_H_E_ItoMWr_68(step2, msg, h)
                 [] (msg.mtype = "WrCur") -> Home_H_E_WrCur_69(step2, msg, h)
                 [] (msg.mtype = "CLFlush") -> Home_H_E_CLFlush_70(step2, msg, h)
                 [] (msg.mtype = "CleanEvict") -> Home_H_E_CleanEvict_71(step2, msg, h)
                 [] (msg.mtype = "DirtyEvict") -> Home_H_E_DirtyEvict_72(step2, msg, h)
                 [] (msg.mtype = "CleanEvictNoData") -> Home_H_E_CleanEvictNoData_73(step2, msg, h)
                 [] (msg.mtype = "WrInv") -> Home_H_E_WrInv_74(step2, msg, h)
                 [] (msg.mtype = "CacheFlushed") -> Home_H_E_CacheFlushed_75(step2, msg, h)
                 [] OTHER -> Home_H_E_76(step2, msg, h)
    IN step3

Home_HT_EI_AD_RspIHitSE_79(r, msg, h) ==
    LET
        \* msi_opt.m:1287
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1287")
    IN step1

Home_HT_EI_AD_RspIHitSE_80(r, msg, h) ==
    LET
        \* msi_opt.m:1294
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1294")
    IN step1

Home_HT_EI_AD_RspIHitSE_81(r, msg, h) ==
    LET
        \* msi_opt.m:1314
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EI_AD_RspIHitSE_78(r, msg, h) ==
    LET
        \* msi_opt.m:1285
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "CLFlush") -> Home_HT_EI_AD_RspIHitSE_79(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "WrInv") -> Home_HT_EI_AD_RspIHitSE_80(r, msg, h)
                 [] OTHER -> Home_HT_EI_AD_RspIHitSE_81(r, msg, h)
    IN step1

Home_HT_EI_AD_RspIFwdM_83(r, msg, h) ==
    LET
        \* msi_opt.m:1320
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1320")
    IN step1

Home_HT_EI_AD_RspIFwdM_84(r, msg, h) ==
    LET
        \* msi_opt.m:1326
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1326")
    IN step1

Home_HT_EI_AD_RspIFwdM_85(r, msg, h) ==
    LET
        \* msi_opt.m:1342
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EI_AD_RspIFwdM_82(r, msg, h) ==
    LET
        \* msi_opt.m:1318
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "CLFlush") -> Home_HT_EI_AD_RspIFwdM_83(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "WrInv") -> Home_HT_EI_AD_RspIFwdM_84(r, msg, h)
                 [] OTHER -> Home_HT_EI_AD_RspIFwdM_85(r, msg, h)
    IN step1

Home_HT_EI_AD_Data_87(r, msg, h) ==
    LET
        \* msi_opt.m:1348
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_A" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_A"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1348")
        \* msi_opt.m:1349
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1349")
    IN step2

Home_HT_EI_AD_Data_88(r, msg, h) ==
    LET
        \* msi_opt.m:1351
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_A" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_A"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1351")
        \* msi_opt.m:1352
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1352")
    IN step2

Home_HT_EI_AD_Data_89(r, msg, h) ==
    LET
        \* msi_opt.m:1357
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EI_AD_Data_86(r, msg, h) ==
    LET
        \* msi_opt.m:1346
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "CLFlush") -> Home_HT_EI_AD_Data_87(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "WrInv") -> Home_HT_EI_AD_Data_88(r, msg, h)
                 [] OTHER -> Home_HT_EI_AD_Data_89(r, msg, h)
    IN step1

Home_HT_EI_AD_CleanEvictNoData_91(r, msg, h) ==
    LET
        \* msi_opt.m:1363
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_I" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1363")
        \* msi_opt.m:1365
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO", step1.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "I", 1)
        \* msi_opt.m:1369
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].owner = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1369")
    IN step3

Home_HT_EI_AD_CleanEvictNoData_92(r, msg, h) ==
    LET
        \* msi_opt.m:1371
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_II_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_II_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1371")
        \* msi_opt.m:1376
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "WritePull", step1.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
        \* msi_opt.m:1380
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].owner = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1380")
    IN step3

Home_HT_EI_AD_CleanEvictNoData_93(r, msg, h) ==
    LET
        \* msi_opt.m:1382
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EI_AD_CleanEvictNoData_90(r, msg, h) ==
    LET
        \* msi_opt.m:1361
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "CLFlush") -> Home_HT_EI_AD_CleanEvictNoData_91(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "WrInv") -> Home_HT_EI_AD_CleanEvictNoData_92(r, msg, h)
                 [] OTHER -> Home_HT_EI_AD_CleanEvictNoData_93(r, msg, h)
    IN step1

Home_HT_EI_AD_CleanEvict_95(r, msg, h) ==
    LET
        \* msi_opt.m:1388
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1388")
    IN step1

Home_HT_EI_AD_CleanEvict_96(r, msg, h) ==
    LET
        \* msi_opt.m:1394
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1394")
    IN step1

Home_HT_EI_AD_CleanEvict_97(r, msg, h) ==
    LET
        \* msi_opt.m:1400
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EI_AD_CleanEvict_94(r, msg, h) ==
    LET
        \* msi_opt.m:1386
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "CLFlush") -> Home_HT_EI_AD_CleanEvict_95(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "WrInv") -> Home_HT_EI_AD_CleanEvict_96(r, msg, h)
                 [] OTHER -> Home_HT_EI_AD_CleanEvict_97(r, msg, h)
    IN step1

Home_HT_EI_AD_DirtyEvict_99(r, msg, h) ==
    LET
        \* msi_opt.m:1405
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1405")
    IN step1

Home_HT_EI_AD_DirtyEvict_100(r, msg, h) ==
    LET
        \* msi_opt.m:1411
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1411")
    IN step1

Home_HT_EI_AD_DirtyEvict_101(r, msg, h) ==
    LET
        \* msi_opt.m:1417
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EI_AD_DirtyEvict_98(r, msg, h) ==
    LET
        \* msi_opt.m:1403
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "CLFlush") -> Home_HT_EI_AD_DirtyEvict_99(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "WrInv") -> Home_HT_EI_AD_DirtyEvict_100(r, msg, h)
                 [] OTHER -> Home_HT_EI_AD_DirtyEvict_101(r, msg, h)
    IN step1

Home_HT_EI_AD_102(r, msg, h) ==
    LET
        \* msi_opt.m:1447
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EI_AD_77(r, msg, h) ==
    LET
        \* msi_opt.m:1283
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "RspIHitSE") -> Home_HT_EI_AD_RspIHitSE_78(r, msg, h)
                 [] (msg.mtype = "RspIFwdM") -> Home_HT_EI_AD_RspIFwdM_82(r, msg, h)
                 [] (msg.mtype = "Data") -> Home_HT_EI_AD_Data_86(r, msg, h)
                 [] (msg.mtype = "CleanEvictNoData") -> Home_HT_EI_AD_CleanEvictNoData_90(r, msg, h)
                 [] (msg.mtype = "CleanEvict") -> Home_HT_EI_AD_CleanEvict_94(r, msg, h)
                 [] (msg.mtype = "DirtyEvict") -> Home_HT_EI_AD_DirtyEvict_98(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_EI_AD_102(r, msg, h)
    IN step1

Home_HT_EI_A_RspIFwdM_105(r, msg, h) ==
    LET
        \* msi_opt.m:1455
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_I" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1455")
        \* msi_opt.m:1456
        step2 == IF step1.error # "" THEN step1
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1456")
        \* msi_opt.m:1457
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1457")
        \* msi_opt.m:1458
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1458")
        \* msi_opt.m:1460
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].owner = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:1460")
    IN step5

Home_HT_EI_A_RspIFwdM_106(r, msg, h) ==
    LET
        \* msi_opt.m:1462
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1462")
        \* msi_opt.m:1463
        step2 == IF step1.error # "" THEN step1
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1463")
        \* msi_opt.m:1465
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "WritePull", step2.HomeNodes[h].owner, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step3

Home_HT_EI_A_RspIFwdM_107(r, msg, h) ==
    LET
        \* msi_opt.m:1478
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EI_A_RspIFwdM_104(r, msg, h) ==
    LET
        \* msi_opt.m:1453
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "CLFlush") -> Home_HT_EI_A_RspIFwdM_105(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "WrInv") -> Home_HT_EI_A_RspIFwdM_106(r, msg, h)
                 [] OTHER -> Home_HT_EI_A_RspIFwdM_107(r, msg, h)
    IN step1

Home_HT_EI_A_RspIHitSE_109(r, msg, h) ==
    LET
        \* msi_opt.m:1483
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_I" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1483")
        \* msi_opt.m:1484
        step2 == IF step1.error # "" THEN step1
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1484")
        \* msi_opt.m:1485
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1485")
        \* msi_opt.m:1486
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1486")
        \* msi_opt.m:1488
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].owner = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:1488")
    IN step5

Home_HT_EI_A_RspIHitSE_110(r, msg, h) ==
    LET
        \* msi_opt.m:1490
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1490")
        \* msi_opt.m:1491
        step2 == IF step1.error # "" THEN step1
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1491")
        \* msi_opt.m:1493
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "WritePull", step2.HomeNodes[h].owner, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step3

Home_HT_EI_A_RspIHitSE_111(r, msg, h) ==
    LET
        \* msi_opt.m:1497
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EI_A_RspIHitSE_108(r, msg, h) ==
    LET
        \* msi_opt.m:1481
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "CLFlush") -> Home_HT_EI_A_RspIHitSE_109(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "WrInv") -> Home_HT_EI_A_RspIHitSE_110(r, msg, h)
                 [] OTHER -> Home_HT_EI_A_RspIHitSE_111(r, msg, h)
    IN step1

Home_HT_EI_A_112(r, msg, h) ==
    LET
        \* msi_opt.m:1526
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EI_A_103(r, msg, h) ==
    LET
        \* msi_opt.m:1451
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "RspIFwdM") -> Home_HT_EI_A_RspIFwdM_104(r, msg, h)
                 [] (msg.mtype = "RspIHitSE") -> Home_HT_EI_A_RspIHitSE_108(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_EI_A_112(r, msg, h)
    IN step1

Home_HT_EI_D_Data_115(r, msg, h) ==
    LET
        \* msi_opt.m:1534
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_I" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1534")
        \* msi_opt.m:1535
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1535")
        \* msi_opt.m:1537
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO", step2.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "I", 1)
        \* msi_opt.m:1540
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1540")
        \* msi_opt.m:1541
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:1541")
        \* msi_opt.m:1542
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:1542")
        \* msi_opt.m:1544
        step7 == IF step6.error # "" THEN step6
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step6 EXCEPT !.HomeNodes[h].owner = Undefined]
                ELSE Fail(step6, "Type/range error at msi_opt.m:1544")
    IN step7

Home_HT_EI_D_Data_117(r, msg, h) ==
    LET
        \* msi_opt.m:1554
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_I" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1554")
        \* msi_opt.m:1555
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1555")
        \* msi_opt.m:1556
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO", step2.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "I", 1)
        \* msi_opt.m:1559
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1559")
        \* msi_opt.m:1560
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:1560")
        \* msi_opt.m:1561
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:1561")
        \* msi_opt.m:1563
        step7 == IF step6.error # "" THEN step6
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step6 EXCEPT !.HomeNodes[h].owner = Undefined]
                ELSE Fail(step6, "Type/range error at msi_opt.m:1563")
    IN step7

Home_HT_EI_D_Data_118(r, msg, h) ==
    LET
        \* msi_opt.m:1547
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1547")
        \* msi_opt.m:1548
        step2 == IF step1.error # "" THEN step1
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1548")
        \* msi_opt.m:1550
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "WritePull", step2.HomeNodes[h].owner, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step3

Home_HT_EI_D_Data_116(r, msg, h) ==
    LET
        \* msi_opt.m:1546
        step1 == IF r.error # "" THEN r
                 ELSE IF ((r.HomeNodes[h].request_pre = 1)) THEN Home_HT_EI_D_Data_118(r, msg, h)
                ELSE Home_HT_EI_D_Data_117(r, msg, h)
    IN step1

Home_HT_EI_D_Data_119(r, msg, h) ==
    LET
        \* msi_opt.m:1576
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_I" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1576")
        \* msi_opt.m:1577
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1577")
        \* msi_opt.m:1579
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1579")
        \* msi_opt.m:1580
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1580")
        \* msi_opt.m:1581
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:1581")
        \* msi_opt.m:1583
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].owner = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:1583")
    IN step6

Home_HT_EI_D_Data_120(r, msg, h) ==
    LET
        \* msi_opt.m:1585
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_I" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1585")
        \* msi_opt.m:1586
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1586")
        \* msi_opt.m:1588
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1588")
        \* msi_opt.m:1589
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1589")
        \* msi_opt.m:1590
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:1590")
        \* msi_opt.m:1592
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].owner = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:1592")
    IN step6

Home_HT_EI_D_Data_121(r, msg, h) ==
    LET
        \* msi_opt.m:1595
        step1 == IF r.error # "" THEN r
                 ELSE Check(r, ((r.HomeNodes[h].request_pre = 0)), "HT_EI_D CleanEvict type, Data received, reqeust_pre should be 0", 1595)
        \* msi_opt.m:1596
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "H_I" \in (HomeStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].state = "H_I"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1596")
        \* msi_opt.m:1597
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1597")
        \* msi_opt.m:1598
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1598")
        \* msi_opt.m:1599
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:1599")
        \* msi_opt.m:1600
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:1600")
        \* msi_opt.m:1602
        step7 == IF step6.error # "" THEN step6
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step6 EXCEPT !.HomeNodes[h].owner = Undefined]
                ELSE Fail(step6, "Type/range error at msi_opt.m:1602")
    IN step7

Home_HT_EI_D_Data_122(r, msg, h) ==
    LET
        \* msi_opt.m:1604
        step1 == IF r.error # "" THEN r
                 ELSE Check(r, ((r.HomeNodes[h].request_pre = 0)), "HT_EI_D DirtyEvict type, Data received, reqeust_pre should be 0", 1604)
        \* msi_opt.m:1605
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "H_I" \in (HomeStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].state = "H_I"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1605")
        \* msi_opt.m:1606
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1606")
        \* msi_opt.m:1607
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1607")
        \* msi_opt.m:1608
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:1608")
        \* msi_opt.m:1609
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:1609")
        \* msi_opt.m:1611
        step7 == IF step6.error # "" THEN step6
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step6 EXCEPT !.HomeNodes[h].owner = Undefined]
                ELSE Fail(step6, "Type/range error at msi_opt.m:1611")
    IN step7

Home_HT_EI_D_Data_123(r, msg, h) ==
    LET
        \* msi_opt.m:1614
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EI_D_Data_114(r, msg, h) ==
    LET
        \* msi_opt.m:1532
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "CLFlush") -> Home_HT_EI_D_Data_115(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "WrInv") -> Home_HT_EI_D_Data_116(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "ItoMWr") -> Home_HT_EI_D_Data_119(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "WrCur") -> Home_HT_EI_D_Data_120(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "CleanEvict") -> Home_HT_EI_D_Data_121(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "DirtyEvict") -> Home_HT_EI_D_Data_122(r, msg, h)
                 [] OTHER -> Home_HT_EI_D_Data_123(r, msg, h)
    IN step1

Home_HT_EI_D_124(r, msg, h) ==
    LET
        \* msi_opt.m:1643
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EI_D_113(r, msg, h) ==
    LET
        \* msi_opt.m:1530
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "Data") -> Home_HT_EI_D_Data_114(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_EI_D_124(r, msg, h)
    IN step1

Home_HT_EE_AD_RspIHitSE_127(r, msg, h) ==
    LET
        \* msi_opt.m:1671
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EE_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EE_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1671")
    IN step1

Home_HT_EE_AD_RspIHitSE_128(r, msg, h) ==
    LET
        \* msi_opt.m:1699
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EE_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EE_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1699")
    IN step1

Home_HT_EE_AD_RspIHitSE_129(r, msg, h) ==
    LET
        \* msi_opt.m:1708
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EE_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EE_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1708")
    IN step1

Home_HT_EE_AD_RspIHitSE_130(r, msg, h) ==
    LET
        \* msi_opt.m:1717
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EE_AD_RspIHitSE_126(r, msg, h) ==
    LET
        \* msi_opt.m:1656
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "RdOwn") -> Home_HT_EE_AD_RspIHitSE_127(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "ItoMWr") -> Home_HT_EE_AD_RspIHitSE_128(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "WrCur") -> Home_HT_EE_AD_RspIHitSE_129(r, msg, h)
                 [] OTHER -> Home_HT_EE_AD_RspIHitSE_130(r, msg, h)
    IN step1

Home_HT_EE_AD_RspIFwdM_132(r, msg, h) ==
    LET
        \* msi_opt.m:1723
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EE_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EE_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1723")
    IN step1

Home_HT_EE_AD_RspIFwdM_133(r, msg, h) ==
    LET
        \* msi_opt.m:1725
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EE_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EE_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1725")
    IN step1

Home_HT_EE_AD_RspIFwdM_134(r, msg, h) ==
    LET
        \* msi_opt.m:1727
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EE_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EE_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1727")
    IN step1

Home_HT_EE_AD_RspIFwdM_135(r, msg, h) ==
    LET
        \* msi_opt.m:1729
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EE_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EE_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1729")
    IN step1

Home_HT_EE_AD_RspIFwdM_136(r, msg, h) ==
    LET
        \* msi_opt.m:1731
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EE_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EE_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1731")
    IN step1

Home_HT_EE_AD_RspIFwdM_137(r, msg, h) ==
    LET
        \* msi_opt.m:1733
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EE_AD_RspIFwdM_131(r, msg, h) ==
    LET
        \* msi_opt.m:1721
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "RdCurr") -> Home_HT_EE_AD_RspIFwdM_132(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "RdOwn") -> Home_HT_EE_AD_RspIFwdM_133(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "RdOwnNoData") -> Home_HT_EE_AD_RspIFwdM_134(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "ItoMWr") -> Home_HT_EE_AD_RspIFwdM_135(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "WrCur") -> Home_HT_EE_AD_RspIFwdM_136(r, msg, h)
                 [] OTHER -> Home_HT_EE_AD_RspIFwdM_137(r, msg, h)
    IN step1

Home_HT_EE_AD_RspVFwdV_139(r, msg, h) ==
    LET
        \* msi_opt.m:1739
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EE_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EE_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1739")
    IN step1

Home_HT_EE_AD_RspVFwdV_140(r, msg, h) ==
    LET
        \* msi_opt.m:1749
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EE_AD_RspVFwdV_138(r, msg, h) ==
    LET
        \* msi_opt.m:1737
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "RdCurr") -> Home_HT_EE_AD_RspVFwdV_139(r, msg, h)
                 [] OTHER -> Home_HT_EE_AD_RspVFwdV_140(r, msg, h)
    IN step1

Home_HT_EE_AD_Data_142(r, msg, h) ==
    LET
        \* msi_opt.m:1755
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EE_A" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EE_A"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1755")
        \* msi_opt.m:1756
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1756")
    IN step2

Home_HT_EE_AD_Data_143(r, msg, h) ==
    LET
        \* msi_opt.m:1758
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EE_A" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EE_A"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1758")
        \* msi_opt.m:1759
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1759")
    IN step2

Home_HT_EE_AD_Data_144(r, msg, h) ==
    LET
        \* msi_opt.m:1761
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EE_A" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EE_A"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1761")
        \* msi_opt.m:1762
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1762")
    IN step2

Home_HT_EE_AD_Data_145(r, msg, h) ==
    LET
        \* msi_opt.m:1764
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EE_A" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EE_A"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1764")
        \* msi_opt.m:1765
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1765")
    IN step2

Home_HT_EE_AD_Data_146(r, msg, h) ==
    LET
        \* msi_opt.m:1767
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EE_A" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EE_A"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1767")
        \* msi_opt.m:1768
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1768")
    IN step2

Home_HT_EE_AD_Data_147(r, msg, h) ==
    LET
        \* msi_opt.m:1770
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EE_AD_Data_141(r, msg, h) ==
    LET
        \* msi_opt.m:1753
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "RdCurr") -> Home_HT_EE_AD_Data_142(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "RdOwn") -> Home_HT_EE_AD_Data_143(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "RdOwnNoData") -> Home_HT_EE_AD_Data_144(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "ItoMWr") -> Home_HT_EE_AD_Data_145(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "WrCur") -> Home_HT_EE_AD_Data_146(r, msg, h)
                 [] OTHER -> Home_HT_EE_AD_Data_147(r, msg, h)
    IN step1

Home_HT_EE_AD_CleanEvict_149(r, msg, h) ==
    LET
        \* msi_opt.m:1777
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EE_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EE_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1777")
    IN step1

Home_HT_EE_AD_CleanEvict_151(r, msg, h) ==
    r

Home_HT_EE_AD_CleanEvict_150(r, msg, h) ==
    LET
        \* msi_opt.m:1783
        step1 == IF r.error # "" THEN r
                 ELSE IF (r.HomeNodes[h].snp_cur_sent = 1) THEN Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                ELSE Home_HT_EE_AD_CleanEvict_151(r, msg, h)
    IN step1

Home_HT_EE_AD_CleanEvict_152(r, msg, h) ==
    LET
        \* msi_opt.m:1795
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EE_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EE_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1795")
    IN step1

Home_HT_EE_AD_CleanEvict_153(r, msg, h) ==
    LET
        \* msi_opt.m:1802
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EE_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EE_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1802")
    IN step1

Home_HT_EE_AD_CleanEvict_154(r, msg, h) ==
    LET
        \* msi_opt.m:1808
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EE_AD_CleanEvict_148(r, msg, h) ==
    LET
        \* msi_opt.m:1775
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "RdOwn") -> Home_HT_EE_AD_CleanEvict_149(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "RdCurr") -> Home_HT_EE_AD_CleanEvict_150(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "ItoMWr") -> Home_HT_EE_AD_CleanEvict_152(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "WrCur") -> Home_HT_EE_AD_CleanEvict_153(r, msg, h)
                 [] OTHER -> Home_HT_EE_AD_CleanEvict_154(r, msg, h)
    IN step1

Home_HT_EE_AD_CleanEvictNoData_156(r, msg, h) ==
    LET
        \* msi_opt.m:1821
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_E" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_E"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1821")
        \* msi_opt.m:1822
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO", step1.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "E", 1)
        \* msi_opt.m:1825
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "Data", step2.HomeNodes[h].requester, h, H2D_DATA, step2.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:1828
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1828")
        \* msi_opt.m:1829
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:1829")
        \* msi_opt.m:1830
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:1830")
    IN step6

Home_HT_EE_AD_CleanEvictNoData_157(r, msg, h) ==
    LET
        \* msi_opt.m:1833
        step1 == IF r.error # "" THEN r
                 ELSE IF (r.HomeNodes[h].snp_cur_sent = 1) THEN Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                ELSE Home_HT_EE_AD_CleanEvict_151(r, msg, h)
    IN step1

Home_HT_EE_AD_CleanEvictNoData_158(r, msg, h) ==
    LET
        \* msi_opt.m:1847
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1847")
        \* msi_opt.m:1848
        step2 == IF step1.error # "" THEN step1
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1848")
        \* msi_opt.m:1850
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO_WritePull", step2.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step3

Home_HT_EE_AD_CleanEvictNoData_159(r, msg, h) ==
    LET
        \* msi_opt.m:1856
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1856")
        \* msi_opt.m:1857
        step2 == IF step1.error # "" THEN step1
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1857")
        \* msi_opt.m:1859
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO_WritePull", step2.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step3

Home_HT_EE_AD_CleanEvictNoData_160(r, msg, h) ==
    LET
        \* msi_opt.m:1863
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EE_AD_CleanEvictNoData_155(r, msg, h) ==
    LET
        \* msi_opt.m:1812
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "RdOwn") -> Home_HT_EE_AD_CleanEvictNoData_156(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "RdCurr") -> Home_HT_EE_AD_CleanEvictNoData_157(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "ItoMWr") -> Home_HT_EE_AD_CleanEvictNoData_158(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "WrCur") -> Home_HT_EE_AD_CleanEvictNoData_159(r, msg, h)
                 [] OTHER -> Home_HT_EE_AD_CleanEvictNoData_160(r, msg, h)
    IN step1

Home_HT_EE_AD_DirtyEvict_162(r, msg, h) ==
    LET
        \* msi_opt.m:1869
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EE_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EE_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1869")
    IN step1

Home_HT_EE_AD_DirtyEvict_163(r, msg, h) ==
    LET
        \* msi_opt.m:1875
        step1 == IF r.error # "" THEN r
                 ELSE IF (r.HomeNodes[h].snp_cur_sent = 1) THEN Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                ELSE Home_HT_EE_AD_CleanEvict_151(r, msg, h)
    IN step1

Home_HT_EE_AD_DirtyEvict_164(r, msg, h) ==
    LET
        \* msi_opt.m:1886
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EE_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EE_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1886")
    IN step1

Home_HT_EE_AD_DirtyEvict_165(r, msg, h) ==
    LET
        \* msi_opt.m:1893
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EE_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EE_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1893")
    IN step1

Home_HT_EE_AD_DirtyEvict_166(r, msg, h) ==
    LET
        \* msi_opt.m:1899
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EE_AD_DirtyEvict_161(r, msg, h) ==
    LET
        \* msi_opt.m:1867
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "RdOwn") -> Home_HT_EE_AD_DirtyEvict_162(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "RdCurr") -> Home_HT_EE_AD_DirtyEvict_163(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "ItoMWr") -> Home_HT_EE_AD_DirtyEvict_164(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "WrCur") -> Home_HT_EE_AD_DirtyEvict_165(r, msg, h)
                 [] OTHER -> Home_HT_EE_AD_DirtyEvict_166(r, msg, h)
    IN step1

Home_HT_EE_AD_167(r, msg, h) ==
    LET
        \* msi_opt.m:1928
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EE_AD_125(r, msg, h) ==
    LET
        \* msi_opt.m:1647
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "RspIHitSE") -> Home_HT_EE_AD_RspIHitSE_126(r, msg, h)
                 [] (msg.mtype = "RspIFwdM") -> Home_HT_EE_AD_RspIFwdM_131(r, msg, h)
                 [] (msg.mtype = "RspVFwdV") -> Home_HT_EE_AD_RspVFwdV_138(r, msg, h)
                 [] (msg.mtype = "Data") -> Home_HT_EE_AD_Data_141(r, msg, h)
                 [] (msg.mtype = "CleanEvict") -> Home_HT_EE_AD_CleanEvict_148(r, msg, h)
                 [] (msg.mtype = "CleanEvictNoData") -> Home_HT_EE_AD_CleanEvictNoData_155(r, msg, h)
                 [] (msg.mtype = "DirtyEvict") -> Home_HT_EE_AD_DirtyEvict_161(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_EE_AD_167(r, msg, h)
    IN step1

Home_HT_EE_A_RspIHitSE_170(r, msg, h) ==
    LET
        \* msi_opt.m:1944
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_E" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_E"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1944")
        \* msi_opt.m:1945
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO", step1.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "E", 1)
        \* msi_opt.m:1948
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "Data", step2.HomeNodes[h].requester, h, H2D_DATA, step2.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:1951
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1951")
        \* msi_opt.m:1952
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:1952")
        \* msi_opt.m:1953
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:1953")
    IN step6

Home_HT_EE_A_RspIHitSE_171(r, msg, h) ==
    LET
        \* msi_opt.m:1956
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1956")
        \* msi_opt.m:1957
        step2 == IF step1.error # "" THEN step1
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1957")
        \* msi_opt.m:1959
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO_WritePull", step2.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step3

Home_HT_EE_A_RspIHitSE_172(r, msg, h) ==
    LET
        \* msi_opt.m:1963
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1963")
        \* msi_opt.m:1964
        step2 == IF step1.error # "" THEN step1
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(step1, "Type/range error at msi_opt.m:1964")
        \* msi_opt.m:1966
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO_WritePull", step2.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step3

Home_HT_EE_A_RspIHitSE_173(r, msg, h) ==
    LET
        \* msi_opt.m:1970
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EE_A_RspIHitSE_169(r, msg, h) ==
    LET
        \* msi_opt.m:1934
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "RdOwn") -> Home_HT_EE_A_RspIHitSE_170(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "ItoMWr") -> Home_HT_EE_A_RspIHitSE_171(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "WrCur") -> Home_HT_EE_A_RspIHitSE_172(r, msg, h)
                 [] OTHER -> Home_HT_EE_A_RspIHitSE_173(r, msg, h)
    IN step1

Home_HT_EE_A_RspVFwdV_175(r, msg, h) ==
    LET
        \* msi_opt.m:1976
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_E" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_E"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1976")
        \* msi_opt.m:1977
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "Data", step1.HomeNodes[h].requester, h, H2D_DATA, step1.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:1980
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:1980")
        \* msi_opt.m:1981
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:1981")
        \* msi_opt.m:1982
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:1982")
    IN step5

Home_HT_EE_A_RspVFwdV_176(r, msg, h) ==
    LET
        \* msi_opt.m:1984
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EE_A_RspVFwdV_174(r, msg, h) ==
    LET
        \* msi_opt.m:1973
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "RdCurr") -> Home_HT_EE_A_RspVFwdV_175(r, msg, h)
                 [] OTHER -> Home_HT_EE_A_RspVFwdV_176(r, msg, h)
    IN step1

Home_HT_EE_A_RspIFwdM_178(r, msg, h) ==
    LET
        \* msi_opt.m:1997
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_E" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_E"]
                ELSE Fail(r, "Type/range error at msi_opt.m:1997")
        \* msi_opt.m:1998
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO", step1.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "E", 1)
        \* msi_opt.m:2001
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "Data", step2.HomeNodes[h].requester, h, H2D_DATA, step2.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:2004
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:2004")
        \* msi_opt.m:2005
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:2005")
        \* msi_opt.m:2006
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:2006")
    IN step6

Home_HT_EE_A_RspIFwdM_179(r, msg, h) ==
    LET
        \* msi_opt.m:2008
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2008")
        \* msi_opt.m:2009
        step2 == IF step1.error # "" THEN step1
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2009")
        \* msi_opt.m:2011
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO_WritePull", step2.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step3

Home_HT_EE_A_RspIFwdM_180(r, msg, h) ==
    LET
        \* msi_opt.m:2015
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2015")
        \* msi_opt.m:2016
        step2 == IF step1.error # "" THEN step1
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2016")
        \* msi_opt.m:2018
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO_WritePull", step2.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step3

Home_HT_EE_A_RspIFwdM_181(r, msg, h) ==
    LET
        \* msi_opt.m:2022
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EE_A_RspIFwdM_177(r, msg, h) ==
    LET
        \* msi_opt.m:1987
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "RdOwn") -> Home_HT_EE_A_RspIFwdM_178(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "ItoMWr") -> Home_HT_EE_A_RspIFwdM_179(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "WrCur") -> Home_HT_EE_A_RspIFwdM_180(r, msg, h)
                 [] OTHER -> Home_HT_EE_A_RspIFwdM_181(r, msg, h)
    IN step1

Home_HT_EE_A_182(r, msg, h) ==
    LET
        \* msi_opt.m:2052
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EE_A_168(r, msg, h) ==
    LET
        \* msi_opt.m:1932
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "RspIHitSE") -> Home_HT_EE_A_RspIHitSE_169(r, msg, h)
                 [] (msg.mtype = "RspVFwdV") -> Home_HT_EE_A_RspVFwdV_174(r, msg, h)
                 [] (msg.mtype = "RspIFwdM") -> Home_HT_EE_A_RspIFwdM_177(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_EE_A_182(r, msg, h)
    IN step1

Home_HT_EE_D_Data_185(r, msg, h) ==
    LET
        \* msi_opt.m:2060
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_E" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_E"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2060")
        \* msi_opt.m:2061
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2061")
        \* msi_opt.m:2063
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "Data", step2.HomeNodes[h].requester, h, H2D_DATA, step2.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:2066
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:2066")
        \* msi_opt.m:2067
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:2067")
        \* msi_opt.m:2068
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:2068")
    IN step6

Home_HT_EE_D_Data_186(r, msg, h) ==
    LET
        \* msi_opt.m:2070
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_E" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_E"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2070")
        \* msi_opt.m:2071
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2071")
        \* msi_opt.m:2074
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO", step2.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "E", 1)
        \* msi_opt.m:2077
        step4 == IF step3.error # "" THEN step3
                 ELSE Send(step3, "Data", step3.HomeNodes[h].requester, h, H2D_DATA, step3.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:2080
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:2080")
        \* msi_opt.m:2081
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:2081")
        \* msi_opt.m:2082
        step7 == IF step6.error # "" THEN step6
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step6 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step6, "Type/range error at msi_opt.m:2082")
    IN step7

Home_HT_EE_D_Data_187(r, msg, h) ==
    LET
        \* msi_opt.m:2084
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2084")
        \* msi_opt.m:2085
        step2 == IF step1.error # "" THEN step1
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2085")
        \* msi_opt.m:2086
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step2, "Type/range error at msi_opt.m:2086")
        \* msi_opt.m:2088
        step4 == IF step3.error # "" THEN step3
                 ELSE Send(step3, "GO_WritePull", step3.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step4

Home_HT_EE_D_Data_188(r, msg, h) ==
    LET
        \* msi_opt.m:2092
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_E" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_E"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2092")
        \* msi_opt.m:2093
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2093")
        \* msi_opt.m:2094
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO", step2.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "E", 1)
        \* msi_opt.m:2097
        step4 == IF step3.error # "" THEN step3
                 ELSE Send(step3, "Data", step3.HomeNodes[h].requester, h, H2D_DATA, step3.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:2100
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:2100")
        \* msi_opt.m:2101
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:2101")
        \* msi_opt.m:2102
        step7 == IF step6.error # "" THEN step6
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step6 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step6, "Type/range error at msi_opt.m:2102")
        \* msi_opt.m:2103
        step8 == IF step7.error # "" THEN step7
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step7 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step7, "Type/range error at msi_opt.m:2103")
        \* msi_opt.m:2105
        step9 == IF step8.error # "" THEN step8
                 ELSE Send(step8, "GO_WritePull", step8.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step9

Home_HT_EE_D_Data_189(r, msg, h) ==
    LET
        \* msi_opt.m:2110
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_EI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_EI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2110")
        \* msi_opt.m:2111
        step2 == IF step1.error # "" THEN step1
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].request_pre = 0]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2111")
        \* msi_opt.m:2112
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step2, "Type/range error at msi_opt.m:2112")
        \* msi_opt.m:2114
        step4 == IF step3.error # "" THEN step3
                 ELSE Send(step3, "GO_WritePull", step3.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step4

Home_HT_EE_D_Data_190(r, msg, h) ==
    LET
        \* msi_opt.m:2118
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EE_D_Data_184(r, msg, h) ==
    LET
        \* msi_opt.m:2058
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "RdCurr") -> Home_HT_EE_D_Data_185(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "RdOwn") -> Home_HT_EE_D_Data_186(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "ItoMWr") -> Home_HT_EE_D_Data_187(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "RdOwnNoData") -> Home_HT_EE_D_Data_188(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "WrCur") -> Home_HT_EE_D_Data_189(r, msg, h)
                 [] OTHER -> Home_HT_EE_D_Data_190(r, msg, h)
    IN step1

Home_HT_EE_D_191(r, msg, h) ==
    LET
        \* msi_opt.m:2147
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_EE_D_183(r, msg, h) ==
    LET
        \* msi_opt.m:2056
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "Data") -> Home_HT_EE_D_Data_184(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_EE_D_191(r, msg, h)
    IN step1

Home_HT_ES_AD_RspSHitSE_194(r, msg, h) ==
    LET
        \* msi_opt.m:2156
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_ES_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_ES_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2156")
    IN step1

Home_HT_ES_AD_RspSHitSE_195(r, msg, h) ==
    LET
        \* msi_opt.m:2168
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_ES_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_ES_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2168")
    IN step1

Home_HT_ES_AD_RspSHitSE_196(r, msg, h) ==
    LET
        \* msi_opt.m:2198
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_ES_AD_RspSHitSE_193(r, msg, h) ==
    LET
        \* msi_opt.m:2153
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "RdShared") -> Home_HT_ES_AD_RspSHitSE_194(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "RdAny") -> Home_HT_ES_AD_RspSHitSE_195(r, msg, h)
                 [] OTHER -> Home_HT_ES_AD_RspSHitSE_196(r, msg, h)
    IN step1

Home_HT_ES_AD_RspSFwdM_198(r, msg, h) ==
    LET
        \* msi_opt.m:2204
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_ES_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_ES_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2204")
    IN step1

Home_HT_ES_AD_RspSFwdM_199(r, msg, h) ==
    LET
        \* msi_opt.m:2206
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_ES_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_ES_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2206")
    IN step1

Home_HT_ES_AD_RspSFwdM_200(r, msg, h) ==
    LET
        \* msi_opt.m:2208
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_ES_AD_RspSFwdM_197(r, msg, h) ==
    LET
        \* msi_opt.m:2202
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "RdShared") -> Home_HT_ES_AD_RspSFwdM_198(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "RdAny") -> Home_HT_ES_AD_RspSFwdM_199(r, msg, h)
                 [] OTHER -> Home_HT_ES_AD_RspSFwdM_200(r, msg, h)
    IN step1

Home_HT_ES_AD_Data_202(r, msg, h) ==
    LET
        \* msi_opt.m:2214
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_ES_A" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_ES_A"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2214")
        \* msi_opt.m:2215
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2215")
    IN step2

Home_HT_ES_AD_Data_203(r, msg, h) ==
    LET
        \* msi_opt.m:2217
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_ES_A" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_ES_A"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2217")
        \* msi_opt.m:2218
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2218")
    IN step2

Home_HT_ES_AD_Data_204(r, msg, h) ==
    LET
        \* msi_opt.m:2220
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_ES_AD_Data_201(r, msg, h) ==
    LET
        \* msi_opt.m:2212
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "RdShared") -> Home_HT_ES_AD_Data_202(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "RdAny") -> Home_HT_ES_AD_Data_203(r, msg, h)
                 [] OTHER -> Home_HT_ES_AD_Data_204(r, msg, h)
    IN step1

Home_HT_ES_AD_CleanEvictNoData_207(r, msg, h) ==
    LET
        \* msi_opt.m:2235
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_S" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_S"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2235")
        \* msi_opt.m:2236
        step2 == IF step1.error # "" THEN step1
                 ELSE RemoveFromSharersList(step1, msg.src, h)
        \* msi_opt.m:2238
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO", step2.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "S", 1)
        \* msi_opt.m:2241
        step4 == IF step3.error # "" THEN step3
                 ELSE Send(step3, "Data", step3.HomeNodes[h].requester, h, H2D_DATA, step3.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:2244
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:2244")
        \* msi_opt.m:2245
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:2245")
        \* msi_opt.m:2246
        step7 == IF step6.error # "" THEN step6
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step6 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step6, "Type/range error at msi_opt.m:2246")
    IN step7

Home_HT_ES_AD_CleanEvictNoData_208(r, msg, h) ==
    LET
        \* msi_opt.m:2230
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "GO", r.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "I", 1)
    IN step1

Home_HT_ES_AD_CleanEvictNoData_206(r, msg, h) ==
    LET
        \* msi_opt.m:2229
        step1 == IF r.error # "" THEN r
                 ELSE IF (r.HomeNodes[h].snp_data_sent = 1) THEN Home_HT_ES_AD_CleanEvictNoData_208(r, msg, h)
                ELSE Home_HT_ES_AD_CleanEvictNoData_207(r, msg, h)
    IN step1

Home_HT_ES_AD_CleanEvictNoData_210(r, msg, h) ==
    LET
        \* msi_opt.m:2258
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_S" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_S"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2258")
        \* msi_opt.m:2259
        step2 == IF step1.error # "" THEN step1
                 ELSE RemoveFromSharersList(step1, msg.src, h)
        \* msi_opt.m:2261
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO", step2.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "S", 1)
        \* msi_opt.m:2264
        step4 == IF step3.error # "" THEN step3
                 ELSE Send(step3, "Data", step3.HomeNodes[h].requester, h, H2D_DATA, step3.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:2267
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:2267")
        \* msi_opt.m:2268
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:2268")
        \* msi_opt.m:2269
        step7 == IF step6.error # "" THEN step6
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step6 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step6, "Type/range error at msi_opt.m:2269")
    IN step7

Home_HT_ES_AD_CleanEvictNoData_211(r, msg, h) ==
    LET
        \* msi_opt.m:2254
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "GO", r.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "I", 1)
    IN step1

Home_HT_ES_AD_CleanEvictNoData_209(r, msg, h) ==
    LET
        \* msi_opt.m:2253
        step1 == IF r.error # "" THEN r
                 ELSE IF (r.HomeNodes[h].snp_data_sent = 1) THEN Home_HT_ES_AD_CleanEvictNoData_211(r, msg, h)
                ELSE Home_HT_ES_AD_CleanEvictNoData_210(r, msg, h)
    IN step1

Home_HT_ES_AD_CleanEvictNoData_212(r, msg, h) ==
    LET
        \* msi_opt.m:2272
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_ES_AD_CleanEvictNoData_205(r, msg, h) ==
    LET
        \* msi_opt.m:2224
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "RdShared") -> Home_HT_ES_AD_CleanEvictNoData_206(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "RdAny") -> Home_HT_ES_AD_CleanEvictNoData_209(r, msg, h)
                 [] OTHER -> Home_HT_ES_AD_CleanEvictNoData_212(r, msg, h)
    IN step1

Home_HT_ES_AD_CleanEvict_213(r, msg, h) ==
    LET
        \* msi_opt.m:2275
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_IS_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_IS_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2275")
    IN step1

Home_HT_ES_AD_DirtyEvict_214(r, msg, h) ==
    LET
        \* msi_opt.m:2277
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_IS_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_IS_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2277")
    IN step1

Home_HT_ES_AD_215(r, msg, h) ==
    LET
        \* msi_opt.m:2305
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_ES_AD_192(r, msg, h) ==
    LET
        \* msi_opt.m:2151
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "RspSHitSE") -> Home_HT_ES_AD_RspSHitSE_193(r, msg, h)
                 [] (msg.mtype = "RspSFwdM") -> Home_HT_ES_AD_RspSFwdM_197(r, msg, h)
                 [] (msg.mtype = "Data") -> Home_HT_ES_AD_Data_201(r, msg, h)
                 [] (msg.mtype = "CleanEvictNoData") -> Home_HT_ES_AD_CleanEvictNoData_205(r, msg, h)
                 [] (msg.mtype = "CleanEvict") -> Home_HT_ES_AD_CleanEvict_213(r, msg, h)
                 [] (msg.mtype = "DirtyEvict") -> Home_HT_ES_AD_DirtyEvict_214(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_ES_AD_215(r, msg, h)
    IN step1

Home_HT_ES_A_RspSHitSE_218(r, msg, h) ==
    LET
        \* msi_opt.m:2313
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_S" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_S"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2313")
        \* msi_opt.m:2314
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO", step1.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "S", 1)
        \* msi_opt.m:2317
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "Data", step2.HomeNodes[h].requester, h, H2D_DATA, step2.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:2320
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:2320")
        \* msi_opt.m:2321
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:2321")
        \* msi_opt.m:2322
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:2322")
    IN step6

Home_HT_ES_A_RspSHitSE_219(r, msg, h) ==
    LET
        \* msi_opt.m:2324
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_S" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_S"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2324")
        \* msi_opt.m:2325
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO", step1.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "S", 1)
        \* msi_opt.m:2328
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "Data", step2.HomeNodes[h].requester, h, H2D_DATA, step2.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:2331
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:2331")
        \* msi_opt.m:2332
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:2332")
        \* msi_opt.m:2333
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:2333")
    IN step6

Home_HT_ES_A_RspSHitSE_220(r, msg, h) ==
    LET
        \* msi_opt.m:2335
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_ES_A_RspSHitSE_217(r, msg, h) ==
    LET
        \* msi_opt.m:2311
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "RdShared") -> Home_HT_ES_A_RspSHitSE_218(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "RdAny") -> Home_HT_ES_A_RspSHitSE_219(r, msg, h)
                 [] OTHER -> Home_HT_ES_A_RspSHitSE_220(r, msg, h)
    IN step1

Home_HT_ES_A_RspSFwdM_222(r, msg, h) ==
    LET
        \* msi_opt.m:2340
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_S" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_S"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2340")
        \* msi_opt.m:2341
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO", step1.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "S", 1)
        \* msi_opt.m:2344
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "Data", step2.HomeNodes[h].requester, h, H2D_DATA, step2.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:2347
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:2347")
        \* msi_opt.m:2348
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:2348")
        \* msi_opt.m:2349
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:2349")
    IN step6

Home_HT_ES_A_RspSFwdM_223(r, msg, h) ==
    LET
        \* msi_opt.m:2351
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_S" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_S"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2351")
        \* msi_opt.m:2352
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO", step1.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "S", 1)
        \* msi_opt.m:2355
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "Data", step2.HomeNodes[h].requester, h, H2D_DATA, step2.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:2358
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:2358")
        \* msi_opt.m:2359
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:2359")
        \* msi_opt.m:2360
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:2360")
    IN step6

Home_HT_ES_A_RspSFwdM_224(r, msg, h) ==
    LET
        \* msi_opt.m:2362
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_ES_A_RspSFwdM_221(r, msg, h) ==
    LET
        \* msi_opt.m:2338
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "RdShared") -> Home_HT_ES_A_RspSFwdM_222(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "RdAny") -> Home_HT_ES_A_RspSFwdM_223(r, msg, h)
                 [] OTHER -> Home_HT_ES_A_RspSFwdM_224(r, msg, h)
    IN step1

Home_HT_ES_A_225(r, msg, h) ==
    LET
        \* msi_opt.m:2391
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_ES_A_216(r, msg, h) ==
    LET
        \* msi_opt.m:2309
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "RspSHitSE") -> Home_HT_ES_A_RspSHitSE_217(r, msg, h)
                 [] (msg.mtype = "RspSFwdM") -> Home_HT_ES_A_RspSFwdM_221(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_ES_A_225(r, msg, h)
    IN step1

Home_HT_ES_D_Data_228(r, msg, h) ==
    LET
        \* msi_opt.m:2399
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_S" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_S"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2399")
        \* msi_opt.m:2400
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2400")
        \* msi_opt.m:2402
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO", step2.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "S", 1)
        \* msi_opt.m:2405
        step4 == IF step3.error # "" THEN step3
                 ELSE Send(step3, "Data", step3.HomeNodes[h].requester, h, H2D_DATA, step3.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:2408
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:2408")
        \* msi_opt.m:2409
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:2409")
        \* msi_opt.m:2410
        step7 == IF step6.error # "" THEN step6
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step6 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step6, "Type/range error at msi_opt.m:2410")
    IN step7

Home_HT_ES_D_Data_229(r, msg, h) ==
    LET
        \* msi_opt.m:2412
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_S" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_S"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2412")
        \* msi_opt.m:2413
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2413")
        \* msi_opt.m:2415
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO", step2.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "S", 1)
        \* msi_opt.m:2418
        step4 == IF step3.error # "" THEN step3
                 ELSE Send(step3, "Data", step3.HomeNodes[h].requester, h, H2D_DATA, step3.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:2421
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:2421")
        \* msi_opt.m:2422
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:2422")
        \* msi_opt.m:2423
        step7 == IF step6.error # "" THEN step6
                 ELSE IF Undefined \in (0..1) \cup {Undefined} THEN
                    [step6 EXCEPT !.HomeNodes[h].request_pre = Undefined]
                ELSE Fail(step6, "Type/range error at msi_opt.m:2423")
    IN step7

Home_HT_ES_D_Data_230(r, msg, h) ==
    LET
        \* msi_opt.m:2425
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_ES_D_Data_227(r, msg, h) ==
    LET
        \* msi_opt.m:2397
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "RdShared") -> Home_HT_ES_D_Data_228(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "RdAny") -> Home_HT_ES_D_Data_229(r, msg, h)
                 [] OTHER -> Home_HT_ES_D_Data_230(r, msg, h)
    IN step1

Home_HT_ES_D_231(r, msg, h) ==
    LET
        \* msi_opt.m:2454
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_ES_D_226(r, msg, h) ==
    LET
        \* msi_opt.m:2395
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "Data") -> Home_HT_ES_D_Data_227(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_ES_D_231(r, msg, h)
    IN step1

Home_H_S_RdShared_233(r, msg, h) ==
    LET
        \* msi_opt.m:2466
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "GO", msg.src, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "S", 1)
        \* msi_opt.m:2469
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "Data", msg.src, h, H2D_DATA, step1.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:2472
        step3 == IF step2.error # "" THEN step2
                 ELSE AddToSharersList(step2, msg.src, h)
    IN step3

Home_H_S_RdAny_234(r, msg, h) ==
    LET
        \* msi_opt.m:2477
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "GO", msg.src, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "S", 1)
        \* msi_opt.m:2480
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "Data", msg.src, h, H2D_DATA, step1.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:2483
        step3 == IF step2.error # "" THEN step2
                 ELSE AddToSharersList(step2, msg.src, h)
    IN step3

Home_H_S_RdCurr_235(r, msg, h) ==
    LET
        \* msi_opt.m:2488
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "Data", msg.src, h, H2D_DATA, r.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
    IN step1

InvalidateStep470(r, rqst, h, msg, n) ==
    LET
        \* msi_opt.m:425
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "SnpInv", n, h, H2D_REQ, Undefined, 0, Undefined, msg.cqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

InvalidateStep469(r, rqst, h, msg, n) ==
    LET
        \* msi_opt.m:429
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "SnpInv", n, h, H2D_REQ, Undefined, 1, Undefined, msg.cqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

InvalidateStep468(r, rqst, h, msg, n) ==
    LET
        \* msi_opt.m:424
        step1 == IF r.error # "" THEN r
                 ELSE IF (h = "Home0") THEN InvalidateStep470(r, rqst, h, msg, n)
                ELSE InvalidateStep469(r, rqst, h, msg, n)
    IN step1

InvalidateStep466(r, rqst, h, msg, n) ==
    r

InvalidateStep467(r, rqst, h, msg, n) ==
    LET
        \* msi_opt.m:419
        step1 == IF r.error # "" THEN r
                 ELSE RemoveFromSharersList(r, n, h)
        \* msi_opt.m:420
        step2 == IF step1.error # "" THEN step1
                 ELSE IF (n # rqst) THEN InvalidateStep468(step1, rqst, h, msg, n)
                ELSE InvalidateStep466(step1, rqst, h, msg, n)
    IN step2

InvalidateStep465(r, rqst, h, msg, n) ==
    LET
        \* msi_opt.m:416
        step1 == IF r.error # "" THEN r
                 ELSE IF (((n \in Proc) /\ (Cardinality({i \in r.HomeNodes[h].sharers: (i = n)}) # 0))) THEN InvalidateStep467(r, rqst, h, msg, n)
                ELSE InvalidateStep466(r, rqst, h, msg, n)
    IN step1

InvalidateStep464(r, rqst, h, msg) ==
    LET
        \* msi_opt.m:415
        step1 == IF r.error # "" THEN r
                 ELSE LET Loop470_0(acc, n) == InvalidateStep465(acc, rqst, h, msg, n)
                IN Fold(Loop470_0, r, NodeOrder)
    IN step1

Home_H_S_RdOwnNoData_238(r, msg, h) ==
    LET
        \* msi_opt.m:2519
        step1 == IF r.error # "" THEN r
                 ELSE InvalidateStep464(r, msg.src, h, msg)
        \* msi_opt.m:2520
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "HT_SE_AD" \in (HomeStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].state = "HT_SE_AD"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2520")
        \* msi_opt.m:2521
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step2, "Type/range error at msi_opt.m:2521")
        \* msi_opt.m:2522
        step4 == IF step3.error # "" THEN step3
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step3, "Type/range error at msi_opt.m:2522")
    IN step4

Home_H_S_RdOwnNoData_239(r, msg, h) ==
    LET
        \* msi_opt.m:2514
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "GO", msg.src, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "E", 1)
        \* msi_opt.m:2517
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "H_E" \in (HomeStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].state = "H_E"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2517")
    IN step2

Home_H_S_RdOwnNoData_237(r, msg, h) ==
    LET
        \* msi_opt.m:2513
        step1 == IF r.error # "" THEN r
                 ELSE IF (r.cnt = 0) THEN Home_H_S_RdOwnNoData_239(r, msg, h)
                ELSE Home_H_S_RdOwnNoData_238(r, msg, h)
    IN step1

Home_H_S_RdOwnNoData_241(r, msg, h) ==
    LET
        \* msi_opt.m:2506
        step1 == IF r.error # "" THEN r
                 ELSE InvalidateStep464(r, msg.src, h, msg)
        \* msi_opt.m:2507
        step2 == IF step1.error # "" THEN step1
                 ELSE RemoveFromSharersList(step1, msg.src, h)
        \* msi_opt.m:2508
        step3 == IF step2.error # "" THEN step2
                 ELSE IF "HT_SE_AD" \in (HomeStates) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].state = "HT_SE_AD"]
                ELSE Fail(step2, "Type/range error at msi_opt.m:2508")
        \* msi_opt.m:2509
        step4 == IF step3.error # "" THEN step3
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step3, "Type/range error at msi_opt.m:2509")
        \* msi_opt.m:2510
        step5 == IF step4.error # "" THEN step4
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step4, "Type/range error at msi_opt.m:2510")
    IN step5

Home_H_S_RdOwnNoData_242(r, msg, h) ==
    LET
        \* msi_opt.m:2498
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "GO", msg.src, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "E", 1)
        \* msi_opt.m:2501
        step2 == IF step1.error # "" THEN step1
                 ELSE RemoveFromSharersList(step1, msg.src, h)
        \* msi_opt.m:2503
        step3 == IF step2.error # "" THEN step2
                 ELSE IF "H_E" \in (HomeStates) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].state = "H_E"]
                ELSE Fail(step2, "Type/range error at msi_opt.m:2503")
        \* msi_opt.m:2504
        step4 == IF step3.error # "" THEN step3
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].owner = msg.src]
                ELSE Fail(step3, "Type/range error at msi_opt.m:2504")
    IN step4

Home_H_S_RdOwnNoData_240(r, msg, h) ==
    LET
        \* msi_opt.m:2497
        step1 == IF r.error # "" THEN r
                 ELSE IF (r.cnt = 1) THEN Home_H_S_RdOwnNoData_242(r, msg, h)
                ELSE Home_H_S_RdOwnNoData_241(r, msg, h)
    IN step1

Home_H_S_RdOwnNoData_236(r, msg, h) ==
    LET
        \* msi_opt.m:2496
        step1 == IF r.error # "" THEN r
                 ELSE IF (msg.src \in r.HomeNodes[h].sharers) THEN Home_H_S_RdOwnNoData_240(r, msg, h)
                ELSE Home_H_S_RdOwnNoData_237(r, msg, h)
    IN step1

Home_H_S_RdOwn_245(r, msg, h) ==
    LET
        \* msi_opt.m:2557
        step1 == IF r.error # "" THEN r
                 ELSE InvalidateStep464(r, msg.src, h, msg)
        \* msi_opt.m:2558
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "HT_SE_AD" \in (HomeStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].state = "HT_SE_AD"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2558")
        \* msi_opt.m:2559
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step2, "Type/range error at msi_opt.m:2559")
        \* msi_opt.m:2560
        step4 == IF step3.error # "" THEN step3
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step3, "Type/range error at msi_opt.m:2560")
    IN step4

Home_H_S_RdOwn_246(r, msg, h) ==
    LET
        \* msi_opt.m:2549
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "GO", msg.src, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "E", 1)
        \* msi_opt.m:2552
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "Data", msg.src, h, H2D_DATA, step1.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:2555
        step3 == IF step2.error # "" THEN step2
                 ELSE IF "H_E" \in (HomeStates) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].state = "H_E"]
                ELSE Fail(step2, "Type/range error at msi_opt.m:2555")
    IN step3

Home_H_S_RdOwn_244(r, msg, h) ==
    LET
        \* msi_opt.m:2548
        step1 == IF r.error # "" THEN r
                 ELSE IF (r.cnt = 0) THEN Home_H_S_RdOwn_246(r, msg, h)
                ELSE Home_H_S_RdOwn_245(r, msg, h)
    IN step1

Home_H_S_RdOwn_248(r, msg, h) ==
    LET
        \* msi_opt.m:2541
        step1 == IF r.error # "" THEN r
                 ELSE InvalidateStep464(r, msg.src, h, msg)
        \* msi_opt.m:2542
        step2 == IF step1.error # "" THEN step1
                 ELSE RemoveFromSharersList(step1, msg.src, h)
        \* msi_opt.m:2543
        step3 == IF step2.error # "" THEN step2
                 ELSE IF "HT_SE_AD" \in (HomeStates) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].state = "HT_SE_AD"]
                ELSE Fail(step2, "Type/range error at msi_opt.m:2543")
        \* msi_opt.m:2544
        step4 == IF step3.error # "" THEN step3
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step3, "Type/range error at msi_opt.m:2544")
        \* msi_opt.m:2545
        step5 == IF step4.error # "" THEN step4
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step4, "Type/range error at msi_opt.m:2545")
    IN step5

Home_H_S_RdOwn_249(r, msg, h) ==
    LET
        \* msi_opt.m:2531
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "GO", msg.src, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "E", 1)
        \* msi_opt.m:2534
        step2 == IF step1.error # "" THEN step1
                 ELSE RemoveFromSharersList(step1, msg.src, h)
        \* msi_opt.m:2535
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "Data", msg.src, h, H2D_DATA, step2.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:2538
        step4 == IF step3.error # "" THEN step3
                 ELSE IF "H_E" \in (HomeStates) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].state = "H_E"]
                ELSE Fail(step3, "Type/range error at msi_opt.m:2538")
        \* msi_opt.m:2539
        step5 == IF step4.error # "" THEN step4
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].owner = msg.src]
                ELSE Fail(step4, "Type/range error at msi_opt.m:2539")
    IN step5

Home_H_S_RdOwn_247(r, msg, h) ==
    LET
        \* msi_opt.m:2530
        step1 == IF r.error # "" THEN r
                 ELSE IF (r.cnt = 1) THEN Home_H_S_RdOwn_249(r, msg, h)
                ELSE Home_H_S_RdOwn_248(r, msg, h)
    IN step1

Home_H_S_RdOwn_243(r, msg, h) ==
    LET
        \* msi_opt.m:2529
        step1 == IF r.error # "" THEN r
                 ELSE IF (msg.src \in r.HomeNodes[h].sharers) THEN Home_H_S_RdOwn_247(r, msg, h)
                ELSE Home_H_S_RdOwn_244(r, msg, h)
    IN step1

Home_H_S_WrCur_250(r, msg, h) ==
    LET
        \* msi_opt.m:2567
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_SI_AD" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_SI_AD"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2567")
        \* msi_opt.m:2568
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2568")
        \* msi_opt.m:2569
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step2, "Type/range error at msi_opt.m:2569")
        \* msi_opt.m:2570
        step4 == IF step3.error # "" THEN step3
                 ELSE InvalidateStep464(step3, step3.HomeNodes[h].owner, h, msg)
    IN step4

Home_H_S_ItoMWr_251(r, msg, h) ==
    LET
        \* msi_opt.m:2575
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_SI_AD" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_SI_AD"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2575")
        \* msi_opt.m:2576
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2576")
        \* msi_opt.m:2577
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step2, "Type/range error at msi_opt.m:2577")
        \* msi_opt.m:2578
        step4 == IF step3.error # "" THEN step3
                 ELSE InvalidateStep464(step3, step3.HomeNodes[h].owner, h, msg)
    IN step4

Home_H_S_CleanEvictNoData_253(r, msg, h) ==
    LET
        \* msi_opt.m:2590
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "GO", msg.src, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "I", 1)
        \* msi_opt.m:2593
        step2 == IF step1.error # "" THEN step1
                 ELSE RemoveFromSharersList(step1, msg.src, h)
    IN step2

Home_H_S_CleanEvictNoData_254(r, msg, h) ==
    LET
        \* msi_opt.m:2584
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_I" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2584")
        \* msi_opt.m:2585
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO", msg.src, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "I", 1)
        \* msi_opt.m:2588
        step3 == IF step2.error # "" THEN step2
                 ELSE RemoveFromSharersList(step2, msg.src, h)
    IN step3

Home_H_S_CleanEvictNoData_252(r, msg, h) ==
    LET
        \* msi_opt.m:2583
        step1 == IF r.error # "" THEN r
                 ELSE IF (r.cnt = 1) THEN Home_H_S_CleanEvictNoData_254(r, msg, h)
                ELSE Home_H_S_CleanEvictNoData_253(r, msg, h)
    IN step1

Home_H_S_CLFlush_255(r, msg, h) ==
    LET
        \* msi_opt.m:2599
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_SI_AD" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_SI_AD"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2599")
        \* msi_opt.m:2600
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2600")
        \* msi_opt.m:2601
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step2, "Type/range error at msi_opt.m:2601")
        \* msi_opt.m:2602
        step4 == IF step3.error # "" THEN step3
                 ELSE InvalidateStep464(step3, step3.HomeNodes[h].owner, h, msg)
    IN step4

Home_H_S_WrInv_256(r, msg, h) ==
    LET
        \* msi_opt.m:2607
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_SI_AD" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_SI_AD"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2607")
        \* msi_opt.m:2608
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2608")
        \* msi_opt.m:2609
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step2, "Type/range error at msi_opt.m:2609")
        \* msi_opt.m:2610
        step4 == IF step3.error # "" THEN step3
                 ELSE InvalidateStep464(step3, step3.HomeNodes[h].owner, h, msg)
    IN step4

Home_H_S_CacheFlushed_257(r, msg, h) ==
    LET
        \* msi_opt.m:2613
        step1 == IF r.error # "" THEN r
                 ELSE Check(r, (~((msg.src \in r.HomeNodes[h].sharers))), "CacheFlushed from sharer", 2613)
        \* msi_opt.m:2614
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "H_S" \in (HomeStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].state = "H_S"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2614")
        \* msi_opt.m:2619
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO", msg.src, h, H2D_REQ, Undefined, msg.addr, Undefined, msg.cqid, Undefined, Undefined, Undefined, Undefined, Undefined, "I", 1)
    IN step3

Home_H_S_258(r, msg, h) ==
    LET
        \* msi_opt.m:2624
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_H_S_232(r, msg, h) ==
    LET
        \* msi_opt.m:2459
        step1 == IF r.error # "" THEN r
                 ELSE Check(r, (((r.HomeNodes[h].owner = Undefined) = TRUE)), "HomeNodes has owner, but line is Shared", 2459)
        \* msi_opt.m:2461
        step2 == IF step1.error # "" THEN step1
                 ELSE Check(step1, ((step1.cnt # 0)), "HomeNodes has no sharer, but line is Shared", 2461)
        \* msi_opt.m:2463
        step3 == IF step2.error # "" THEN step2
                 ELSE CASE (msg.mtype = "RdShared") -> Home_H_S_RdShared_233(step2, msg, h)
                 [] (msg.mtype = "RdAny") -> Home_H_S_RdAny_234(step2, msg, h)
                 [] (msg.mtype = "RdCurr") -> Home_H_S_RdCurr_235(step2, msg, h)
                 [] (msg.mtype = "RdOwnNoData") -> Home_H_S_RdOwnNoData_236(step2, msg, h)
                 [] (msg.mtype = "RdOwn") -> Home_H_S_RdOwn_243(step2, msg, h)
                 [] (msg.mtype = "WrCur") -> Home_H_S_WrCur_250(step2, msg, h)
                 [] (msg.mtype = "ItoMWr") -> Home_H_S_ItoMWr_251(step2, msg, h)
                 [] (msg.mtype = "CleanEvictNoData") -> Home_H_S_CleanEvictNoData_252(step2, msg, h)
                 [] (msg.mtype = "CLFlush") -> Home_H_S_CLFlush_255(step2, msg, h)
                 [] (msg.mtype = "WrInv") -> Home_H_S_WrInv_256(step2, msg, h)
                 [] (msg.mtype = "CacheFlushed") -> Home_H_S_CacheFlushed_257(step2, msg, h)
                 [] OTHER -> Home_H_S_258(step2, msg, h)
    IN step3

Home_HT_SI_AD_RspIHitSE_262(r, msg, h) ==
    LET
        \* msi_opt.m:2636
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_I" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2636")
        \* msi_opt.m:2637
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO", step1.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "I", 1)
        \* msi_opt.m:2640
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:2640")
        \* msi_opt.m:2641
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:2641")
    IN step4

Home_HT_SI_AD_RspIHitSE_263(r, msg, h) ==
    LET
        \* msi_opt.m:2645
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_SI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_SI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2645")
        \* msi_opt.m:2646
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "WritePull", step1.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step2

Home_HT_SI_AD_RspIHitSE_264(r, msg, h) ==
    LET
        \* msi_opt.m:2651
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_SI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_SI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2651")
        \* msi_opt.m:2652
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO_WritePull", step1.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step2

Home_HT_SI_AD_RspIHitSE_265(r, msg, h) ==
    LET
        \* msi_opt.m:2657
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_SI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_SI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2657")
        \* msi_opt.m:2658
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO_WritePull", step1.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step2

Home_HT_SI_AD_RspIHitSE_266(r, msg, h) ==
    LET
        \* msi_opt.m:2663
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_SI_AD_RspIHitSE_261(r, msg, h) ==
    LET
        \* msi_opt.m:2633
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "CLFlush") -> Home_HT_SI_AD_RspIHitSE_262(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "WrInv") -> Home_HT_SI_AD_RspIHitSE_263(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "WrCur") -> Home_HT_SI_AD_RspIHitSE_264(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "ItoMWr") -> Home_HT_SI_AD_RspIHitSE_265(r, msg, h)
                 [] OTHER -> Home_HT_SI_AD_RspIHitSE_266(r, msg, h)
    IN step1

Home_HT_SI_AD_RspIHitSE_260(r, msg, h) ==
    LET
        \* msi_opt.m:2632
        step1 == IF r.error # "" THEN r
                 ELSE IF (r.cnt = 0) THEN Home_HT_SI_AD_RspIHitSE_261(r, msg, h)
                ELSE Home_HT_EE_AD_CleanEvict_151(r, msg, h)
    IN step1

Home_HT_SI_AD_267(r, msg, h) ==
    LET
        \* msi_opt.m:2711
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_SI_AD_259(r, msg, h) ==
    LET
        \* msi_opt.m:2629
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "RspIHitSE") -> Home_HT_SI_AD_RspIHitSE_260(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed" \/ msg.mtype = "RspIHitI" \/ msg.mtype = "RspVHitV" \/ msg.mtype = "RspSHitSE" \/ msg.mtype = "RspSFwdM" \/ msg.mtype = "RspIFwdM" \/ msg.mtype = "RspVFwdV") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_SI_AD_267(r, msg, h)
    IN step1

Home_HT_SI_D_Data_270(r, msg, h) ==
    LET
        \* msi_opt.m:2721
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_I" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2721")
        \* msi_opt.m:2722
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2722")
        \* msi_opt.m:2723
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO", step2.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "I", 1)
        \* msi_opt.m:2726
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:2726")
        \* msi_opt.m:2727
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:2727")
    IN step5

Home_HT_SI_D_Data_271(r, msg, h) ==
    LET
        \* msi_opt.m:2730
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_I" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2730")
        \* msi_opt.m:2731
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2731")
        \* msi_opt.m:2732
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:2732")
        \* msi_opt.m:2733
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:2733")
    IN step4

Home_HT_SI_D_Data_272(r, msg, h) ==
    LET
        \* msi_opt.m:2736
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_I" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2736")
        \* msi_opt.m:2737
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2737")
        \* msi_opt.m:2738
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:2738")
        \* msi_opt.m:2739
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:2739")
    IN step4

Home_HT_SI_D_Data_273(r, msg, h) ==
    LET
        \* msi_opt.m:2742
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_SI_D_Data_269(r, msg, h) ==
    LET
        \* msi_opt.m:2719
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "WrInv") -> Home_HT_SI_D_Data_270(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "WrCur") -> Home_HT_SI_D_Data_271(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "ItoMWr") -> Home_HT_SI_D_Data_272(r, msg, h)
                 [] OTHER -> Home_HT_SI_D_Data_273(r, msg, h)
    IN step1

Home_HT_SI_D_274(r, msg, h) ==
    LET
        \* msi_opt.m:2789
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_SI_D_268(r, msg, h) ==
    LET
        \* msi_opt.m:2716
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "Data") -> Home_HT_SI_D_Data_269(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed" \/ msg.mtype = "RspIHitI" \/ msg.mtype = "RspVHitV" \/ msg.mtype = "RspIHitSE" \/ msg.mtype = "RspSHitSE" \/ msg.mtype = "RspSFwdM" \/ msg.mtype = "RspIFwdM" \/ msg.mtype = "RspVFwdV") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_SI_D_274(r, msg, h)
    IN step1

Home_HT_SE_AD_RspIHitSE_278(r, msg, h) ==
    LET
        \* msi_opt.m:2803
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_E" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_E"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2803")
        \* msi_opt.m:2804
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO", step1.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "E", 1)
        \* msi_opt.m:2807
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "Data", step2.HomeNodes[h].requester, h, H2D_DATA, step2.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:2810
        step4 == IF step3.error # "" THEN step3
                 ELSE IF step3.HomeNodes[h].requester \in (Node) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].owner = step3.HomeNodes[h].requester]
                ELSE Fail(step3, "Type/range error at msi_opt.m:2810")
        \* msi_opt.m:2811
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:2811")
        \* msi_opt.m:2812
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:2812")
    IN step6

Home_HT_SE_AD_RspIHitSE_279(r, msg, h) ==
    LET
        \* msi_opt.m:2815
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_E" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_E"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2815")
        \* msi_opt.m:2816
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "GO", step1.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "E", 1)
        \* msi_opt.m:2820
        step3 == IF step2.error # "" THEN step2
                 ELSE IF step2.HomeNodes[h].requester \in (Node) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].owner = step2.HomeNodes[h].requester]
                ELSE Fail(step2, "Type/range error at msi_opt.m:2820")
        \* msi_opt.m:2821
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:2821")
        \* msi_opt.m:2822
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:2822")
    IN step5

Home_HT_SE_AD_RspIHitSE_277(r, msg, h) ==
    LET
        \* msi_opt.m:2800
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.HomeNodes[h].request_type = "RdOwn") -> Home_HT_SE_AD_RspIHitSE_278(r, msg, h)
                 [] (r.HomeNodes[h].request_type = "RdOwnNoData") -> Home_HT_SE_AD_RspIHitSE_279(r, msg, h)
                 [] OTHER -> Home_HT_EE_AD_CleanEvict_151(r, msg, h)
    IN step1

Home_HT_SE_AD_RspIHitSE_276(r, msg, h) ==
    LET
        \* msi_opt.m:2798
        step1 == IF r.error # "" THEN r
                 ELSE Check(r, (((r.HomeNodes[h].request_type = Undefined) = FALSE)), "In HT_SE_AD, request_type should be defined", 2798)
        \* msi_opt.m:2799
        step2 == IF step1.error # "" THEN step1
                 ELSE IF (step1.cnt = 0) THEN Home_HT_SE_AD_RspIHitSE_277(step1, msg, h)
                ELSE Home_HT_EE_AD_CleanEvict_151(step1, msg, h)
    IN step2

Home_HT_SE_AD_280(r, msg, h) ==
    LET
        \* msi_opt.m:2871
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_SE_AD_275(r, msg, h) ==
    LET
        \* msi_opt.m:2794
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "RspIHitSE") -> Home_HT_SE_AD_RspIHitSE_276(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed" \/ msg.mtype = "RspIHitI" \/ msg.mtype = "RspVHitV" \/ msg.mtype = "RspSHitSE" \/ msg.mtype = "RspSFwdM" \/ msg.mtype = "RspIFwdM" \/ msg.mtype = "RspVFwdV" \/ msg.mtype = "Data") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_SE_AD_280(r, msg, h)
    IN step1

Home_H_M_RdCurr_282(r, msg, h) ==
    LET
        \* msi_opt.m:2885
        step1 == IF r.error # "" THEN r
                 ELSE Check(r, ((msg.src # r.HomeNodes[h].owner)), "owner should not request RdCurr", 2885)
        \* msi_opt.m:2887
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "HT_MM_AD" \in (HomeStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].state = "HT_MM_AD"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2887")
        \* msi_opt.m:2888
        step3 == IF step2.error # "" THEN step2
                 ELSE IF 1 \in (0..1) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].snp_cur_sent = 1]
                ELSE Fail(step2, "Type/range error at msi_opt.m:2888")
        \* msi_opt.m:2889
        step4 == IF step3.error # "" THEN step3
                 ELSE Send(step3, "SnpCur", step3.HomeNodes[h].owner, h, H2D_REQ, Undefined, msg.addr, Undefined, msg.cqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step4

Home_H_M_CLFlush_283(r, msg, h) ==
    LET
        \* msi_opt.m:2894
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_MI_AD" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_MI_AD"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2894")
        \* msi_opt.m:2895
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "SnpInv", step1.HomeNodes[h].owner, h, H2D_REQ, Undefined, msg.addr, Undefined, msg.cqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
        \* msi_opt.m:2898
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].owner = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:2898")
    IN step3

Home_H_M_DirtyEvict_284(r, msg, h) ==
    LET
        \* msi_opt.m:2901
        step1 == IF r.error # "" THEN r
                 ELSE Check(r, ((msg.src = r.HomeNodes[h].owner)), "only owner can request DirtyEvict", 2901)
        \* msi_opt.m:2904
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "HT_MI_D" \in (HomeStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].state = "HT_MI_D"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2904")
        \* msi_opt.m:2905
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO_WritePull", msg.src, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
        \* msi_opt.m:2908
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].owner = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:2908")
    IN step4

Home_H_M_WrInv_285(r, msg, h) ==
    LET
        \* msi_opt.m:2911
        step1 == IF r.error # "" THEN r
                 ELSE Check(r, ((msg.src # r.HomeNodes[h].owner)), "owner should not request WrInv", 2911)
        \* msi_opt.m:2913
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "HT_MI_AD1" \in (HomeStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].state = "HT_MI_AD1"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2913")
        \* msi_opt.m:2914
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "SnpInv", step2.HomeNodes[h].owner, h, H2D_REQ, Undefined, msg.addr, Undefined, msg.cqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
        \* msi_opt.m:2917
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].owner = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:2917")
    IN step4

Home_H_M_ItoMWr_286(r, msg, h) ==
    LET
        \* msi_opt.m:2920
        step1 == IF r.error # "" THEN r
                 ELSE Check(r, ((msg.src # r.HomeNodes[h].owner)), "owner should not request ItoMWr", 2920)
        \* msi_opt.m:2922
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "HT_MI_AD1" \in (HomeStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].state = "HT_MI_AD1"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2922")
        \* msi_opt.m:2923
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "SnpInv", step2.HomeNodes[h].owner, h, H2D_REQ, Undefined, msg.addr, Undefined, msg.cqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
        \* msi_opt.m:2926
        step4 == IF step3.error # "" THEN step3
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].owner = msg.src]
                ELSE Fail(step3, "Type/range error at msi_opt.m:2926")
    IN step4

Home_H_M_RdOwn_287(r, msg, h) ==
    LET
        \* msi_opt.m:2929
        step1 == IF r.error # "" THEN r
                 ELSE Check(r, ((msg.src # r.HomeNodes[h].owner)), "owner should not request RdOwn", 2929)
        \* msi_opt.m:2931
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "HT_ME_AD" \in (HomeStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].state = "HT_ME_AD"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2931")
        \* msi_opt.m:2932
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "SnpInv", step2.HomeNodes[h].owner, h, H2D_REQ, Undefined, msg.addr, Undefined, msg.cqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
        \* msi_opt.m:2935
        step4 == IF step3.error # "" THEN step3
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].owner = msg.src]
                ELSE Fail(step3, "Type/range error at msi_opt.m:2935")
    IN step4

Home_H_M_WrCur_288(r, msg, h) ==
    LET
        \* msi_opt.m:2938
        step1 == IF r.error # "" THEN r
                 ELSE Check(r, ((msg.src # r.HomeNodes[h].owner)), "owner should not request WrCur", 2938)
        \* msi_opt.m:2940
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "HT_MI_AD1" \in (HomeStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].state = "HT_MI_AD1"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2940")
        \* msi_opt.m:2941
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "SnpInv", step2.HomeNodes[h].owner, h, H2D_REQ, Undefined, msg.addr, Undefined, msg.cqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step3

Home_H_M_RdShared_289(r, msg, h) ==
    LET
        \* msi_opt.m:2947
        step1 == IF r.error # "" THEN r
                 ELSE Check(r, ((msg.src # r.HomeNodes[h].owner)), "owner should not request RdShared", 2947)
        \* msi_opt.m:2949
        step2 == IF step1.error # "" THEN step1
                 ELSE IF 1 \in (0..1) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].snp_data_sent = 1]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2949")
        \* msi_opt.m:2950
        step3 == IF step2.error # "" THEN step2
                 ELSE IF "HT_MS_AD" \in (HomeStates) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].state = "HT_MS_AD"]
                ELSE Fail(step2, "Type/range error at msi_opt.m:2950")
        \* msi_opt.m:2951
        step4 == IF step3.error # "" THEN step3
                 ELSE Send(step3, "SnpData", step3.HomeNodes[h].owner, h, H2D_REQ, Undefined, msg.addr, Undefined, msg.cqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
        \* msi_opt.m:2954
        step5 == IF step4.error # "" THEN step4
                 ELSE AddToSharersList(step4, msg.src, h)
        \* msi_opt.m:2955
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].owner = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:2955")
    IN step6

Home_H_M_RdAny_290(r, msg, h) ==
    LET
        \* msi_opt.m:2958
        step1 == IF r.error # "" THEN r
                 ELSE Check(r, ((msg.src # r.HomeNodes[h].owner)), "owner should not request RdAny", 2958)
        \* msi_opt.m:2960
        step2 == IF step1.error # "" THEN step1
                 ELSE IF 1 \in (0..1) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].snp_data_sent = 1]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2960")
        \* msi_opt.m:2961
        step3 == IF step2.error # "" THEN step2
                 ELSE IF "HT_MS_AD" \in (HomeStates) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].state = "HT_MS_AD"]
                ELSE Fail(step2, "Type/range error at msi_opt.m:2961")
        \* msi_opt.m:2962
        step4 == IF step3.error # "" THEN step3
                 ELSE Send(step3, "SnpData", step3.HomeNodes[h].owner, h, H2D_REQ, Undefined, msg.addr, Undefined, msg.cqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
        \* msi_opt.m:2965
        step5 == IF step4.error # "" THEN step4
                 ELSE AddToSharersList(step4, msg.src, h)
        \* msi_opt.m:2966
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].owner = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:2966")
    IN step6

Home_H_M_CacheFlushed_291(r, msg, h) ==
    LET
        \* msi_opt.m:2969
        step1 == IF r.error # "" THEN r
                 ELSE Check(r, ((msg.src # r.HomeNodes[h].owner)), "CacheFlushed msg from non-owner", 2969)
        \* msi_opt.m:2970
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "H_M" \in (HomeStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].state = "H_M"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2970")
        \* msi_opt.m:2975
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO", msg.src, h, H2D_REQ, Undefined, msg.addr, Undefined, msg.cqid, Undefined, Undefined, Undefined, Undefined, Undefined, "I", 1)
    IN step3

Home_H_M_292(r, msg, h) ==
    LET
        \* msi_opt.m:2980
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_H_M_281(r, msg, h) ==
    LET
        \* msi_opt.m:2877
        step1 == IF r.error # "" THEN r
                 ELSE Check(r, (((r.HomeNodes[h].owner = Undefined) = FALSE)), "HomeNodes has no owner, but line is Modified", 2877)
        \* msi_opt.m:2880
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.src \in (Node) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].requester = msg.src]
                ELSE Fail(step1, "Type/range error at msi_opt.m:2880")
        \* msi_opt.m:2881
        step3 == IF step2.error # "" THEN step2
                 ELSE IF msg.mtype \in (MessageTypes) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_type = msg.mtype]
                ELSE Fail(step2, "Type/range error at msi_opt.m:2881")
        \* msi_opt.m:2883
        step4 == IF step3.error # "" THEN step3
                 ELSE CASE (msg.mtype = "RdCurr") -> Home_H_M_RdCurr_282(step3, msg, h)
                 [] (msg.mtype = "CLFlush") -> Home_H_M_CLFlush_283(step3, msg, h)
                 [] (msg.mtype = "DirtyEvict") -> Home_H_M_DirtyEvict_284(step3, msg, h)
                 [] (msg.mtype = "WrInv") -> Home_H_M_WrInv_285(step3, msg, h)
                 [] (msg.mtype = "ItoMWr") -> Home_H_M_ItoMWr_286(step3, msg, h)
                 [] (msg.mtype = "RdOwn") -> Home_H_M_RdOwn_287(step3, msg, h)
                 [] (msg.mtype = "WrCur") -> Home_H_M_WrCur_288(step3, msg, h)
                 [] (msg.mtype = "RdShared") -> Home_H_M_RdShared_289(step3, msg, h)
                 [] (msg.mtype = "RdAny") -> Home_H_M_RdAny_290(step3, msg, h)
                 [] (msg.mtype = "CacheFlushed") -> Home_H_M_CacheFlushed_291(step3, msg, h)
                 [] OTHER -> Home_H_M_292(step3, msg, h)
    IN step4

Home_HT_MM_AD_Data_294(r, msg, h) ==
    LET
        \* msi_opt.m:2986
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_MM_A" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_MM_A"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2986")
        \* msi_opt.m:2987
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "Data", step1.HomeNodes[h].requester, h, H2D_DATA, step1.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
    IN step2

Home_HT_MM_AD_RspVFwdV_295(r, msg, h) ==
    LET
        \* msi_opt.m:2991
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_MM_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_MM_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:2991")
    IN step1

Home_HT_MM_AD_296(r, msg, h) ==
    LET
        \* msi_opt.m:3033
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_MM_AD_293(r, msg, h) ==
    LET
        \* msi_opt.m:2984
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "Data") -> Home_HT_MM_AD_Data_294(r, msg, h)
                 [] (msg.mtype = "RspVFwdV") -> Home_HT_MM_AD_RspVFwdV_295(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed" \/ msg.mtype = "RspIHitI" \/ msg.mtype = "RspVHitV" \/ msg.mtype = "RspIHitSE" \/ msg.mtype = "RspSHitSE" \/ msg.mtype = "RspSFwdM" \/ msg.mtype = "RspIFwdM") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_MM_AD_296(r, msg, h)
    IN step1

Home_HT_MM_A_RspVFwdV_298(r, msg, h) ==
    LET
        \* msi_opt.m:3039
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_M" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_M"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3039")
        \* msi_opt.m:3040
        step2 == IF step1.error # "" THEN step1
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step1, "Type/range error at msi_opt.m:3040")
        \* msi_opt.m:3041
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:3041")
    IN step3

Home_HT_MM_A_299(r, msg, h) ==
    LET
        \* msi_opt.m:3085
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_MM_A_297(r, msg, h) ==
    LET
        \* msi_opt.m:3037
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "RspVFwdV") -> Home_HT_MM_A_RspVFwdV_298(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed" \/ msg.mtype = "RspIHitI" \/ msg.mtype = "RspVHitV" \/ msg.mtype = "RspIHitSE" \/ msg.mtype = "RspSHitSE" \/ msg.mtype = "RspSFwdM" \/ msg.mtype = "RspIFwdM" \/ msg.mtype = "Data") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_MM_A_299(r, msg, h)
    IN step1

Home_HT_MM_D_Data_301(r, msg, h) ==
    LET
        \* msi_opt.m:3091
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_M" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_M"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3091")
        \* msi_opt.m:3092
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "Data", step1.HomeNodes[h].requester, h, H2D_DATA, step1.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:3095
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:3095")
        \* msi_opt.m:3096
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:3096")
    IN step4

Home_HT_MM_D_302(r, msg, h) ==
    LET
        \* msi_opt.m:3140
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_MM_D_300(r, msg, h) ==
    LET
        \* msi_opt.m:3089
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "Data") -> Home_HT_MM_D_Data_301(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed" \/ msg.mtype = "RspIHitI" \/ msg.mtype = "RspVHitV" \/ msg.mtype = "RspIHitSE" \/ msg.mtype = "RspSHitSE" \/ msg.mtype = "RspSFwdM" \/ msg.mtype = "RspIFwdM" \/ msg.mtype = "RspVFwdV") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_MM_D_302(r, msg, h)
    IN step1

Home_HT_MI_AD1_Data_304(r, msg, h) ==
    LET
        \* msi_opt.m:3146
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_MI_A1" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_MI_A1"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3146")
        \* msi_opt.m:3147
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:3147")
    IN step2

Home_HT_MI_AD1_RspIFwdM_305(r, msg, h) ==
    LET
        \* msi_opt.m:3149
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_MI_D1" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_MI_D1"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3149")
    IN step1

Home_HT_MI_AD1_306(r, msg, h) ==
    LET
        \* msi_opt.m:3191
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_MI_AD1_303(r, msg, h) ==
    LET
        \* msi_opt.m:3144
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "Data") -> Home_HT_MI_AD1_Data_304(r, msg, h)
                 [] (msg.mtype = "RspIFwdM") -> Home_HT_MI_AD1_RspIFwdM_305(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed" \/ msg.mtype = "RspIHitI" \/ msg.mtype = "RspVHitV" \/ msg.mtype = "RspIHitSE" \/ msg.mtype = "RspSHitSE" \/ msg.mtype = "RspSFwdM" \/ msg.mtype = "RspVFwdV") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_MI_AD1_306(r, msg, h)
    IN step1

Home_HT_MI_A1_RspIFwdM_309(r, msg, h) ==
    LET
        \* msi_opt.m:3200
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "WritePull", r.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step1

Home_HT_MI_A1_RspIFwdM_310(r, msg, h) ==
    LET
        \* msi_opt.m:3204
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "GO_WritePull", r.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step1

Home_HT_MI_A1_RspIFwdM_311(r, msg, h) ==
    LET
        \* msi_opt.m:3208
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "GO_WritePull", r.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step1

Home_HT_MI_A1_RspIFwdM_312(r, msg, h) ==
    LET
        \* msi_opt.m:3212
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledState(r)
    IN step1

Home_HT_MI_A1_RspIFwdM_308(r, msg, h) ==
    LET
        \* msi_opt.m:3197
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_MI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_MI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3197")
        \* msi_opt.m:3198
        step2 == IF step1.error # "" THEN step1
                 ELSE CASE (step1.HomeNodes[h].request_type = "WrInv") -> Home_HT_MI_A1_RspIFwdM_309(step1, msg, h)
                 [] (step1.HomeNodes[h].request_type = "ItoMWr") -> Home_HT_MI_A1_RspIFwdM_310(step1, msg, h)
                 [] (step1.HomeNodes[h].request_type = "WrCur") -> Home_HT_MI_A1_RspIFwdM_311(step1, msg, h)
                 [] OTHER -> Home_HT_MI_A1_RspIFwdM_312(step1, msg, h)
    IN step2

Home_HT_MI_A1_313(r, msg, h) ==
    LET
        \* msi_opt.m:3257
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_MI_A1_307(r, msg, h) ==
    LET
        \* msi_opt.m:3195
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "RspIFwdM") -> Home_HT_MI_A1_RspIFwdM_308(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed" \/ msg.mtype = "RspIHitI" \/ msg.mtype = "RspVHitV" \/ msg.mtype = "RspIHitSE" \/ msg.mtype = "RspSHitSE" \/ msg.mtype = "RspSFwdM" \/ msg.mtype = "RspVFwdV" \/ msg.mtype = "Data") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_MI_A1_313(r, msg, h)
    IN step1

Home_HT_MI_D1_Data_316(r, msg, h) ==
    LET
        \* msi_opt.m:3267
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "WritePull", r.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step1

Home_HT_MI_D1_Data_317(r, msg, h) ==
    LET
        \* msi_opt.m:3271
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "GO_WritePull", r.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step1

Home_HT_MI_D1_Data_318(r, msg, h) ==
    LET
        \* msi_opt.m:3275
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "GO_WritePull", r.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, msg.uqid, 1)
    IN step1

Home_HT_MI_D1_Data_319(r, msg, h) ==
    LET
        \* msi_opt.m:3279
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledState(r)
    IN step1

Home_HT_MI_D1_Data_315(r, msg, h) ==
    LET
        \* msi_opt.m:3263
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_MI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_MI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3263")
        \* msi_opt.m:3264
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:3264")
        \* msi_opt.m:3265
        step3 == IF step2.error # "" THEN step2
                 ELSE CASE (step2.HomeNodes[h].request_type = "WrInv") -> Home_HT_MI_D1_Data_316(step2, msg, h)
                 [] (step2.HomeNodes[h].request_type = "ItoMWr") -> Home_HT_MI_D1_Data_317(step2, msg, h)
                 [] (step2.HomeNodes[h].request_type = "WrCur") -> Home_HT_MI_D1_Data_318(step2, msg, h)
                 [] OTHER -> Home_HT_MI_D1_Data_319(step2, msg, h)
    IN step3

Home_HT_MI_D1_320(r, msg, h) ==
    LET
        \* msi_opt.m:3324
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_MI_D1_314(r, msg, h) ==
    LET
        \* msi_opt.m:3261
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "Data") -> Home_HT_MI_D1_Data_315(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed" \/ msg.mtype = "RspIHitI" \/ msg.mtype = "RspVHitV" \/ msg.mtype = "RspIHitSE" \/ msg.mtype = "RspSHitSE" \/ msg.mtype = "RspSFwdM" \/ msg.mtype = "RspIFwdM" \/ msg.mtype = "RspVFwdV") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_MI_D1_320(r, msg, h)
    IN step1

Home_HT_MI_AD_Data_322(r, msg, h) ==
    LET
        \* msi_opt.m:3332
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_MI_A" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_MI_A"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3332")
        \* msi_opt.m:3333
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:3333")
        \* msi_opt.m:3334
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO", step2.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "I", 1)
    IN step3

Home_HT_MI_AD_RspIFwdM_323(r, msg, h) ==
    LET
        \* msi_opt.m:3338
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_MI_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_MI_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3338")
    IN step1

Home_HT_MI_AD_324(r, msg, h) ==
    LET
        \* msi_opt.m:3380
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_MI_AD_321(r, msg, h) ==
    LET
        \* msi_opt.m:3328
        step1 == IF r.error # "" THEN r
                 ELSE Check(r, ((r.HomeNodes[h].request_type = "CLFlush")), "only CLFlush should be here", 3328)
        \* msi_opt.m:3330
        step2 == IF step1.error # "" THEN step1
                 ELSE CASE (msg.mtype = "Data") -> Home_HT_MI_AD_Data_322(step1, msg, h)
                 [] (msg.mtype = "RspIFwdM") -> Home_HT_MI_AD_RspIFwdM_323(step1, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed" \/ msg.mtype = "RspIHitI" \/ msg.mtype = "RspVHitV" \/ msg.mtype = "RspIHitSE" \/ msg.mtype = "RspSHitSE" \/ msg.mtype = "RspSFwdM" \/ msg.mtype = "RspVFwdV") -> Home_HT_II_AD_RspIFwdM_28(step1, msg, h)
                 [] OTHER -> Home_HT_MI_AD_324(step1, msg, h)
    IN step2

Home_HT_MI_A_RspIFwdM_326(r, msg, h) ==
    LET
        \* msi_opt.m:3386
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_I" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3386")
        \* msi_opt.m:3387
        step2 == IF step1.error # "" THEN step1
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step1, "Type/range error at msi_opt.m:3387")
        \* msi_opt.m:3388
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:3388")
        \* msi_opt.m:3389
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].owner = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:3389")
    IN step4

Home_HT_MI_A_327(r, msg, h) ==
    LET
        \* msi_opt.m:3432
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_MI_A_325(r, msg, h) ==
    LET
        \* msi_opt.m:3384
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "RspIFwdM") -> Home_HT_MI_A_RspIFwdM_326(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed" \/ msg.mtype = "RspIHitI" \/ msg.mtype = "RspVHitV" \/ msg.mtype = "RspIHitSE" \/ msg.mtype = "RspSHitSE" \/ msg.mtype = "RspSFwdM" \/ msg.mtype = "RspVFwdV" \/ msg.mtype = "Data") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_MI_A_327(r, msg, h)
    IN step1

Home_HT_MI_D_Data_330(r, msg, h) ==
    LET
        \* msi_opt.m:3458
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledState(r)
    IN step1

Home_HT_MI_D_Data_329(r, msg, h) ==
    LET
        \* msi_opt.m:3438
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_I" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3438")
        \* msi_opt.m:3439
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:3439")
        \* msi_opt.m:3440
        step3 == IF step2.error # "" THEN step2
                 ELSE CASE (step2.HomeNodes[h].request_type = "DirtyEvict" \/ step2.HomeNodes[h].request_type = "WrInv" \/ step2.HomeNodes[h].request_type = "CLFlush" \/ step2.HomeNodes[h].request_type = "ItoMWr" \/ step2.HomeNodes[h].request_type = "WrCur") -> Home_HT_EE_AD_CleanEvict_151(step2, msg, h)
                 [] OTHER -> Home_HT_MI_D_Data_330(step2, msg, h)
        \* msi_opt.m:3460
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:3460")
        \* msi_opt.m:3461
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:3461")
        \* msi_opt.m:3462
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].owner = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:3462")
    IN step6

Home_HT_MI_D_331(r, msg, h) ==
    LET
        \* msi_opt.m:3506
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_MI_D_328(r, msg, h) ==
    LET
        \* msi_opt.m:3436
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "Data") -> Home_HT_MI_D_Data_329(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed" \/ msg.mtype = "RspIHitI" \/ msg.mtype = "RspVHitV" \/ msg.mtype = "RspIHitSE" \/ msg.mtype = "RspSHitSE" \/ msg.mtype = "RspSFwdM" \/ msg.mtype = "RspIFwdM" \/ msg.mtype = "RspVFwdV") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_MI_D_331(r, msg, h)
    IN step1

Home_HT_ME_AD_Data_333(r, msg, h) ==
    LET
        \* msi_opt.m:3512
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_ME_A" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_ME_A"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3512")
        \* msi_opt.m:3513
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:3513")
        \* msi_opt.m:3514
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO", step2.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "E", 1)
        \* msi_opt.m:3517
        step4 == IF step3.error # "" THEN step3
                 ELSE Send(step3, "Data", step3.HomeNodes[h].requester, h, H2D_DATA, step3.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
    IN step4

Home_HT_ME_AD_RspIFwdM_334(r, msg, h) ==
    LET
        \* msi_opt.m:3521
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_ME_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_ME_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3521")
    IN step1

Home_HT_ME_AD_335(r, msg, h) ==
    LET
        \* msi_opt.m:3563
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_ME_AD_332(r, msg, h) ==
    LET
        \* msi_opt.m:3510
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "Data") -> Home_HT_ME_AD_Data_333(r, msg, h)
                 [] (msg.mtype = "RspIFwdM") -> Home_HT_ME_AD_RspIFwdM_334(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed" \/ msg.mtype = "RspIHitI" \/ msg.mtype = "RspVHitV" \/ msg.mtype = "RspIHitSE" \/ msg.mtype = "RspSHitSE" \/ msg.mtype = "RspSFwdM" \/ msg.mtype = "RspVFwdV") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_ME_AD_335(r, msg, h)
    IN step1

Home_HT_ME_A_RspIFwdM_337(r, msg, h) ==
    LET
        \* msi_opt.m:3569
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_M" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_M"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3569")
        \* msi_opt.m:3570
        step2 == IF step1.error # "" THEN step1
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step1, "Type/range error at msi_opt.m:3570")
        \* msi_opt.m:3571
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:3571")
    IN step3

Home_HT_ME_A_338(r, msg, h) ==
    LET
        \* msi_opt.m:3615
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_ME_A_336(r, msg, h) ==
    LET
        \* msi_opt.m:3567
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "RspIFwdM") -> Home_HT_ME_A_RspIFwdM_337(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed" \/ msg.mtype = "RspIHitI" \/ msg.mtype = "RspVHitV" \/ msg.mtype = "RspIHitSE" \/ msg.mtype = "RspSHitSE" \/ msg.mtype = "RspSFwdM" \/ msg.mtype = "RspVFwdV" \/ msg.mtype = "Data") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_ME_A_338(r, msg, h)
    IN step1

Home_HT_ME_D_Data_340(r, msg, h) ==
    LET
        \* msi_opt.m:3621
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_M" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_M"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3621")
        \* msi_opt.m:3622
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:3622")
        \* msi_opt.m:3623
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "Data", step2.HomeNodes[h].requester, h, H2D_DATA, step2.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:3626
        step4 == IF step3.error # "" THEN step3
                 ELSE Send(step3, "GO", step3.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "E", 1)
        \* msi_opt.m:3629
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:3629")
        \* msi_opt.m:3630
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:3630")
    IN step6

Home_HT_ME_D_341(r, msg, h) ==
    LET
        \* msi_opt.m:3674
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_ME_D_339(r, msg, h) ==
    LET
        \* msi_opt.m:3619
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "Data") -> Home_HT_ME_D_Data_340(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed" \/ msg.mtype = "RspIHitI" \/ msg.mtype = "RspVHitV" \/ msg.mtype = "RspIHitSE" \/ msg.mtype = "RspSHitSE" \/ msg.mtype = "RspSFwdM" \/ msg.mtype = "RspIFwdM" \/ msg.mtype = "RspVFwdV") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_ME_D_341(r, msg, h)
    IN step1

Home_HT_MS_AD_Data_343(r, msg, h) ==
    LET
        \* msi_opt.m:3680
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_MS_A" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_MS_A"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3680")
        \* msi_opt.m:3681
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:3681")
        \* msi_opt.m:3682
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "GO", step2.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "S", 1)
        \* msi_opt.m:3685
        step4 == IF step3.error # "" THEN step3
                 ELSE Send(step3, "Data", step3.HomeNodes[h].requester, h, H2D_DATA, step3.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
    IN step4

Home_HT_MS_AD_RspIFwdM_344(r, msg, h) ==
    LET
        \* msi_opt.m:3689
        step1 == IF r.error # "" THEN r
                 ELSE IF "HT_MS_D" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "HT_MS_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3689")
    IN step1

Home_HT_MS_AD_345(r, msg, h) ==
    LET
        \* msi_opt.m:3731
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_MS_AD_342(r, msg, h) ==
    LET
        \* msi_opt.m:3678
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "Data") -> Home_HT_MS_AD_Data_343(r, msg, h)
                 [] (msg.mtype = "RspIFwdM") -> Home_HT_MS_AD_RspIFwdM_344(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed" \/ msg.mtype = "RspIHitI" \/ msg.mtype = "RspVHitV" \/ msg.mtype = "RspIHitSE" \/ msg.mtype = "RspSHitSE" \/ msg.mtype = "RspSFwdM" \/ msg.mtype = "RspVFwdV") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_MS_AD_345(r, msg, h)
    IN step1

Home_HT_MS_A_RspIFwdM_347(r, msg, h) ==
    LET
        \* msi_opt.m:3737
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_S" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_S"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3737")
        \* msi_opt.m:3738
        step2 == IF step1.error # "" THEN step1
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step1, "Type/range error at msi_opt.m:3738")
        \* msi_opt.m:3739
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step2 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:3739")
        \* msi_opt.m:3740
        step4 == IF step3.error # "" THEN step3
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [step3 EXCEPT !.HomeNodes[h].snp_data_sent = 0]
                ELSE Fail(step3, "Type/range error at msi_opt.m:3740")
    IN step4

Home_HT_MS_A_348(r, msg, h) ==
    LET
        \* msi_opt.m:3784
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_MS_A_346(r, msg, h) ==
    LET
        \* msi_opt.m:3735
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "RspIFwdM") -> Home_HT_MS_A_RspIFwdM_347(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed" \/ msg.mtype = "RspIHitI" \/ msg.mtype = "RspVHitV" \/ msg.mtype = "RspIHitSE" \/ msg.mtype = "RspSHitSE" \/ msg.mtype = "RspSFwdM" \/ msg.mtype = "RspVFwdV" \/ msg.mtype = "Data") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_MS_A_348(r, msg, h)
    IN step1

Home_HT_MS_D_Data_350(r, msg, h) ==
    LET
        \* msi_opt.m:3790
        step1 == IF r.error # "" THEN r
                 ELSE IF "H_S" \in (HomeStates) \cup {Undefined} THEN
                    [r EXCEPT !.HomeNodes[h].state = "H_S"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3790")
        \* msi_opt.m:3791
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.HomeNodes[h].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:3791")
        \* msi_opt.m:3792
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "Data", step2.HomeNodes[h].requester, h, H2D_DATA, step2.HomeNodes[h].val, Undefined, msg.uqid, Undefined, Undefined, 0, 0, Undefined, 0, Undefined, Undefined)
        \* msi_opt.m:3795
        step4 == IF step3.error # "" THEN step3
                 ELSE Send(step3, "GO", step3.HomeNodes[h].requester, h, H2D_RSP, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, "S", 1)
        \* msi_opt.m:3798
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (Node) \cup {Undefined} THEN
                    [step4 EXCEPT !.HomeNodes[h].requester = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:3798")
        \* msi_opt.m:3799
        step6 == IF step5.error # "" THEN step5
                 ELSE IF Undefined \in (MessageTypes) \cup {Undefined} THEN
                    [step5 EXCEPT !.HomeNodes[h].request_type = Undefined]
                ELSE Fail(step5, "Type/range error at msi_opt.m:3799")
        \* msi_opt.m:3800
        step7 == IF step6.error # "" THEN step6
                 ELSE IF 0 \in (0..1) \cup {Undefined} THEN
                    [step6 EXCEPT !.HomeNodes[h].snp_data_sent = 0]
                ELSE Fail(step6, "Type/range error at msi_opt.m:3800")
    IN step7

Home_HT_MS_D_351(r, msg, h) ==
    LET
        \* msi_opt.m:3844
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, h)
    IN step1

Home_HT_MS_D_349(r, msg, h) ==
    LET
        \* msi_opt.m:3788
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "Data") -> Home_HT_MS_D_Data_350(r, msg, h)
                 [] (msg.mtype = "RdCurr" \/ msg.mtype = "RdOwn" \/ msg.mtype = "RdShared" \/ msg.mtype = "RdAny" \/ msg.mtype = "RdOwnNoData" \/ msg.mtype = "ItoMWr" \/ msg.mtype = "WrCur" \/ msg.mtype = "CLFlush" \/ msg.mtype = "CleanEvict" \/ msg.mtype = "DirtyEvict" \/ msg.mtype = "CleanEvictNoData" \/ msg.mtype = "WrInv" \/ msg.mtype = "CacheFlushed" \/ msg.mtype = "RspIHitI" \/ msg.mtype = "RspVHitV" \/ msg.mtype = "RspIHitSE" \/ msg.mtype = "RspSHitSE" \/ msg.mtype = "RspSFwdM" \/ msg.mtype = "RspIFwdM" \/ msg.mtype = "RspVFwdV") -> Home_HT_II_AD_RspIFwdM_28(r, msg, h)
                 [] OTHER -> Home_HT_MS_D_351(r, msg, h)
    IN step1

HomeStep3(r, msg, h) ==
    LET
        \* msi_opt.m:453
        step1 == IF r.error # "" THEN r
                 ELSE IF Cardinality(r.HomeNodes[h].sharers) \in (0..ProcCount) \cup {Undefined} THEN
                    [r EXCEPT !.cnt = Cardinality(r.HomeNodes[h].sharers)]
                ELSE Fail(r, "Type/range error at msi_opt.m:453")
        \* msi_opt.m:457
        step2 == IF step1.error # "" THEN step1
                 ELSE IF TRUE \in (BOOLEAN) \cup {Undefined} THEN
                    [step1 EXCEPT !.msg_processed = TRUE]
                ELSE Fail(step1, "Type/range error at msi_opt.m:457")
        \* msi_opt.m:459
        step3 == IF step2.error # "" THEN step2
                 ELSE CASE (step2.HomeNodes[h].state = "H_I") -> Home_H_I_4(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_II_AD") -> Home_HT_II_AD_23(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_IS_D") -> Home_HT_IS_D_30(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_IE_AD") -> Home_HT_IE_AD_33(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_IE_D") -> Home_HT_IE_D_37(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_IE_A") -> Home_HT_IE_A_45(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_II_D") -> Home_HT_II_D_53(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "H_E") -> Home_H_E_62(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_EI_AD") -> Home_HT_EI_AD_77(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_EI_A") -> Home_HT_EI_A_103(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_EI_D") -> Home_HT_EI_D_113(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_EE_AD") -> Home_HT_EE_AD_125(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_EE_A") -> Home_HT_EE_A_168(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_EE_D") -> Home_HT_EE_D_183(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_ES_AD") -> Home_HT_ES_AD_192(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_ES_A") -> Home_HT_ES_A_216(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_ES_D") -> Home_HT_ES_D_226(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "H_S") -> Home_H_S_232(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_SI_AD") -> Home_HT_SI_AD_259(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_SI_D") -> Home_HT_SI_D_268(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_SE_AD") -> Home_HT_SE_AD_275(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "H_M") -> Home_H_M_281(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_MM_AD") -> Home_HT_MM_AD_293(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_MM_A") -> Home_HT_MM_A_297(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_MM_D") -> Home_HT_MM_D_300(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_MI_AD1") -> Home_HT_MI_AD1_303(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_MI_A1") -> Home_HT_MI_A1_307(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_MI_D1") -> Home_HT_MI_D1_314(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_MI_AD") -> Home_HT_MI_AD_321(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_MI_A") -> Home_HT_MI_A_325(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_MI_D") -> Home_HT_MI_D_328(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_ME_AD") -> Home_HT_ME_AD_332(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_ME_A") -> Home_HT_ME_A_336(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_ME_D") -> Home_HT_ME_D_339(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_MS_AD") -> Home_HT_MS_AD_342(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_MS_A") -> Home_HT_MS_A_346(step2, msg, h)
                 [] (step2.HomeNodes[h].state = "HT_MS_D") -> Home_HT_MS_D_349(step2, msg, h)
                 [] OTHER -> Home_HT_EE_AD_CleanEvict_151(step2, msg, h)
    IN step3

HomeStep2(r, msg, h) ==
    LET
        \* msi_opt.m:444
        step1 == IF r.error # "" THEN r
                 ELSE HomeStep3(r, msg, h)
    IN step1

HomeStep1(r, msg, h) ==
    LET
        \* msi_opt.m:443
        step1 == IF r.error # "" THEN r
                 ELSE HomeStep2(r, msg, h)
    IN step1

Device_P_I_357(r, msg, p) ==
    LET
        \* msi_opt.m:3870
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, p)
    IN step1

Device_P_I_356(r, msg, p) ==
    LET
        \* msi_opt.m:3867
        step1 == IF r.error # "" THEN r
                 ELSE Device_P_I_357(r, msg, p)
    IN step1

Device_PT_IS_AD_GO_360(r, msg, p) ==
    LET
        \* msi_opt.m:3882
        step1 == IF r.error # "" THEN r
                 ELSE IF FALSE \in (BOOLEAN) \cup {Undefined} THEN
                    [r EXCEPT !.msg_processed = FALSE]
                ELSE Fail(r, "Type/range error at msi_opt.m:3882")
    IN step1

Device_PT_IS_AD_GO_361(r, msg, p) ==
    LET
        \* msi_opt.m:3880
        step1 == IF r.error # "" THEN r
                 ELSE IF "PT_IE_D" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "PT_IE_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3880")
    IN step1

Device_PT_IS_AD_GO_362(r, msg, p) ==
    LET
        \* msi_opt.m:3878
        step1 == IF r.error # "" THEN r
                 ELSE IF "PT_IS_D" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "PT_IS_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3878")
    IN step1

Device_PT_IS_AD_GO_359(r, msg, p) ==
    LET
        \* msi_opt.m:3877
        step1 == IF r.error # "" THEN r
                 ELSE IF (msg.rspdata = "S") THEN Device_PT_IS_AD_GO_362(r, msg, p)
                ELSE IF (msg.rspdata = "E") THEN Device_PT_IS_AD_GO_361(r, msg, p)
                ELSE Device_PT_IS_AD_GO_360(r, msg, p)
    IN step1

Device_PT_IS_AD_Data_363(r, msg, p) ==
    LET
        \* msi_opt.m:3886
        step1 == IF r.error # "" THEN r
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].val = msg.val]
                ELSE Fail(r, "Type/range error at msi_opt.m:3886")
        \* msi_opt.m:3887
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "PT_IS_A" \in (ProcStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.Procs[p].state = "PT_IS_A"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:3887")
    IN step2

Device_PT_IS_AD_364(r, msg, p) ==
    LET
        \* msi_opt.m:3896
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, p)
    IN step1

Device_PT_IS_AD_358(r, msg, p) ==
    LET
        \* msi_opt.m:3874
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "GO") -> Device_PT_IS_AD_GO_359(r, msg, p)
                 [] (msg.mtype = "Data") -> Device_PT_IS_AD_Data_363(r, msg, p)
                 [] (msg.mtype = "SnpInv" \/ msg.mtype = "SnpCur" \/ msg.mtype = "SnpData") -> Device_PT_IS_AD_GO_360(r, msg, p)
                 [] OTHER -> Device_PT_IS_AD_364(r, msg, p)
    IN step1

Device_PT_IS_A_GO_367(r, msg, p) ==
    LET
        \* msi_opt.m:3905
        step1 == IF r.error # "" THEN r
                 ELSE IF "P_E" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "P_E"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3905")
    IN step1

Device_PT_IS_A_GO_368(r, msg, p) ==
    LET
        \* msi_opt.m:3903
        step1 == IF r.error # "" THEN r
                 ELSE IF "P_S" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "P_S"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3903")
    IN step1

Device_PT_IS_A_GO_366(r, msg, p) ==
    LET
        \* msi_opt.m:3902
        step1 == IF r.error # "" THEN r
                 ELSE IF (msg.rspdata = "S") THEN Device_PT_IS_A_GO_368(r, msg, p)
                ELSE IF (msg.rspdata = "E") THEN Device_PT_IS_A_GO_367(r, msg, p)
                ELSE Device_PT_IS_AD_GO_360(r, msg, p)
    IN step1

Device_PT_IS_A_369(r, msg, p) ==
    LET
        \* msi_opt.m:3917
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, p)
    IN step1

Device_PT_IS_A_365(r, msg, p) ==
    LET
        \* msi_opt.m:3900
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "GO") -> Device_PT_IS_A_GO_366(r, msg, p)
                 [] (msg.mtype = "SnpInv" \/ msg.mtype = "SnpCur" \/ msg.mtype = "SnpData") -> Device_PT_IS_AD_GO_360(r, msg, p)
                 [] OTHER -> Device_PT_IS_A_369(r, msg, p)
    IN step1

Device_PT_IS_D_Data_371(r, msg, p) ==
    LET
        \* msi_opt.m:3923
        step1 == IF r.error # "" THEN r
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].val = msg.val]
                ELSE Fail(r, "Type/range error at msi_opt.m:3923")
        \* msi_opt.m:3924
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "P_S" \in (ProcStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.Procs[p].state = "P_S"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:3924")
    IN step2

Device_PT_IS_D_372(r, msg, p) ==
    LET
        \* msi_opt.m:3933
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, p)
    IN step1

Device_PT_IS_D_370(r, msg, p) ==
    LET
        \* msi_opt.m:3921
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "Data") -> Device_PT_IS_D_Data_371(r, msg, p)
                 [] (msg.mtype = "SnpInv" \/ msg.mtype = "SnpCur" \/ msg.mtype = "SnpData") -> Device_PT_IS_AD_GO_360(r, msg, p)
                 [] OTHER -> Device_PT_IS_D_372(r, msg, p)
    IN step1

Device_P_S_SnpInv_374(r, msg, p) ==
    LET
        \* msi_opt.m:3940
        step1 == IF r.error # "" THEN r
                 ELSE IF "P_I" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "P_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3940")
        \* msi_opt.m:3941
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "RspIHitSE", msg.src, p, D2H_RSP, Undefined, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
        \* msi_opt.m:3944
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Address) \cup {Undefined} THEN
                    [step2 EXCEPT !.Procs[p].addr = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:3944")
        \* msi_opt.m:3945
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Value) \cup {Undefined} THEN
                    [step3 EXCEPT !.Procs[p].val = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:3945")
    IN step4

Device_P_S_375(r, msg, p) ==
    LET
        \* msi_opt.m:3948
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, p)
    IN step1

Device_P_S_373(r, msg, p) ==
    LET
        \* msi_opt.m:3937
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "SnpInv") -> Device_P_S_SnpInv_374(r, msg, p)
                 [] OTHER -> Device_P_S_375(r, msg, p)
    IN step1

Device_PT_IM_AD_GO_378(r, msg, p) ==
    LET
        \* msi_opt.m:3955
        step1 == IF r.error # "" THEN r
                 ELSE IF "PT_IM_D" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "PT_IM_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3955")
    IN step1

Device_PT_IM_AD_GO_377(r, msg, p) ==
    LET
        \* msi_opt.m:3954
        step1 == IF r.error # "" THEN r
                 ELSE IF (msg.rspdata = "M") THEN Device_PT_IM_AD_GO_378(r, msg, p)
                ELSE Device_PT_IS_AD_GO_360(r, msg, p)
    IN step1

Device_PT_IM_AD_Data_379(r, msg, p) ==
    LET
        \* msi_opt.m:3960
        step1 == IF r.error # "" THEN r
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].val = msg.val]
                ELSE Fail(r, "Type/range error at msi_opt.m:3960")
        \* msi_opt.m:3961
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "PT_IM_A" \in (ProcStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.Procs[p].state = "PT_IM_A"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:3961")
    IN step2

Device_PT_IM_AD_380(r, msg, p) ==
    LET
        \* msi_opt.m:3969
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, p)
    IN step1

Device_PT_IM_AD_376(r, msg, p) ==
    LET
        \* msi_opt.m:3952
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "GO") -> Device_PT_IM_AD_GO_377(r, msg, p)
                 [] (msg.mtype = "Data") -> Device_PT_IM_AD_Data_379(r, msg, p)
                 [] (msg.mtype = "SnpInv" \/ msg.mtype = "SnpCur" \/ msg.mtype = "SnpData") -> Device_PT_IS_AD_GO_360(r, msg, p)
                 [] OTHER -> Device_PT_IM_AD_380(r, msg, p)
    IN step1

Device_PT_IM_D_Data_382(r, msg, p) ==
    LET
        \* msi_opt.m:3975
        step1 == IF r.error # "" THEN r
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].val = msg.val]
                ELSE Fail(r, "Type/range error at msi_opt.m:3975")
        \* msi_opt.m:3976
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "P_M" \in (ProcStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.Procs[p].state = "P_M"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:3976")
    IN step2

Device_PT_IM_D_383(r, msg, p) ==
    LET
        \* msi_opt.m:3984
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, p)
    IN step1

Device_PT_IM_D_381(r, msg, p) ==
    LET
        \* msi_opt.m:3973
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "Data") -> Device_PT_IM_D_Data_382(r, msg, p)
                 [] (msg.mtype = "SnpInv" \/ msg.mtype = "SnpCur" \/ msg.mtype = "SnpData") -> Device_PT_IS_AD_GO_360(r, msg, p)
                 [] OTHER -> Device_PT_IM_D_383(r, msg, p)
    IN step1

Device_PT_IM_A_GO_386(r, msg, p) ==
    LET
        \* msi_opt.m:3991
        step1 == IF r.error # "" THEN r
                 ELSE IF "P_M" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "P_M"]
                ELSE Fail(r, "Type/range error at msi_opt.m:3991")
    IN step1

Device_PT_IM_A_GO_385(r, msg, p) ==
    LET
        \* msi_opt.m:3990
        step1 == IF r.error # "" THEN r
                 ELSE IF (msg.rspdata = "M") THEN Device_PT_IM_A_GO_386(r, msg, p)
                ELSE Device_PT_IS_AD_GO_360(r, msg, p)
    IN step1

Device_PT_IM_A_387(r, msg, p) ==
    LET
        \* msi_opt.m:4002
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, p)
    IN step1

Device_PT_IM_A_384(r, msg, p) ==
    LET
        \* msi_opt.m:3988
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "GO") -> Device_PT_IM_A_GO_385(r, msg, p)
                 [] (msg.mtype = "SnpInv" \/ msg.mtype = "SnpCur" \/ msg.mtype = "SnpData") -> Device_PT_IS_AD_GO_360(r, msg, p)
                 [] OTHER -> Device_PT_IM_A_387(r, msg, p)
    IN step1

Device_PT_SI_GOI_GO_389(r, msg, p) ==
    LET
        \* msi_opt.m:4008
        step1 == IF r.error # "" THEN r
                 ELSE Check(r, ((msg.rspdata = "I")), "The GO received should be GO-I", 4008)
        \* msi_opt.m:4009
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "P_I" \in (ProcStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.Procs[p].state = "P_I"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:4009")
        \* msi_opt.m:4010
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Address) \cup {Undefined} THEN
                    [step2 EXCEPT !.Procs[p].addr = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:4010")
        \* msi_opt.m:4011
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Value) \cup {Undefined} THEN
                    [step3 EXCEPT !.Procs[p].val = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:4011")
    IN step4

Device_PT_SI_GOI_SnpInv_390(r, msg, p) ==
    LET
        \* msi_opt.m:4014
        step1 == IF r.error # "" THEN r
                 ELSE IF "PT_II_GOI" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "PT_II_GOI"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4014")
        \* msi_opt.m:4015
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "RspIHitSE", msg.src, p, D2H_RSP, Undefined, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
        \* msi_opt.m:4018
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Address) \cup {Undefined} THEN
                    [step2 EXCEPT !.Procs[p].addr = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:4018")
        \* msi_opt.m:4019
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Value) \cup {Undefined} THEN
                    [step3 EXCEPT !.Procs[p].val = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:4019")
    IN step4

Device_PT_SI_GOI_SnpCur_391(r, msg, p) ==
    LET
        \* msi_opt.m:4022
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "RspSHitSE", msg.src, p, D2H_RSP, Undefined, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
        \* msi_opt.m:4025
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "Data", msg.src, p, D2H_DATA, step1.Procs[p].val, Undefined, Undefined, msg.uqid, Undefined, 0, 0, 0, Undefined, Undefined, Undefined)
    IN step2

Device_PT_SI_GOI_SnpData_392(r, msg, p) ==
    LET
        \* msi_opt.m:4030
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "RspSHitSE", msg.src, p, D2H_RSP, Undefined, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

Device_PT_SI_GOI_393(r, msg, p) ==
    LET
        \* msi_opt.m:4037
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, p)
    IN step1

Device_PT_SI_GOI_388(r, msg, p) ==
    LET
        \* msi_opt.m:4006
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "GO") -> Device_PT_SI_GOI_GO_389(r, msg, p)
                 [] (msg.mtype = "SnpInv") -> Device_PT_SI_GOI_SnpInv_390(r, msg, p)
                 [] (msg.mtype = "SnpCur") -> Device_PT_SI_GOI_SnpCur_391(r, msg, p)
                 [] (msg.mtype = "SnpData") -> Device_PT_SI_GOI_SnpData_392(r, msg, p)
                 [] OTHER -> Device_PT_SI_GOI_393(r, msg, p)
    IN step1

Device_PT_II_D_Data_395(r, msg, p) ==
    LET
        \* msi_opt.m:4044
        step1 == IF r.error # "" THEN r
                 ELSE IF Undefined \in (Value) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].val = Undefined]
                ELSE Fail(r, "Type/range error at msi_opt.m:4044")
        \* msi_opt.m:4045
        step2 == IF step1.error # "" THEN step1
                 ELSE IF Undefined \in (Address) \cup {Undefined} THEN
                    [step1 EXCEPT !.Procs[p].addr = Undefined]
                ELSE Fail(step1, "Type/range error at msi_opt.m:4045")
        \* msi_opt.m:4046
        step3 == IF step2.error # "" THEN step2
                 ELSE IF "P_I" \in (ProcStates) \cup {Undefined} THEN
                    [step2 EXCEPT !.Procs[p].state = "P_I"]
                ELSE Fail(step2, "Type/range error at msi_opt.m:4046")
    IN step3

Device_PT_II_D_396(r, msg, p) ==
    LET
        \* msi_opt.m:4051
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, p)
    IN step1

Device_PT_II_D_394(r, msg, p) ==
    LET
        \* msi_opt.m:4042
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "Data") -> Device_PT_II_D_Data_395(r, msg, p)
                 [] OTHER -> Device_PT_II_D_396(r, msg, p)
    IN step1

Device_PT_II_GOI_GO_398(r, msg, p) ==
    LET
        \* msi_opt.m:4058
        step1 == IF r.error # "" THEN r
                 ELSE Check(r, ((msg.rspdata = "I")), "The GO received should be GO-I", 4058)
        \* msi_opt.m:4059
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "P_I" \in (ProcStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.Procs[p].state = "P_I"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:4059")
    IN step2

Device_PT_II_GOI_399(r, msg, p) ==
    LET
        \* msi_opt.m:4064
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, p)
    IN step1

Device_PT_II_GOI_397(r, msg, p) ==
    LET
        \* msi_opt.m:4056
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "GO") -> Device_PT_II_GOI_GO_398(r, msg, p)
                 [] OTHER -> Device_PT_II_GOI_399(r, msg, p)
    IN step1

Device_PT_II_WP_WritePull_402(r, msg, p) ==
    LET
        \* msi_opt.m:4078
        step1 == IF r.error # "" THEN r
                 ELSE IF r.Procs[p].mem_write_val \in (Value) \cup {Undefined} THEN
                    [r EXCEPT !.LastWrites[1] = r.Procs[p].mem_write_val]
                ELSE Fail(r, "Type/range error at msi_opt.m:4078")
    IN step1

Device_PT_II_WP_WritePull_403(r, msg, p) ==
    LET
        \* msi_opt.m:4076
        step1 == IF r.error # "" THEN r
                 ELSE IF r.Procs[p].mem_write_val \in (Value) \cup {Undefined} THEN
                    [r EXCEPT !.LastWrites[0] = r.Procs[p].mem_write_val]
                ELSE Fail(r, "Type/range error at msi_opt.m:4076")
    IN step1

Device_PT_II_WP_WritePull_401(r, msg, p) ==
    LET
        \* msi_opt.m:4071
        step1 == IF r.error # "" THEN r
                 ELSE IF "PT_II_GO" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "PT_II_GO"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4071")
        \* msi_opt.m:4072
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "Data", msg.src, p, D2H_DATA, step1.Procs[p].mem_write_val, Undefined, Undefined, msg.cqid, Undefined, 0, 0, 0, Undefined, Undefined, Undefined)
        \* msi_opt.m:4075
        step3 == IF step2.error # "" THEN step2
                 ELSE IF (msg.src = "Home0") THEN Device_PT_II_WP_WritePull_403(step2, msg, p)
                ELSE Device_PT_II_WP_WritePull_402(step2, msg, p)
        \* msi_opt.m:4081
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Value) \cup {Undefined} THEN
                    [step3 EXCEPT !.Procs[p].mem_write_val = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:4081")
    IN step4

Device_PT_II_WP_404(r, msg, p) ==
    LET
        \* msi_opt.m:4083
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, p)
    IN step1

Device_PT_II_WP_400(r, msg, p) ==
    LET
        \* msi_opt.m:4069
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "WritePull") -> Device_PT_II_WP_WritePull_401(r, msg, p)
                 [] OTHER -> Device_PT_II_WP_404(r, msg, p)
    IN step1

Device_PT_II_GO_GO_407(r, msg, p) ==
    LET
        \* msi_opt.m:4090
        step1 == IF r.error # "" THEN r
                 ELSE IF "P_I" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "P_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4090")
    IN step1

Device_PT_II_GO_GO_406(r, msg, p) ==
    LET
        \* msi_opt.m:4089
        step1 == IF r.error # "" THEN r
                 ELSE IF (msg.rspdata = "I") THEN Device_PT_II_GO_GO_407(r, msg, p)
                ELSE Device_PT_IS_AD_GO_360(r, msg, p)
    IN step1

Device_PT_II_GO_408(r, msg, p) ==
    LET
        \* msi_opt.m:4095
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, p)
    IN step1

Device_PT_II_GO_405(r, msg, p) ==
    LET
        \* msi_opt.m:4087
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "GO") -> Device_PT_II_GO_GO_406(r, msg, p)
                 [] OTHER -> Device_PT_II_GO_408(r, msg, p)
    IN step1

Device_PT_II_GP_GO_WritePull_411(r, msg, p) ==
    LET
        \* msi_opt.m:4121
        step1 == IF r.error # "" THEN r
                 ELSE IF r.Procs[p].mem_write_val \in (Value) \cup {Undefined} THEN
                    [r EXCEPT !.LastWrites[1] = r.Procs[p].mem_write_val]
                ELSE Fail(r, "Type/range error at msi_opt.m:4121")
    IN step1

Device_PT_II_GP_GO_WritePull_412(r, msg, p) ==
    LET
        \* msi_opt.m:4119
        step1 == IF r.error # "" THEN r
                 ELSE IF r.Procs[p].mem_write_val \in (Value) \cup {Undefined} THEN
                    [r EXCEPT !.LastWrites[0] = r.Procs[p].mem_write_val]
                ELSE Fail(r, "Type/range error at msi_opt.m:4119")
    IN step1

Device_PT_II_GP_GO_WritePull_410(r, msg, p) ==
    LET
        \* msi_opt.m:4113
        step1 == IF r.error # "" THEN r
                 ELSE IF "P_I" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "P_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4113")
        \* msi_opt.m:4114
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "Data", msg.src, p, D2H_DATA, step1.Procs[p].mem_write_val, Undefined, Undefined, msg.cqid, Undefined, 0, 0, 0, Undefined, Undefined, Undefined)
        \* msi_opt.m:4118
        step3 == IF step2.error # "" THEN step2
                 ELSE IF (msg.src = "Home0") THEN Device_PT_II_GP_GO_WritePull_412(step2, msg, p)
                ELSE Device_PT_II_GP_GO_WritePull_411(step2, msg, p)
        \* msi_opt.m:4124
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Value) \cup {Undefined} THEN
                    [step3 EXCEPT !.Procs[p].mem_write_val = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:4124")
    IN step4

Device_PT_II_GP_413(r, msg, p) ==
    LET
        \* msi_opt.m:4126
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, p)
    IN step1

Device_PT_II_GP_409(r, msg, p) ==
    LET
        \* msi_opt.m:4110
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "GO_WritePull") -> Device_PT_II_GP_GO_WritePull_410(r, msg, p)
                 [] OTHER -> Device_PT_II_GP_413(r, msg, p)
    IN step1

Device_P_E_SnpCur_415(r, msg, p) ==
    LET
        \* msi_opt.m:4133
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "Data", msg.src, p, D2H_DATA, r.Procs[p].val, Undefined, Undefined, msg.uqid, 0, 0, Undefined, 0, Undefined, Undefined, Undefined)
        \* msi_opt.m:4136
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "RspVFwdV", msg.src, p, D2H_RSP, Undefined, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step2

Device_P_E_SnpData_416(r, msg, p) ==
    LET
        \* msi_opt.m:4140
        step1 == IF r.error # "" THEN r
                 ELSE IF "P_S" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "P_S"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4140")
        \* msi_opt.m:4141
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "Data", msg.src, p, D2H_DATA, step1.Procs[p].val, Undefined, Undefined, msg.uqid, 0, 0, Undefined, 0, Undefined, Undefined, Undefined)
        \* msi_opt.m:4144
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "RspSHitSE", msg.src, p, D2H_RSP, Undefined, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step3

Device_P_E_SnpInv_417(r, msg, p) ==
    LET
        \* msi_opt.m:4148
        step1 == IF r.error # "" THEN r
                 ELSE IF "P_I" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "P_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4148")
        \* msi_opt.m:4149
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "Data", msg.src, p, D2H_DATA, step1.Procs[p].val, Undefined, Undefined, msg.uqid, 0, 0, Undefined, 0, Undefined, Undefined, Undefined)
        \* msi_opt.m:4152
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "RspIHitSE", msg.src, p, D2H_RSP, Undefined, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
        \* msi_opt.m:4156
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Address) \cup {Undefined} THEN
                    [step3 EXCEPT !.Procs[p].addr = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:4156")
        \* msi_opt.m:4157
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (Value) \cup {Undefined} THEN
                    [step4 EXCEPT !.Procs[p].val = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:4157")
    IN step5

Device_P_E_418(r, msg, p) ==
    LET
        \* msi_opt.m:4159
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, p)
    IN step1

Device_P_E_414(r, msg, p) ==
    LET
        \* msi_opt.m:4131
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "SnpCur") -> Device_P_E_SnpCur_415(r, msg, p)
                 [] (msg.mtype = "SnpData") -> Device_P_E_SnpData_416(r, msg, p)
                 [] (msg.mtype = "SnpInv") -> Device_P_E_SnpInv_417(r, msg, p)
                 [] OTHER -> Device_P_E_418(r, msg, p)
    IN step1

Device_PT_EI_GOI_GO_421(r, msg, p) ==
    LET
        \* msi_opt.m:4166
        step1 == IF r.error # "" THEN r
                 ELSE IF "P_I" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "P_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4166")
        \* msi_opt.m:4167
        step2 == IF step1.error # "" THEN step1
                 ELSE IF Undefined \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.Procs[p].val = Undefined]
                ELSE Fail(step1, "Type/range error at msi_opt.m:4167")
        \* msi_opt.m:4168
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Address) \cup {Undefined} THEN
                    [step2 EXCEPT !.Procs[p].addr = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:4168")
    IN step3

Device_PT_EI_GOI_GO_420(r, msg, p) ==
    LET
        \* msi_opt.m:4165
        step1 == IF r.error # "" THEN r
                 ELSE IF (msg.rspdata = "I") THEN Device_PT_EI_GOI_GO_421(r, msg, p)
                ELSE Device_PT_IS_AD_GO_360(r, msg, p)
    IN step1

Device_PT_EI_GOI_SnpCur_422(r, msg, p) ==
    LET
        \* msi_opt.m:4173
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "Data", msg.src, p, D2H_DATA, r.Procs[p].val, Undefined, Undefined, msg.uqid, 0, 0, Undefined, 0, Undefined, Undefined, Undefined)
        \* msi_opt.m:4176
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "RspVFwdV", msg.src, p, D2H_RSP, Undefined, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step2

Device_PT_EI_GOI_SnpData_423(r, msg, p) ==
    LET
        \* msi_opt.m:4181
        step1 == IF r.error # "" THEN r
                 ELSE IF "P_I" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "P_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4181")
        \* msi_opt.m:4182
        step2 == IF step1.error # "" THEN step1
                 ELSE IF Undefined \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.Procs[p].val = Undefined]
                ELSE Fail(step1, "Type/range error at msi_opt.m:4182")
        \* msi_opt.m:4183
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Address) \cup {Undefined} THEN
                    [step2 EXCEPT !.Procs[p].addr = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:4183")
    IN step3

Device_PT_EI_GOI_SnpInv_424(r, msg, p) ==
    LET
        \* msi_opt.m:4193
        step1 == IF r.error # "" THEN r
                 ELSE IF "P_I" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "P_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4193")
        \* msi_opt.m:4194
        step2 == IF step1.error # "" THEN step1
                 ELSE IF Undefined \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.Procs[p].val = Undefined]
                ELSE Fail(step1, "Type/range error at msi_opt.m:4194")
        \* msi_opt.m:4195
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Address) \cup {Undefined} THEN
                    [step2 EXCEPT !.Procs[p].addr = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:4195")
    IN step3

Device_PT_EI_GOI_425(r, msg, p) ==
    LET
        \* msi_opt.m:4204
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, p)
    IN step1

Device_PT_EI_GOI_419(r, msg, p) ==
    LET
        \* msi_opt.m:4163
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "GO") -> Device_PT_EI_GOI_GO_420(r, msg, p)
                 [] (msg.mtype = "SnpCur") -> Device_PT_EI_GOI_SnpCur_422(r, msg, p)
                 [] (msg.mtype = "SnpData") -> Device_PT_EI_GOI_SnpData_423(r, msg, p)
                 [] (msg.mtype = "SnpInv") -> Device_PT_EI_GOI_SnpInv_424(r, msg, p)
                 [] OTHER -> Device_PT_EI_GOI_425(r, msg, p)
    IN step1

Device_PT_EI_GP_GO_WritePull_427(r, msg, p) ==
    LET
        \* msi_opt.m:4210
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "Data", msg.src, p, D2H_DATA, r.Procs[p].val, Undefined, Undefined, msg.uqid, 0, 0, Undefined, 0, Undefined, Undefined, Undefined)
        \* msi_opt.m:4213
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "P_I" \in (ProcStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.Procs[p].state = "P_I"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:4213")
        \* msi_opt.m:4214
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Value) \cup {Undefined} THEN
                    [step2 EXCEPT !.Procs[p].val = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:4214")
        \* msi_opt.m:4215
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Address) \cup {Undefined} THEN
                    [step3 EXCEPT !.Procs[p].addr = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:4215")
    IN step4

Device_PT_EI_GP_SnpCur_428(r, msg, p) ==
    LET
        \* msi_opt.m:4217
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "Data", msg.src, p, D2H_DATA, r.Procs[p].val, Undefined, Undefined, msg.uqid, 0, 0, Undefined, 0, Undefined, Undefined, Undefined)
        \* msi_opt.m:4220
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "RspVFwdV", msg.src, p, D2H_RSP, Undefined, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step2

Device_PT_EI_GP_SnpData_429(r, msg, p) ==
    LET
        \* msi_opt.m:4225
        step1 == IF r.error # "" THEN r
                 ELSE IF "P_I" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "P_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4225")
        \* msi_opt.m:4227
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "Data", msg.src, p, D2H_DATA, step1.Procs[p].val, Undefined, Undefined, msg.uqid, 0, 0, Undefined, 0, Undefined, Undefined, Undefined)
        \* msi_opt.m:4231
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Value) \cup {Undefined} THEN
                    [step2 EXCEPT !.Procs[p].val = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:4231")
        \* msi_opt.m:4232
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Address) \cup {Undefined} THEN
                    [step3 EXCEPT !.Procs[p].addr = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:4232")
    IN step4

Device_PT_EI_GP_SnpInv_430(r, msg, p) ==
    LET
        \* msi_opt.m:4239
        step1 == IF r.error # "" THEN r
                 ELSE IF "P_I" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "P_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4239")
        \* msi_opt.m:4240
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "Data", msg.src, p, D2H_DATA, step1.Procs[p].val, Undefined, Undefined, msg.uqid, 0, 0, Undefined, 0, Undefined, Undefined, Undefined)
        \* msi_opt.m:4244
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Value) \cup {Undefined} THEN
                    [step2 EXCEPT !.Procs[p].val = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:4244")
        \* msi_opt.m:4245
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Address) \cup {Undefined} THEN
                    [step3 EXCEPT !.Procs[p].addr = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:4245")
    IN step4

Device_PT_EI_GP_431(r, msg, p) ==
    LET
        \* msi_opt.m:4250
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, p)
    IN step1

Device_PT_EI_GP_426(r, msg, p) ==
    LET
        \* msi_opt.m:4208
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "GO_WritePull") -> Device_PT_EI_GP_GO_WritePull_427(r, msg, p)
                 [] (msg.mtype = "SnpCur") -> Device_PT_EI_GP_SnpCur_428(r, msg, p)
                 [] (msg.mtype = "SnpData") -> Device_PT_EI_GP_SnpData_429(r, msg, p)
                 [] (msg.mtype = "SnpInv") -> Device_PT_EI_GP_SnpInv_430(r, msg, p)
                 [] OTHER -> Device_PT_EI_GP_431(r, msg, p)
    IN step1

Device_PT_MI_GP_GO_WritePull_433(r, msg, p) ==
    LET
        \* msi_opt.m:4257
        step1 == IF r.error # "" THEN r
                 ELSE IF "P_I" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "P_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4257")
        \* msi_opt.m:4258
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "Data", msg.src, p, D2H_DATA, step1.Procs[p].val, step1.Procs[p].addr, Undefined, msg.uqid, 0, 0, Undefined, 0, Undefined, Undefined, Undefined)
        \* msi_opt.m:4261
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Address) \cup {Undefined} THEN
                    [step2 EXCEPT !.Procs[p].addr = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:4261")
        \* msi_opt.m:4262
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Value) \cup {Undefined} THEN
                    [step3 EXCEPT !.Procs[p].val = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:4262")
    IN step4

Device_PT_MI_GP_SnpCur_434(r, msg, p) ==
    LET
        \* msi_opt.m:4264
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "Data", msg.src, p, D2H_DATA, r.Procs[p].val, Undefined, Undefined, msg.uqid, 0, 0, Undefined, 0, Undefined, Undefined, Undefined)
        \* msi_opt.m:4267
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "RspVFwdV", msg.src, p, D2H_RSP, Undefined, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step2

Device_PT_MI_GP_SnpData_435(r, msg, p) ==
    LET
        \* msi_opt.m:4278
        step1 == IF r.error # "" THEN r
                 ELSE IF "P_I" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "P_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4278")
        \* msi_opt.m:4280
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "Data", msg.src, p, D2H_DATA, step1.Procs[p].val, Undefined, Undefined, msg.uqid, 0, 0, Undefined, 0, Undefined, Undefined, Undefined)
        \* msi_opt.m:4284
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Value) \cup {Undefined} THEN
                    [step2 EXCEPT !.Procs[p].val = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:4284")
        \* msi_opt.m:4285
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Address) \cup {Undefined} THEN
                    [step3 EXCEPT !.Procs[p].addr = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:4285")
    IN step4

Device_PT_MI_GP_SnpInv_436(r, msg, p) ==
    LET
        \* msi_opt.m:4297
        step1 == IF r.error # "" THEN r
                 ELSE IF "P_I" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "P_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4297")
        \* msi_opt.m:4299
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "Data", msg.src, p, D2H_DATA, step1.Procs[p].val, Undefined, Undefined, msg.uqid, 0, 0, Undefined, 0, Undefined, Undefined, Undefined)
        \* msi_opt.m:4303
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Value) \cup {Undefined} THEN
                    [step2 EXCEPT !.Procs[p].val = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:4303")
        \* msi_opt.m:4304
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Address) \cup {Undefined} THEN
                    [step3 EXCEPT !.Procs[p].addr = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:4304")
    IN step4

Device_PT_MI_GP_437(r, msg, p) ==
    LET
        \* msi_opt.m:4306
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, p)
    IN step1

Device_PT_MI_GP_432(r, msg, p) ==
    LET
        \* msi_opt.m:4255
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "GO_WritePull") -> Device_PT_MI_GP_GO_WritePull_433(r, msg, p)
                 [] (msg.mtype = "SnpCur") -> Device_PT_MI_GP_SnpCur_434(r, msg, p)
                 [] (msg.mtype = "SnpData") -> Device_PT_MI_GP_SnpData_435(r, msg, p)
                 [] (msg.mtype = "SnpInv") -> Device_PT_MI_GP_SnpInv_436(r, msg, p)
                 [] OTHER -> Device_PT_MI_GP_437(r, msg, p)
    IN step1

Device_PT_SE_A_GO_439(r, msg, p) ==
    LET
        \* msi_opt.m:4314
        step1 == IF r.error # "" THEN r
                 ELSE Check(r, ((msg.rspdata = "E")), "The GO received should be GO-E", 4314)
        \* msi_opt.m:4315
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "P_E" \in (ProcStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.Procs[p].state = "P_E"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:4315")
    IN step2

Device_PT_SE_A_SnpCur_440(r, msg, p) ==
    LET
        \* msi_opt.m:4318
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "Data", msg.src, p, D2H_DATA, r.Procs[p].val, Undefined, Undefined, msg.uqid, 0, 0, Undefined, 0, Undefined, Undefined, Undefined)
        \* msi_opt.m:4321
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "RspSHitSE", msg.src, p, D2H_RSP, Undefined, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step2

Device_PT_SE_A_SnpInv_441(r, msg, p) ==
    LET
        \* msi_opt.m:4328
        step1 == IF r.error # "" THEN r
                 ELSE IF "PT_IE_AD" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "PT_IE_AD"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4328")
        \* msi_opt.m:4329
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "RspIHitSE", msg.src, p, D2H_RSP, Undefined, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
        \* msi_opt.m:4332
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Address) \cup {Undefined} THEN
                    [step2 EXCEPT !.Procs[p].addr = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:4332")
        \* msi_opt.m:4333
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Value) \cup {Undefined} THEN
                    [step3 EXCEPT !.Procs[p].val = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:4333")
    IN step4

Device_PT_SE_A_442(r, msg, p) ==
    LET
        \* msi_opt.m:4336
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, p)
    IN step1

Device_PT_SE_A_438(r, msg, p) ==
    LET
        \* msi_opt.m:4311
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "GO") -> Device_PT_SE_A_GO_439(r, msg, p)
                 [] (msg.mtype = "SnpCur") -> Device_PT_SE_A_SnpCur_440(r, msg, p)
                 [] (msg.mtype = "SnpInv") -> Device_PT_SE_A_SnpInv_441(r, msg, p)
                 [] OTHER -> Device_PT_SE_A_442(r, msg, p)
    IN step1

Device_PT_SM_GOE_GO_444(r, msg, p) ==
    LET
        \* msi_opt.m:4345
        step1 == IF r.error # "" THEN r
                 ELSE Check(r, ((msg.rspdata = "E")), "The GO received should be GO-E", 4345)
        \* msi_opt.m:4346
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "P_E" \in (ProcStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.Procs[p].state = "P_E"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:4346")
    IN step2

Device_PT_SM_GOE_SnpCur_445(r, msg, p) ==
    LET
        \* msi_opt.m:4349
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "Data", msg.src, p, D2H_DATA, r.Procs[p].val, Undefined, Undefined, msg.uqid, 0, 0, Undefined, 0, Undefined, Undefined, Undefined)
        \* msi_opt.m:4352
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "RspVFwdV", msg.src, p, D2H_RSP, Undefined, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step2

Device_PT_SM_GOE_SnpInv_446(r, msg, p) ==
    LET
        \* msi_opt.m:4359
        step1 == IF r.error # "" THEN r
                 ELSE IF "PT_IE_AD" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "PT_IE_AD"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4359")
        \* msi_opt.m:4360
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "RspIHitSE", msg.src, p, D2H_RSP, Undefined, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
        \* msi_opt.m:4363
        step3 == IF step2.error # "" THEN step2
                 ELSE IF Undefined \in (Address) \cup {Undefined} THEN
                    [step2 EXCEPT !.Procs[p].addr = Undefined]
                ELSE Fail(step2, "Type/range error at msi_opt.m:4363")
        \* msi_opt.m:4364
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Value) \cup {Undefined} THEN
                    [step3 EXCEPT !.Procs[p].val = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:4364")
    IN step4

Device_PT_SM_GOE_447(r, msg, p) ==
    LET
        \* msi_opt.m:4367
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, p)
    IN step1

Device_PT_SM_GOE_443(r, msg, p) ==
    LET
        \* msi_opt.m:4342
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "GO") -> Device_PT_SM_GOE_GO_444(r, msg, p)
                 [] (msg.mtype = "SnpCur") -> Device_PT_SM_GOE_SnpCur_445(r, msg, p)
                 [] (msg.mtype = "SnpInv") -> Device_PT_SM_GOE_SnpInv_446(r, msg, p)
                 [] OTHER -> Device_PT_SM_GOE_447(r, msg, p)
    IN step1

Device_PT_IE_AD_Data_449(r, msg, p) ==
    LET
        \* msi_opt.m:4374
        step1 == IF r.error # "" THEN r
                 ELSE IF "PT_IE_A" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "PT_IE_A"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4374")
        \* msi_opt.m:4375
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.Procs[p].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:4375")
    IN step2

Device_PT_IE_AD_GO_450(r, msg, p) ==
    LET
        \* msi_opt.m:4378
        step1 == IF r.error # "" THEN r
                 ELSE Check(r, ((msg.rspdata = "E")), "The GO received should be GO-E", 4378)
        \* msi_opt.m:4379
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "PT_IE_D" \in (ProcStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.Procs[p].state = "PT_IE_D"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:4379")
    IN step2

Device_PT_IE_AD_451(r, msg, p) ==
    LET
        \* msi_opt.m:4387
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, p)
    IN step1

Device_PT_IE_AD_448(r, msg, p) ==
    LET
        \* msi_opt.m:4371
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "Data") -> Device_PT_IE_AD_Data_449(r, msg, p)
                 [] (msg.mtype = "GO") -> Device_PT_IE_AD_GO_450(r, msg, p)
                 [] (msg.mtype = "SnpInv" \/ msg.mtype = "SnpCur" \/ msg.mtype = "SnpData") -> Device_PT_IS_AD_GO_360(r, msg, p)
                 [] OTHER -> Device_PT_IE_AD_451(r, msg, p)
    IN step1

Device_PT_IE_A_GO_453(r, msg, p) ==
    LET
        \* msi_opt.m:4394
        step1 == IF r.error # "" THEN r
                 ELSE Check(r, ((msg.rspdata = "E")), "The GO received should be GO-E ", 4394)
        \* msi_opt.m:4395
        step2 == IF step1.error # "" THEN step1
                 ELSE IF "P_E" \in (ProcStates) \cup {Undefined} THEN
                    [step1 EXCEPT !.Procs[p].state = "P_E"]
                ELSE Fail(step1, "Type/range error at msi_opt.m:4395")
    IN step2

Device_PT_IE_A_454(r, msg, p) ==
    LET
        \* msi_opt.m:4403
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, p)
    IN step1

Device_PT_IE_A_452(r, msg, p) ==
    LET
        \* msi_opt.m:4391
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "GO") -> Device_PT_IE_A_GO_453(r, msg, p)
                 [] (msg.mtype = "SnpInv" \/ msg.mtype = "SnpCur" \/ msg.mtype = "SnpData") -> Device_PT_IS_AD_GO_360(r, msg, p)
                 [] OTHER -> Device_PT_IE_A_454(r, msg, p)
    IN step1

Device_PT_IE_D_Data_456(r, msg, p) ==
    LET
        \* msi_opt.m:4410
        step1 == IF r.error # "" THEN r
                 ELSE IF "P_E" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "P_E"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4410")
        \* msi_opt.m:4411
        step2 == IF step1.error # "" THEN step1
                 ELSE IF msg.val \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.Procs[p].val = msg.val]
                ELSE Fail(step1, "Type/range error at msi_opt.m:4411")
    IN step2

Device_PT_IE_D_457(r, msg, p) ==
    LET
        \* msi_opt.m:4419
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, p)
    IN step1

Device_PT_IE_D_455(r, msg, p) ==
    LET
        \* msi_opt.m:4407
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "Data") -> Device_PT_IE_D_Data_456(r, msg, p)
                 [] (msg.mtype = "SnpInv" \/ msg.mtype = "SnpCur" \/ msg.mtype = "SnpData") -> Device_PT_IS_AD_GO_360(r, msg, p)
                 [] OTHER -> Device_PT_IE_D_457(r, msg, p)
    IN step1

Device_P_M_SnpCur_459(r, msg, p) ==
    LET
        \* msi_opt.m:4425
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "Data", msg.src, p, D2H_DATA, r.Procs[p].val, Undefined, Undefined, msg.uqid, 0, 0, Undefined, 0, Undefined, Undefined, Undefined)
        \* msi_opt.m:4428
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "RspVFwdV", msg.src, p, D2H_RSP, Undefined, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step2

Device_P_M_SnpData_460(r, msg, p) ==
    LET
        \* msi_opt.m:4432
        step1 == IF r.error # "" THEN r
                 ELSE IF "P_S" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "P_S"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4432")
        \* msi_opt.m:4433
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "Data", msg.src, p, D2H_DATA, step1.Procs[p].val, Undefined, Undefined, msg.uqid, 0, 0, Undefined, 0, Undefined, Undefined, Undefined)
        \* msi_opt.m:4436
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "RspSFwdM", msg.src, p, D2H_RSP, Undefined, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step3

Device_P_M_SnpInv_461(r, msg, p) ==
    LET
        \* msi_opt.m:4440
        step1 == IF r.error # "" THEN r
                 ELSE IF "P_I" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[p].state = "P_I"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4440")
        \* msi_opt.m:4441
        step2 == IF step1.error # "" THEN step1
                 ELSE Send(step1, "Data", msg.src, p, D2H_DATA, step1.Procs[p].val, Undefined, Undefined, msg.uqid, 0, 0, Undefined, 0, Undefined, Undefined, Undefined)
        \* msi_opt.m:4444
        step3 == IF step2.error # "" THEN step2
                 ELSE Send(step2, "RspIFwdM", msg.src, p, D2H_RSP, Undefined, Undefined, Undefined, msg.uqid, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
        \* msi_opt.m:4448
        step4 == IF step3.error # "" THEN step3
                 ELSE IF Undefined \in (Address) \cup {Undefined} THEN
                    [step3 EXCEPT !.Procs[p].addr = Undefined]
                ELSE Fail(step3, "Type/range error at msi_opt.m:4448")
        \* msi_opt.m:4449
        step5 == IF step4.error # "" THEN step4
                 ELSE IF Undefined \in (Value) \cup {Undefined} THEN
                    [step4 EXCEPT !.Procs[p].val = Undefined]
                ELSE Fail(step4, "Type/range error at msi_opt.m:4449")
    IN step5

Device_P_M_462(r, msg, p) ==
    LET
        \* msi_opt.m:4451
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledMsg(r, msg, p)
    IN step1

Device_P_M_458(r, msg, p) ==
    LET
        \* msi_opt.m:4423
        step1 == IF r.error # "" THEN r
                 ELSE CASE (msg.mtype = "SnpCur") -> Device_P_M_SnpCur_459(r, msg, p)
                 [] (msg.mtype = "SnpData") -> Device_P_M_SnpData_460(r, msg, p)
                 [] (msg.mtype = "SnpInv") -> Device_P_M_SnpInv_461(r, msg, p)
                 [] OTHER -> Device_P_M_462(r, msg, p)
    IN step1

DeviceStep463(r, msg, p) ==
    LET
        \* msi_opt.m:4458
        step1 == IF r.error # "" THEN r
                 ELSE ErrorUnhandledState(r)
    IN step1

DeviceStep355(r, msg, p) ==
    LET
        \* msi_opt.m:3865
        step1 == IF r.error # "" THEN r
                 ELSE CASE (r.Procs[p].state = "P_I") -> Device_P_I_356(r, msg, p)
                 [] (r.Procs[p].state = "PT_IS_AD") -> Device_PT_IS_AD_358(r, msg, p)
                 [] (r.Procs[p].state = "PT_IS_A") -> Device_PT_IS_A_365(r, msg, p)
                 [] (r.Procs[p].state = "PT_IS_D") -> Device_PT_IS_D_370(r, msg, p)
                 [] (r.Procs[p].state = "P_S") -> Device_P_S_373(r, msg, p)
                 [] (r.Procs[p].state = "PT_IM_AD") -> Device_PT_IM_AD_376(r, msg, p)
                 [] (r.Procs[p].state = "PT_IM_D") -> Device_PT_IM_D_381(r, msg, p)
                 [] (r.Procs[p].state = "PT_IM_A") -> Device_PT_IM_A_384(r, msg, p)
                 [] (r.Procs[p].state = "PT_SI_GOI") -> Device_PT_SI_GOI_388(r, msg, p)
                 [] (r.Procs[p].state = "PT_II_D") -> Device_PT_II_D_394(r, msg, p)
                 [] (r.Procs[p].state = "PT_II_GOI") -> Device_PT_II_GOI_397(r, msg, p)
                 [] (r.Procs[p].state = "PT_II_WP") -> Device_PT_II_WP_400(r, msg, p)
                 [] (r.Procs[p].state = "PT_II_GO") -> Device_PT_II_GO_405(r, msg, p)
                 [] (r.Procs[p].state = "PT_II_GP") -> Device_PT_II_GP_409(r, msg, p)
                 [] (r.Procs[p].state = "P_E") -> Device_P_E_414(r, msg, p)
                 [] (r.Procs[p].state = "PT_EI_GOI") -> Device_PT_EI_GOI_419(r, msg, p)
                 [] (r.Procs[p].state = "PT_EI_GP") -> Device_PT_EI_GP_426(r, msg, p)
                 [] (r.Procs[p].state = "PT_MI_GP") -> Device_PT_MI_GP_432(r, msg, p)
                 [] (r.Procs[p].state = "PT_SE_A") -> Device_PT_SE_A_438(r, msg, p)
                 [] (r.Procs[p].state = "PT_SM_GOE") -> Device_PT_SM_GOE_443(r, msg, p)
                 [] (r.Procs[p].state = "PT_IE_AD") -> Device_PT_IE_AD_448(r, msg, p)
                 [] (r.Procs[p].state = "PT_IE_A") -> Device_PT_IE_A_452(r, msg, p)
                 [] (r.Procs[p].state = "PT_IE_D") -> Device_PT_IE_D_455(r, msg, p)
                 [] (r.Procs[p].state = "P_M") -> Device_P_M_458(r, msg, p)
                 [] OTHER -> DeviceStep463(r, msg, p)
    IN step1

DeviceStep354(r, msg, p) ==
    LET
        \* msi_opt.m:3863
        step1 == IF r.error # "" THEN r
                 ELSE DeviceStep355(r, msg, p)
    IN step1

DeviceStep353(r, msg, p) ==
    LET
        \* msi_opt.m:3862
        step1 == IF r.error # "" THEN r
                 ELSE DeviceStep354(r, msg, p)
    IN step1

DeviceStep352(r, msg, p) ==
    LET
        \* msi_opt.m:3859
        step1 == IF r.error # "" THEN r
                 ELSE IF TRUE \in (BOOLEAN) \cup {Undefined} THEN
                    [r EXCEPT !.msg_processed = TRUE]
                ELSE Fail(r, "Type/range error at msi_opt.m:3859")
        \* msi_opt.m:3861
        step2 == IF step1.error # "" THEN step1
                 ELSE DeviceStep353(step1, msg, p)
    IN step2

RuleStep472(r, n, ad, id) ==
    LET
        \* msi_opt.m:4490
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "RdOwn", "Home1", n, D2H_REQ, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep473(r, n, ad, id) ==
    LET
        \* msi_opt.m:4486
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "RdOwn", "Home0", n, D2H_REQ, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep471(r, n, ad, id) ==
    LET
        \* msi_opt.m:4482
        step1 == IF r.error # "" THEN r
                 ELSE IF "PT_IE_AD" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[n].state = "PT_IE_AD"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4482")
        \* msi_opt.m:4483
        step2 == IF step1.error # "" THEN step1
                 ELSE IF ad \in (Address) \cup {Undefined} THEN
                    [step1 EXCEPT !.Procs[n].addr = ad]
                ELSE Fail(step1, "Type/range error at msi_opt.m:4483")
        \* msi_opt.m:4484
        step3 == IF step2.error # "" THEN step2
                 ELSE IF (ad = 0) THEN RuleStep473(step2, n, ad, id)
                ELSE RuleStep472(step2, n, ad, id)
    IN step3

RuleStep475(r, n, ad, id) ==
    LET
        \* msi_opt.m:4506
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "RdAny", "Home1", n, D2H_REQ, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep476(r, n, ad, id) ==
    LET
        \* msi_opt.m:4502
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "RdAny", "Home0", n, D2H_REQ, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep474(r, n, ad, id) ==
    LET
        \* msi_opt.m:4499
        step1 == IF r.error # "" THEN r
                 ELSE IF "PT_IM_AD" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[n].state = "PT_IM_AD"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4499")
        \* msi_opt.m:4500
        step2 == IF step1.error # "" THEN step1
                 ELSE IF ad \in (Address) \cup {Undefined} THEN
                    [step1 EXCEPT !.Procs[n].addr = ad]
                ELSE Fail(step1, "Type/range error at msi_opt.m:4500")
        \* msi_opt.m:4501
        step3 == IF step2.error # "" THEN step2
                 ELSE IF (ad = 0) THEN RuleStep476(step2, n, ad, id)
                ELSE RuleStep475(step2, n, ad, id)
    IN step3

RuleStep478(r, n, ad, id, v) ==
    LET
        \* msi_opt.m:4523
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "WrInv", "Home1", n, D2H_REQ, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep479(r, n, ad, id, v) ==
    LET
        \* msi_opt.m:4519
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "WrInv", "Home0", n, D2H_REQ, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep477(r, n, ad, id, v) ==
    LET
        \* msi_opt.m:4516
        step1 == IF r.error # "" THEN r
                 ELSE IF "PT_II_WP" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[n].state = "PT_II_WP"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4516")
        \* msi_opt.m:4517
        step2 == IF step1.error # "" THEN step1
                 ELSE IF v \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.Procs[n].mem_write_val = v]
                ELSE Fail(step1, "Type/range error at msi_opt.m:4517")
        \* msi_opt.m:4518
        step3 == IF step2.error # "" THEN step2
                 ELSE IF (ad = 0) THEN RuleStep479(step2, n, ad, id, v)
                ELSE RuleStep478(step2, n, ad, id, v)
    IN step3

RuleStep481(r, n, ad, id) ==
    LET
        \* msi_opt.m:4539
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "CleanEvict", "Home1", n, D2H_REQ2, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep482(r, n, ad, id) ==
    LET
        \* msi_opt.m:4535
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "CleanEvict", "Home0", n, D2H_REQ2, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep480(r, n, ad, id) ==
    LET
        \* msi_opt.m:4533
        step1 == IF r.error # "" THEN r
                 ELSE IF "PT_EI_GP" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[n].state = "PT_EI_GP"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4533")
        \* msi_opt.m:4534
        step2 == IF step1.error # "" THEN step1
                 ELSE IF (step1.Procs[n].addr = 0) THEN RuleStep482(step1, n, ad, id)
                ELSE RuleStep481(step1, n, ad, id)
    IN step2

RuleStep484(r, n, ad, id) ==
    LET
        \* msi_opt.m:4554
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "CleanEvictNoData", "Home1", n, D2H_REQ2, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep485(r, n, ad, id) ==
    LET
        \* msi_opt.m:4550
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "CleanEvictNoData", "Home0", n, D2H_REQ2, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep483(r, n, ad, id) ==
    LET
        \* msi_opt.m:4548
        step1 == IF r.error # "" THEN r
                 ELSE IF "PT_EI_GOI" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[n].state = "PT_EI_GOI"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4548")
        \* msi_opt.m:4549
        step2 == IF step1.error # "" THEN step1
                 ELSE IF (step1.Procs[n].addr = 0) THEN RuleStep485(step1, n, ad, id)
                ELSE RuleStep484(step1, n, ad, id)
    IN step2

RuleStep487(r, n, ad, id, v) ==
    LET
        \* msi_opt.m:4574
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "WrCur", "Home1", n, D2H_REQ, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep488(r, n, ad, id, v) ==
    LET
        \* msi_opt.m:4570
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "WrCur", "Home0", n, D2H_REQ, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep486(r, n, ad, id, v) ==
    LET
        \* msi_opt.m:4567
        step1 == IF r.error # "" THEN r
                 ELSE IF "PT_II_GP" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[n].state = "PT_II_GP"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4567")
        \* msi_opt.m:4568
        step2 == IF step1.error # "" THEN step1
                 ELSE IF v \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.Procs[n].mem_write_val = v]
                ELSE Fail(step1, "Type/range error at msi_opt.m:4568")
        \* msi_opt.m:4569
        step3 == IF step2.error # "" THEN step2
                 ELSE IF (ad = 0) THEN RuleStep488(step2, n, ad, id, v)
                ELSE RuleStep487(step2, n, ad, id, v)
    IN step3

RuleStep490(r, n, ad, id, v) ==
    LET
        \* msi_opt.m:4590
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "ItoMWr", "Home1", n, D2H_REQ, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep491(r, n, ad, id, v) ==
    LET
        \* msi_opt.m:4586
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "ItoMWr", "Home0", n, D2H_REQ, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep489(r, n, ad, id, v) ==
    LET
        \* msi_opt.m:4583
        step1 == IF r.error # "" THEN r
                 ELSE IF "PT_II_GP" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[n].state = "PT_II_GP"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4583")
        \* msi_opt.m:4584
        step2 == IF step1.error # "" THEN step1
                 ELSE IF v \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.Procs[n].mem_write_val = v]
                ELSE Fail(step1, "Type/range error at msi_opt.m:4584")
        \* msi_opt.m:4585
        step3 == IF step2.error # "" THEN step2
                 ELSE IF (ad = 0) THEN RuleStep491(step2, n, ad, id, v)
                ELSE RuleStep490(step2, n, ad, id, v)
    IN step3

RuleStep493(r, n, ad, id) ==
    LET
        \* msi_opt.m:4607
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "RdShared", "Home1", n, D2H_REQ, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep494(r, n, ad, id) ==
    LET
        \* msi_opt.m:4603
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "RdShared", "Home0", n, D2H_REQ, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep492(r, n, ad, id) ==
    LET
        \* msi_opt.m:4600
        step1 == IF r.error # "" THEN r
                 ELSE IF "PT_IS_AD" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[n].state = "PT_IS_AD"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4600")
        \* msi_opt.m:4601
        step2 == IF step1.error # "" THEN step1
                 ELSE IF ad \in (Address) \cup {Undefined} THEN
                    [step1 EXCEPT !.Procs[n].addr = ad]
                ELSE Fail(step1, "Type/range error at msi_opt.m:4601")
        \* msi_opt.m:4602
        step3 == IF step2.error # "" THEN step2
                 ELSE IF (ad = 0) THEN RuleStep494(step2, n, ad, id)
                ELSE RuleStep493(step2, n, ad, id)
    IN step3

RuleStep496(r, n, ad, id) ==
    LET
        \* msi_opt.m:4622
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "RdCurr", "Home1", n, D2H_REQ, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep497(r, n, ad, id) ==
    LET
        \* msi_opt.m:4618
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "RdCurr", "Home0", n, D2H_REQ, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep495(r, n, ad, id) ==
    LET
        \* msi_opt.m:4616
        step1 == IF r.error # "" THEN r
                 ELSE IF "PT_II_D" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[n].state = "PT_II_D"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4616")
        \* msi_opt.m:4617
        step2 == IF step1.error # "" THEN step1
                 ELSE IF (ad = 0) THEN RuleStep497(step1, n, ad, id)
                ELSE RuleStep496(step1, n, ad, id)
    IN step2

RuleStep499(r, n, ad, id) ==
    LET
        \* msi_opt.m:4652
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "CleanEvictNoData", "Home1", n, D2H_REQ2, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep500(r, n, ad, id) ==
    LET
        \* msi_opt.m:4648
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "CleanEvictNoData", "Home0", n, D2H_REQ2, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep498(r, n, ad, id) ==
    LET
        \* msi_opt.m:4646
        step1 == IF r.error # "" THEN r
                 ELSE IF "PT_SI_GOI" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[n].state = "PT_SI_GOI"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4646")
        \* msi_opt.m:4647
        step2 == IF step1.error # "" THEN step1
                 ELSE IF (step1.Procs[n].addr = 0) THEN RuleStep500(step1, n, ad, id)
                ELSE RuleStep499(step1, n, ad, id)
    IN step2

RuleStep502(r, n, ad, id) ==
    LET
        \* msi_opt.m:4667
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "RdOwnNoData", "Home1", n, D2H_REQ, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep503(r, n, ad, id) ==
    LET
        \* msi_opt.m:4663
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "RdOwnNoData", "Home0", n, D2H_REQ, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep501(r, n, ad, id) ==
    LET
        \* msi_opt.m:4661
        step1 == IF r.error # "" THEN r
                 ELSE IF "PT_SE_A" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[n].state = "PT_SE_A"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4661")
        \* msi_opt.m:4662
        step2 == IF step1.error # "" THEN step1
                 ELSE IF (step1.Procs[n].addr = 0) THEN RuleStep503(step1, n, ad, id)
                ELSE RuleStep502(step1, n, ad, id)
    IN step2

RuleStep505(r, n, ad, id) ==
    LET
        \* msi_opt.m:4697
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "CLFlush", "Home1", n, D2H_REQ, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep506(r, n, ad, id) ==
    LET
        \* msi_opt.m:4693
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "CLFlush", "Home0", n, D2H_REQ, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep504(r, n, ad, id) ==
    LET
        \* msi_opt.m:4691
        step1 == IF r.error # "" THEN r
                 ELSE IF "PT_II_GOI" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[n].state = "PT_II_GOI"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4691")
        \* msi_opt.m:4692
        step2 == IF step1.error # "" THEN step1
                 ELSE IF (ad = 0) THEN RuleStep506(step1, n, ad, id)
                ELSE RuleStep505(step1, n, ad, id)
    IN step2

RuleStep508(r, n, ad, id) ==
    LET
        \* msi_opt.m:4712
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "CacheFlushed", "Home1", n, D2H_REQ, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep509(r, n, ad, id) ==
    LET
        \* msi_opt.m:4708
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "CacheFlushed", "Home0", n, D2H_REQ, Undefined, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep507(r, n, ad, id) ==
    LET
        \* msi_opt.m:4706
        step1 == IF r.error # "" THEN r
                 ELSE IF "PT_II_GOI" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[n].state = "PT_II_GOI"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4706")
        \* msi_opt.m:4707
        step2 == IF step1.error # "" THEN step1
                 ELSE IF (ad = 0) THEN RuleStep509(step1, n, ad, id)
                ELSE RuleStep508(step1, n, ad, id)
    IN step2

RuleStep511(r, n, ad, id) ==
    LET
        \* msi_opt.m:4727
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "DirtyEvict", "Home1", n, D2H_REQ2, r.Procs[n].val, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep512(r, n, ad, id) ==
    LET
        \* msi_opt.m:4723
        step1 == IF r.error # "" THEN r
                 ELSE Send(r, "DirtyEvict", "Home0", n, D2H_REQ2, r.Procs[n].val, ad, id, Undefined, 0, Undefined, Undefined, Undefined, Undefined, Undefined, Undefined)
    IN step1

RuleStep510(r, n, ad, id) ==
    LET
        \* msi_opt.m:4721
        step1 == IF r.error # "" THEN r
                 ELSE IF "PT_MI_GP" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[n].state = "PT_MI_GP"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4721")
        \* msi_opt.m:4722
        step2 == IF step1.error # "" THEN step1
                 ELSE IF (step1.Procs[n].addr = 0) THEN RuleStep512(step1, n, ad, id)
                ELSE RuleStep511(step1, n, ad, id)
    IN step2

RuleStep514(r, n, ad, v) ==
    LET
        \* msi_opt.m:4744
        step1 == IF r.error # "" THEN r
                 ELSE IF v \in (Value) \cup {Undefined} THEN
                    [r EXCEPT !.LastWrites[1] = v]
                ELSE Fail(r, "Type/range error at msi_opt.m:4744")
    IN step1

RuleStep515(r, n, ad, v) ==
    LET
        \* msi_opt.m:4742
        step1 == IF r.error # "" THEN r
                 ELSE IF v \in (Value) \cup {Undefined} THEN
                    [r EXCEPT !.LastWrites[0] = v]
                ELSE Fail(r, "Type/range error at msi_opt.m:4742")
    IN step1

RuleStep513(r, n, ad, v) ==
    LET
        \* msi_opt.m:4739
        step1 == IF r.error # "" THEN r
                 ELSE IF "P_M" \in (ProcStates) \cup {Undefined} THEN
                    [r EXCEPT !.Procs[n].state = "P_M"]
                ELSE Fail(r, "Type/range error at msi_opt.m:4739")
        \* msi_opt.m:4740
        step2 == IF step1.error # "" THEN step1
                 ELSE IF v \in (Value) \cup {Undefined} THEN
                    [step1 EXCEPT !.Procs[n].val = v]
                ELSE Fail(step1, "Type/range error at msi_opt.m:4740")
        \* msi_opt.m:4741
        step3 == IF step2.error # "" THEN step2
                 ELSE IF (step2.Procs[n].addr = 0) THEN RuleStep515(step2, n, ad, v)
                ELSE RuleStep514(step2, n, ad, v)
    IN step3

SendInvReqToSharers(r, rqst, h, msg) == InvalidateStep464(r, rqst, h, msg)

HomeReceive(r, msg, h) == HomeStep1(r, msg, h)
ProcReceive(r, msg, p) == DeviceStep352(r, msg, p)

Receive(r, msg, n) ==
    IF n \in Home THEN HomeReceive(r, msg, n) ELSE ProcReceive(r, msg, n)
Commit(r) ==
    /\ HomeNodes' = r.HomeNodes /\ Procs' = r.Procs /\ Net' = r.Net
    /\ InBox' = r.InBox /\ msg_processed' = r.msg_processed
    /\ LastWrites' = r.LastWrites /\ error' = r.error

DeliverNetwork(n, msg) ==
    /\ error = ""
    /\ BagIn(msg, Net[n])
    /\ InBox[n][msg.vc] = Undefined
    /\ LET r == Receive(Snapshot, msg, n)
           consumed == [r EXCEPT !.Net[n] = (@ (-) SetToBag({msg}))]
           result == IF r.msg_processed THEN consumed
                     ELSE [consumed EXCEPT !.InBox[n][msg.vc] = msg]
       IN Commit(result)
DeliverBlocked(n, vc) ==
    /\ error = ""
    /\ InBox[n][vc] # Undefined
    /\ LET r == Receive(Snapshot, InBox[n][vc], n)
           result == IF r.msg_processed THEN [r EXCEPT !.InBox[n][vc] = Undefined] ELSE r
       IN Commit(result)

\* The six CXL.cache directions plus the source's separate eviction lane.
\* Channel filters select delivery; opcodes retain the source's VC choices,
\* including questionable choices, without repairing the protocol.
DeliverChannel(vc) ==
    \/ \E n \in Node: \E msg \in DOMAIN Net[n]: msg.vc = vc /\ DeliverNetwork(n, msg)
    \/ \E n \in Node: DeliverBlocked(n, vc)
DeviceToHomeRequest == DeliverChannel(D2H_REQ)
HomeToDeviceRequest == DeliverChannel(H2D_REQ)
DeviceToHomeData == DeliverChannel(D2H_DATA)
DeviceToHomeResponse == DeliverChannel(D2H_RSP)
HomeToDeviceData == DeliverChannel(H2D_DATA)
HomeToDeviceResponse == DeliverChannel(H2D_RSP)
DeviceToHomeEviction == DeliverChannel(D2H_REQ2)

\* msi_opt.m:4479: "device in state I, send RdOwn"
DeviceRule1(n, ad, id) ==
    /\ error = ""
    /\ (Snapshot.Procs[n].state = "P_I")
    /\ Commit(RuleStep471(Snapshot, n, ad, id))

\* msi_opt.m:4496: "device in state I, send RdAny"
DeviceRule2(n, ad, id) ==
    /\ error = ""
    /\ (Snapshot.Procs[n].state = "P_I")
    /\ Commit(RuleStep474(Snapshot, n, ad, id))

\* msi_opt.m:4513: "device in state I, send WrInv"
DeviceRule3(n, ad, id, v) ==
    /\ error = ""
    /\ (Snapshot.Procs[n].state = "P_I")
    /\ Commit(RuleStep477(Snapshot, n, ad, id, v))

\* msi_opt.m:4530: "device in state E, send CleanEvict"
DeviceRule4(n, ad, id) ==
    /\ error = ""
    /\ (Snapshot.Procs[n].state = "P_E")
    /\ Commit(RuleStep480(Snapshot, n, ad, id))

\* msi_opt.m:4545: "device in state E, send CleanEvictNoData"
DeviceRule5(n, ad, id) ==
    /\ error = ""
    /\ (Snapshot.Procs[n].state = "P_E")
    /\ Commit(RuleStep483(Snapshot, n, ad, id))

\* msi_opt.m:4564: "device in state I, send WrCur"
DeviceRule6(n, ad, id, v) ==
    /\ error = ""
    /\ ((Snapshot.Procs[n].state = "P_I"))
    /\ Commit(RuleStep486(Snapshot, n, ad, id, v))

\* msi_opt.m:4580: "device in state I, send ItoMWr"
DeviceRule7(n, ad, id, v) ==
    /\ error = ""
    /\ ((Snapshot.Procs[n].state = "P_I"))
    /\ Commit(RuleStep489(Snapshot, n, ad, id, v))

\* msi_opt.m:4597: "device in state I, send RdShared"
DeviceRule8(n, ad, id) ==
    /\ error = ""
    /\ ((Snapshot.Procs[n].state = "P_I"))
    /\ Commit(RuleStep492(Snapshot, n, ad, id))

\* msi_opt.m:4613: "device in state I, send RdCurr"
DeviceRule9(n, ad, id) ==
    /\ error = ""
    /\ ((Snapshot.Procs[n].state = "P_I"))
    /\ Commit(RuleStep495(Snapshot, n, ad, id))

\* msi_opt.m:4643: "device in state S, send CleanEvictNoData"
DeviceRule10(n, ad, id) ==
    /\ error = ""
    /\ ((Snapshot.Procs[n].state = "P_S"))
    /\ Commit(RuleStep498(Snapshot, n, ad, id))

\* msi_opt.m:4658: "device in state S, send RdOwnNoData"
DeviceRule11(n, ad, id) ==
    /\ error = ""
    /\ ((Snapshot.Procs[n].state = "P_S"))
    /\ Commit(RuleStep501(Snapshot, n, ad, id))

\* msi_opt.m:4688: "device in state I, send CLFlush"
DeviceRule12(n, ad, id) ==
    /\ error = ""
    /\ ((Snapshot.Procs[n].state = "P_I"))
    /\ Commit(RuleStep504(Snapshot, n, ad, id))

\* msi_opt.m:4703: "device in state I, send CacheFlushed"
DeviceRule13(n, ad, id) ==
    /\ error = ""
    /\ (((Snapshot.Procs[n].state = "P_I")) /\ ((Snapshot.Procs[n].val = Undefined)))
    /\ Commit(RuleStep507(Snapshot, n, ad, id))

\* msi_opt.m:4718: "device in state M, send DirtyEvict"
DeviceRule14(n, ad, id) ==
    /\ error = ""
    /\ ((Snapshot.Procs[n].state = "P_M"))
    /\ Commit(RuleStep510(Snapshot, n, ad, id))

\* msi_opt.m:4736: "device in state E, store data"
DeviceRule15(n, ad, v) ==
    /\ error = ""
    /\ (Snapshot.Procs[n].state = "P_E")
    /\ Commit(RuleStep513(Snapshot, n, ad, v))

Init ==
    /\ HomeNodes = [h \in Home |->
        [state |-> "H_I", owner |-> Undefined, sharers |-> {}, val |-> 0,
         requester |-> Undefined, request_type |-> Undefined, request_pre |-> Undefined,
         snp_data_sent |-> Undefined, snp_cur_sent |-> Undefined, flag |-> Undefined]]
    /\ Procs = [p \in Proc |-> [state |-> "P_I", val |-> Undefined,
                               addr |-> Undefined, mem_write_val |-> Undefined]]
    /\ LastWrites = [ad \in Address |-> 0]
    /\ Net = [n \in Node |-> EmptyBag]
    /\ InBox = [n \in Node |-> [vc \in VCType |-> Undefined]]
    /\ msg_processed = Undefined
    /\ error = ""

Next ==
    \/ \E n \in Proc, ad \in Address, id \in UQIDType: DeviceRule1(n, ad, id)
    \/ \E n \in Proc, ad \in Address, id \in UQIDType: DeviceRule2(n, ad, id)
    \/ \E n \in Proc, ad \in Address, id \in UQIDType, v \in Value: DeviceRule3(n, ad, id, v)
    \/ \E n \in Proc, ad \in Address, id \in UQIDType: DeviceRule4(n, ad, id)
    \/ \E n \in Proc, ad \in Address, id \in UQIDType: DeviceRule5(n, ad, id)
    \/ \E n \in Proc, ad \in Address, id \in UQIDType, v \in Value: DeviceRule6(n, ad, id, v)
    \/ \E n \in Proc, ad \in Address, id \in UQIDType, v \in Value: DeviceRule7(n, ad, id, v)
    \/ \E n \in Proc, ad \in Address, id \in UQIDType: DeviceRule8(n, ad, id)
    \/ \E n \in Proc, ad \in Address, id \in UQIDType: DeviceRule9(n, ad, id)
    \/ \E n \in Proc, ad \in Address, id \in UQIDType: DeviceRule10(n, ad, id)
    \/ \E n \in Proc, ad \in Address, id \in UQIDType: DeviceRule11(n, ad, id)
    \/ \E n \in Proc, ad \in Address, id \in UQIDType: DeviceRule12(n, ad, id)
    \/ \E n \in Proc, ad \in Address, id \in UQIDType: DeviceRule13(n, ad, id)
    \/ \E n \in Proc, ad \in Address, id \in UQIDType: DeviceRule14(n, ad, id)
    \/ \E n \in Proc, ad \in Address, v \in Value: DeviceRule15(n, ad, v)
    \/ DeviceToHomeRequest \/ HomeToDeviceRequest
    \/ DeviceToHomeData \/ DeviceToHomeResponse
    \/ HomeToDeviceData \/ HomeToDeviceResponse \/ DeviceToHomeEviction

Spec == Init /\ [][Next]_vars
TypeOK ==
    /\ HomeNodes \in [Home -> HomeRecord]
    /\ \A h \in Home : Cardinality(HomeNodes[h].sharers) <= ProcCount
    /\ Procs \in [Proc -> ProcRecord]
    /\ DOMAIN Net = Node
    /\ \A n \in Node : /\ IsABag(Net[n]) /\ DOMAIN Net[n] \subseteq MessageSet
                        /\ BagCardinality(Net[n]) <= NetMax
    /\ InBox \in [Node -> [VCType -> MessageSet \cup {Undefined}]]
    /\ msg_processed \in WithUndefined(BOOLEAN)
    /\ LastWrites \in [Address -> WithUndefined(Value)]
    /\ error \in STRING
NoErrors == error = ""

\* Source invariant: "Invalid implies empty owner"
InvalidImpliesEmptyOwner ==
    (\A h \in Home : ((Snapshot.HomeNodes[h].state = "H_I") => (Snapshot.HomeNodes[h].owner = Undefined)))

\* Source invariant: "value in addr0 matches value of last write, when invalid"
Address0MemoryMatchesLastWrite ==
    (((Snapshot.HomeNodes["Home0"].state = "H_I") \/ (Snapshot.HomeNodes["Home0"].state = "H_S")) => (Snapshot.HomeNodes["Home0"].val = Snapshot.LastWrites[0]))

\* Source invariant: "value in addr1 matches value of last write, when invalid"
Address1MemoryMatchesLastWrite ==
    (((Snapshot.HomeNodes["Home1"].state = "H_I") \/ (Snapshot.HomeNodes["Home1"].state = "H_S")) => (Snapshot.HomeNodes["Home1"].val = Snapshot.LastWrites[1]))

\* Source invariant: "modified implies empty sharers list"
ModifiedImpliesNoSharers ==
    (\A h \in Home : ((Snapshot.HomeNodes[h].state = "H_M") => (Cardinality(Snapshot.HomeNodes[h].sharers) = 0)))

\* Source invariant: "Invalid implies empty sharer list"
InvalidImpliesNoSharers ==
    (\A h \in Home : ((Snapshot.HomeNodes[h].state = "H_I") => (Cardinality(Snapshot.HomeNodes[h].sharers) = 0)))

\* Source invariant: "addr 0 values in shared state match memory"
Address0SharedValuesMatchMemory ==
    (\A n \in Proc : ((((Snapshot.HomeNodes["Home0"].state = "H_S") /\ (Snapshot.Procs[n].state = "P_S")) /\ (Snapshot.Procs[n].addr = 0)) => (Snapshot.HomeNodes["Home0"].val = Snapshot.Procs[n].val)))

\* Source invariant: "addr 1 values in shared state match memory"
Address1SharedValuesMatchMemory ==
    (\A n \in Proc : ((((Snapshot.HomeNodes["Home1"].state = "H_S") /\ (Snapshot.Procs[n].state = "P_S")) /\ (Snapshot.Procs[n].addr = 1)) => (Snapshot.HomeNodes["Home1"].val = Snapshot.Procs[n].val)))

=============================================================================
