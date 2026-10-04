------------------------- MODULE msi_opt_checks -------------------------
EXTENDS msi_opt

\* Focused translation checks. These test representation and atomic procedure
\* semantics independently of the source's unresolved coherence properties.
TestMessage(t, src, vc) ==
    [valid |-> 1, mtype |-> t, src |-> src, vc |-> vc, val |-> 0,
     addr |-> 0, cqid |-> "UQID0", uqid |-> "UQID0", nt |-> 0,
     chunkvalid |-> 0, poison |-> 0, bogus |-> 0, go_err |-> 0,
     rspdata |-> "E", rsp_pre |-> 1]
Push(r, dst, m) ==
    Send(r, m.mtype, dst, m.src, m.vc, m.val, m.addr, m.cqid, m.uqid,
         m.nt, m.chunkvalid, m.poison, m.bogus, m.go_err, m.rspdata, m.rsp_pre)

DuplicateMessagesPreserved ==
    LET m == TestMessage("RdOwn", "Proc0", D2H_REQ)
        twice == Push(Push(Snapshot, Home0, m), Home0, m)
        remaining == twice.Net[Home0] (-) SetToBag({m})
    IN /\ twice.error = ""
       /\ CopiesIn(m, twice.Net[Home0]) = 2
       /\ CopiesIn(m, remaining) = 1

CapacityCheckedOnEachSend ==
    LET m == TestMessage("RdOwn", "Proc0", D2H_REQ)
        almostFull == [Snapshot EXCEPT !.Net[Home0] = [x \in {m} |-> NetMax-1]]
        full == Push(almostFull, Home0, m)
        overflow == Push(full, Home0, m)
    IN /\ full.error = ""
       /\ BagCardinality(full.Net[Home0]) = NetMax
       /\ overflow.error = "Too many messages"
       /\ overflow.Net = full.Net

DataAndGOCanArriveInEitherOrder ==
    LET acquiring == [Snapshot EXCEPT !.Procs["Proc0"].state = "PT_IE_AD",
                                      !.Procs["Proc0"].addr = 0]
        data == TestMessage("Data", Home0, H2D_DATA)
        go == TestMessage("GO", Home0, H2D_RSP)
        dataFirst == ProcReceive(ProcReceive(acquiring, data, "Proc0"), go, "Proc0")
        goFirst == ProcReceive(ProcReceive(acquiring, go, "Proc0"), data, "Proc0")
    IN /\ dataFirst.error = "" /\ goFirst.error = ""
       /\ dataFirst.Procs["Proc0"].state = "P_E"
       /\ goFirst.Procs["Proc0"].state = "P_E"
       /\ dataFirst.Procs["Proc0"].val = 0
       /\ goFirst.Procs["Proc0"].val = 0

BusyReceiverStalls ==
    LET acquiring == [Snapshot EXCEPT !.Procs["Proc0"].state = "PT_IE_AD"]
        stalled == ProcReceive(acquiring, TestMessage("SnpInv", Home0, H2D_REQ), "Proc0")
    IN /\ stalled.error = "" /\ ~stalled.msg_processed
       /\ stalled.Procs = acquiring.Procs /\ stalled.Net = acquiring.Net

InvalidationsRemoveSharersAndSkipRequester ==
    LET shared == [Snapshot EXCEPT !.HomeNodes[Home0].sharers = {"Proc0", "Proc1"}]
        result == SendInvReqToSharers(shared, "Proc0", Home0,
                                      TestMessage("RdOwn", "Proc0", D2H_REQ))
        messages == DOMAIN result.Net["Proc1"]
    IN /\ result.error = "" /\ result.HomeNodes[Home0].sharers = {}
       /\ result.Net["Proc0"] = EmptyBag
       /\ BagCardinality(result.Net["Proc1"]) = 1
       /\ \A m \in messages : m.mtype = "SnpInv" /\ m.vc = H2D_REQ
                              /\ m.addr = 0 /\ m.uqid = "UQID0"

SourceUnhandledMessageRemainsAnError ==
    LET modified == [Snapshot EXCEPT !.HomeNodes[Home0].state = "H_M",
                                     !.HomeNodes[Home0].owner = "Proc0"]
        result == HomeReceive(modified, TestMessage("CleanEvictNoData", "Proc0", D2H_REQ2), Home0)
    IN result.error # ""

SourceAssertionRemainsAnError ==
    LET invalidOwner == [Snapshot EXCEPT !.HomeNodes[Home0].state = "H_M"]
        result == HomeReceive(invalidOwner, TestMessage("RdOwn", "Proc0", D2H_REQ), Home0)
    IN /\ result.error # "" /\ result.Net = invalidOwner.Net

TranslationChecks ==
    /\ DuplicateMessagesPreserved
    /\ CapacityCheckedOnEachSend
    /\ DataAndGOCanArriveInEitherOrder
    /\ BusyReceiverStalls
    /\ InvalidationsRemoveSharersAndSkipRequester
    /\ SourceUnhandledMessageRemainsAnError
    /\ SourceAssertionRemainsAnError
CheckNext == UNCHANGED vars
=============================================================================
