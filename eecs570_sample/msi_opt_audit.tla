-------------------------- MODULE msi_opt_audit --------------------------
EXTENDS msi_opt
CONSTANT Scenario
VARIABLE step
auditVars == <<vars, step>>
AuditInit == Init /\ step = 0
At(i, A) == step = i /\ A /\ step' = i+1
ReceiveOpcode(n, opcode) ==
    \E m \in DOMAIN Net[n]: m.mtype = opcode /\ DeliverNetwork(n, m)
ReceiveGO(n, grant) ==
    \E m \in DOMAIN Net[n]:
        m.mtype = "GO" /\ m.rspdata = grant /\ DeliverNetwork(n, m)
ResponseQueued(opcode) == \E m \in DOMAIN Net[Home0]: m.mtype = opcode
\* Real executions from Init, followed by every possible drain interleaving.
\* EventualDone prevents a disabled scheduled action from passing vacuously.

Trace_ids ==
    \/ At(0, DeviceRule1("Proc0", 0, "UQID0"))
    \/ At(1, ReceiveOpcode(Home0, "RdOwn"))

Trace_rdshared ==
    \/ At(0, DeviceRule8("Proc0", 0, "UQID0"))
    \/ At(1, ReceiveOpcode(Home0, "RdShared"))
    \/ At(2, ReceiveOpcode("Proc0", "Data"))
    \/ At(3, ReceiveGO("Proc0", "S"))

Trace_rdany_clean ==
    \/ At(0, DeviceRule2("Proc0", 0, "UQID0"))
    \/ At(1, ReceiveOpcode(Home0, "RdAny"))
    \/ At(2, ReceiveGO("Proc0", "E"))
    \/ At(3, ReceiveOpcode("Proc0", "Data"))

Trace_address ==
    \/ At(0, DeviceRule1("Proc0", 0, "UQID0"))
    \/ At(1, ReceiveOpcode(Home0, "RdOwn"))
    \/ At(2, ReceiveGO("Proc0", "E"))
    \/ At(3, ReceiveOpcode("Proc0", "Data"))
    \/ At(4, DeviceRule5("Proc0", 1, "UQID0"))

Trace_rdany_shared ==
    \/ At(0, DeviceRule1("Proc0", 0, "UQID0"))
    \/ At(1, ReceiveOpcode(Home0, "RdOwn"))
    \/ At(2, ReceiveGO("Proc0", "E"))
    \/ At(3, ReceiveOpcode("Proc0", "Data"))
    \/ At(4, DeviceRule2("Proc1", 0, "UQID0"))
    \/ At(5, ReceiveOpcode(Home0, "RdAny"))
    \/ At(6, ReceiveOpcode("Proc0", "SnpData"))
    \/ At(7, ReceiveOpcode(Home0, "RspSHitSE"))
    \/ At(8, ReceiveGO("Proc1", "S"))
    \/ At(9, ReceiveOpcode("Proc1", "Data"))

Trace_history ==
    \/ At(0, DeviceRule1("Proc0", 0, "UQID0"))
    \/ At(1, ReceiveOpcode(Home0, "RdOwn"))
    \/ At(2, ReceiveGO("Proc0", "E"))
    \/ At(3, ReceiveOpcode("Proc0", "Data"))
    \/ At(4, DeviceRule8("Proc1", 0, "UQID0"))
    \/ At(5, ReceiveOpcode(Home0, "RdShared"))
    \/ At(6, ReceiveOpcode("Proc0", "SnpData"))
    \/ At(7, DeviceRule10("Proc0", 0, "UQID0"))
    \/ At(8, ReceiveOpcode(Home0, "RspSHitSE"))
    \/ At(9, ReceiveOpcode(Home0, "CleanEvictNoData"))
    \/ At(10, ReceiveGO("Proc0", "I"))
    \/ At(11, ReceiveGO("Proc1", "S"))
    \/ At(12, ReceiveOpcode("Proc1", "Data"))

Trace_dirty_snoop ==
    \/ At(0, DeviceRule1("Proc0", 0, "UQID0"))
    \/ At(1, ReceiveOpcode(Home0, "RdOwn"))
    \/ At(2, ReceiveGO("Proc0", "E"))
    \/ At(3, ReceiveOpcode("Proc0", "Data"))
    \/ At(4, DeviceRule15("Proc0", 0, 1))
    \/ At(5, DeviceRule1("Proc1", 0, "UQID0"))
    \/ At(6, ReceiveOpcode(Home0, "RdOwn"))
    \/ At(7, DeviceRule14("Proc0", 0, "UQID0"))
    \/ At(8, ReceiveOpcode("Proc0", "SnpInv"))

Trace_clean_snoop ==
    \/ At(0, DeviceRule1("Proc0", 0, "UQID0"))
    \/ At(1, ReceiveOpcode(Home0, "RdOwn"))
    \/ At(2, ReceiveGO("Proc0", "E"))
    \/ At(3, ReceiveOpcode("Proc0", "Data"))
    \/ At(4, DeviceRule4("Proc0", 0, "UQID0"))
    \/ At(5, DeviceRule1("Proc1", 0, "UQID0"))
    \/ At(6, ReceiveOpcode(Home0, "RdOwn"))
    \/ At(7, ReceiveOpcode("Proc0", "SnpInv"))

Trace_first_ack ==
    \/ At(0, DeviceRule1("Proc0", 0, "UQID0"))
    \/ At(1, ReceiveOpcode(Home0, "RdOwn"))
    \/ At(2, ReceiveGO("Proc0", "E"))
    \/ At(3, ReceiveOpcode("Proc0", "Data"))
    \/ At(4, DeviceRule8("Proc1", 0, "UQID0"))
    \/ At(5, ReceiveOpcode(Home0, "RdShared"))
    \/ At(6, ReceiveOpcode("Proc0", "SnpData"))
    \/ At(7, ReceiveOpcode(Home0, "RspSHitSE"))
    \/ At(8, ReceiveGO("Proc1", "S"))
    \/ At(9, ReceiveOpcode("Proc1", "Data"))
    \/ At(10, DeviceRule8("Proc2", 0, "UQID0"))
    \/ At(11, ReceiveOpcode(Home0, "RdShared"))
    \/ At(12, ReceiveGO("Proc2", "S"))
    \/ At(13, ReceiveOpcode("Proc2", "Data"))
    \/ At(14, DeviceRule11("Proc0", 1, "UQID0"))
    \/ At(15, ReceiveOpcode(Home0, "RdOwnNoData"))
    \/ At(16, ReceiveOpcode("Proc1", "SnpInv"))
    \/ At(17, ReceiveOpcode(Home0, "RspIHitSE"))
    \/ At(18, ReceiveOpcode("Proc2", "SnpInv"))
    \/ At(19, ReceiveOpcode(Home0, "RspIHitSE"))
    \/ At(20, ReceiveGO("Proc0", "E"))

Trace_stale_read ==
    \/ At(0, DeviceRule1("Proc0", 0, "UQID0"))
    \/ At(1, ReceiveOpcode(Home0, "RdOwn"))
    \/ At(2, ReceiveGO("Proc0", "E"))
    \/ At(3, ReceiveOpcode("Proc0", "Data"))
    \/ At(4, DeviceRule8("Proc1", 0, "UQID0"))
    \/ At(5, ReceiveOpcode(Home0, "RdShared"))
    \/ At(6, ReceiveOpcode("Proc0", "SnpData"))
    \/ At(7, ReceiveOpcode(Home0, "RspSHitSE"))
    \/ At(8, ReceiveGO("Proc1", "S"))
    \/ At(9, ReceiveOpcode("Proc1", "Data"))
    \/ At(10, DeviceRule8("Proc2", 0, "UQID0"))
    \/ At(11, ReceiveOpcode(Home0, "RdShared"))
    \/ At(12, ReceiveGO("Proc2", "S"))
    \/ At(13, ReceiveOpcode("Proc2", "Data"))
    \/ At(14, DeviceRule11("Proc0", 1, "UQID0"))
    \/ At(15, ReceiveOpcode(Home0, "RdOwnNoData"))
    \/ At(16, ReceiveOpcode("Proc1", "SnpInv"))
    \/ At(17, ReceiveOpcode(Home0, "RspIHitSE"))
    \/ At(18, ReceiveOpcode("Proc2", "SnpInv"))
    \/ At(19, ReceiveOpcode(Home0, "RspIHitSE"))
    \/ At(20, ReceiveGO("Proc0", "E"))
    \/ At(21, DeviceRule15("Proc0", 0, 1))

Trace_cacheflushed_channel ==
    \/ At(0, DeviceRule2("Proc0", 0, "UQID0"))
    \/ At(1, ReceiveOpcode(Home0, "RdAny"))
    \/ At(2, ReceiveGO("Proc0", "E"))
    \/ At(3, ReceiveOpcode("Proc0", "Data"))
    \/ At(4, DeviceRule13("Proc1", 1, "UQID0"))
    \/ At(5, ReceiveOpcode(Home0, "CacheFlushed"))

Trace_handoff ==
    \/ At(0, DeviceRule2("Proc1", 0, "UQID0"))
    \/ At(1, ReceiveOpcode(Home0, "RdAny"))
    \/ At(2, ReceiveGO("Proc1", "E"))
    \/ At(3, ReceiveOpcode("Proc1", "Data"))
    \/ At(4, DeviceRule15("Proc1", 0, 1))
    \/ At(5, DeviceRule1("Proc0", 0, "UQID0"))
    \/ At(6, ReceiveOpcode(Home0, "RdOwn"))
    \/ At(7, ReceiveOpcode("Proc1", "SnpInv"))
    \/ At(8, ReceiveOpcode(Home0, "Data"))
    \/ At(9, ReceiveOpcode(Home0, "RspIFwdM"))
    \/ At(10, ReceiveOpcode("Proc0", "Data"))
    \/ At(11, ReceiveGO("Proc0", "E"))
    \/ At(12, DeviceRule4("Proc0", 0, "UQID0"))
    \/ At(13, ReceiveOpcode(Home0, "CleanEvict"))
    \/ At(14, ReceiveOpcode("Proc0", "GO_WritePull"))
    \/ At(15, ReceiveOpcode(Home0, "Data"))

Trace_handoff_response_first ==
    \/ At(0, DeviceRule2("Proc1", 0, "UQID0"))
    \/ At(1, ReceiveOpcode(Home0, "RdAny"))
    \/ At(2, ReceiveGO("Proc1", "E"))
    \/ At(3, ReceiveOpcode("Proc1", "Data"))
    \/ At(4, DeviceRule15("Proc1", 0, 1))
    \/ At(5, DeviceRule1("Proc0", 0, "UQID0"))
    \/ At(6, ReceiveOpcode(Home0, "RdOwn"))
    \/ At(7, ReceiveOpcode("Proc1", "SnpInv"))
    \/ At(8, ReceiveOpcode(Home0, "RspIFwdM"))
    \/ At(9, ReceiveOpcode(Home0, "Data"))
    \/ At(10, ReceiveOpcode("Proc0", "Data"))
    \/ At(11, ReceiveGO("Proc0", "E"))
    \/ At(12, DeviceRule4("Proc0", 0, "UQID0"))
    \/ At(13, ReceiveOpcode(Home0, "CleanEvict"))
    \/ At(14, ReceiveOpcode("Proc0", "GO_WritePull"))
    \/ At(15, ReceiveOpcode(Home0, "Data"))

Trace_bogus ==
    \/ At(0, DeviceRule1("Proc0", 0, "UQID0"))
    \/ At(1, ReceiveOpcode(Home0, "RdOwn"))
    \/ At(2, ReceiveGO("Proc0", "E"))
    \/ At(3, ReceiveOpcode("Proc0", "Data"))
    \/ At(4, DeviceRule15("Proc0", 0, 1))
    \/ At(5, DeviceRule1("Proc1", 0, "UQID0"))
    \/ At(6, ReceiveOpcode(Home0, "RdOwn"))
    \/ At(7, DeviceRule14("Proc0", 0, "UQID0"))
    \/ At(8, ReceiveOpcode("Proc0", "SnpInv"))
    \/ At(9, ReceiveOpcode(Home0, "RspIFwdM"))
    \/ At(10, ReceiveOpcode(Home0, "Data"))
    \/ At(11, ReceiveGO("Proc1", "E"))
    \/ At(12, ReceiveOpcode("Proc1", "Data"))
    \/ At(13, DeviceRule15("Proc1", 0, 0))
    \/ At(14, ReceiveOpcode(Home0, "DirtyEvict"))
    \/ At(15, ReceiveOpcode("Proc0", "GO_WritePull"))
    \/ At(16, ReceiveOpcode(Home0, "Data"))

Trace_dirty_cur ==
    \/ At(0, DeviceRule1("Proc0", 0, "UQID0"))
    \/ At(1, ReceiveOpcode(Home0, "RdOwn"))
    \/ At(2, ReceiveGO("Proc0", "E"))
    \/ At(3, ReceiveOpcode("Proc0", "Data"))
    \/ At(4, DeviceRule15("Proc0", 0, 1))
    \/ At(5, DeviceRule9("Proc1", 0, "UQID0"))
    \/ At(6, ReceiveOpcode(Home0, "RdCurr"))
    \/ At(7, DeviceRule14("Proc0", 0, "UQID0"))
    \/ At(8, ReceiveOpcode("Proc0", "SnpCur"))

Trace_rdcurr_dirty ==
    \/ At(0, DeviceRule1("Proc0", 0, "UQID0"))
    \/ At(1, ReceiveOpcode(Home0, "RdOwn"))
    \/ At(2, ReceiveGO("Proc0", "E"))
    \/ At(3, ReceiveOpcode("Proc0", "Data"))
    \/ At(4, DeviceRule15("Proc0", 0, 1))
    \/ At(5, DeviceRule9("Proc1", 0, "UQID0"))
    \/ At(6, ReceiveOpcode(Home0, "RdCurr"))
    \/ At(7, ReceiveOpcode("Proc0", "SnpCur"))
    \/ At(8, ReceiveOpcode(Home0, "Data"))
    \/ At(9, ReceiveOpcode(Home0, "RspVFwdV"))
    \/ At(10, ReceiveOpcode("Proc1", "Data"))

Trace_flush_dirty ==
    \/ At(0, DeviceRule1("Proc0", 0, "UQID0"))
    \/ At(1, ReceiveOpcode(Home0, "RdOwn"))
    \/ At(2, ReceiveGO("Proc0", "E"))
    \/ At(3, ReceiveOpcode("Proc0", "Data"))
    \/ At(4, DeviceRule15("Proc0", 0, 1))
    \/ At(5, DeviceRule12("Proc1", 0, "UQID0"))
    \/ At(6, ReceiveOpcode(Home0, "CLFlush"))
    \/ At(7, ReceiveOpcode("Proc0", "SnpInv"))
    \/ At(8, ReceiveOpcode(Home0, "RspIFwdM"))
    \/ At(9, ReceiveOpcode(Home0, "Data"))
    \/ At(10, ReceiveGO("Proc1", "I"))

Trace_wrinv ==
    \/ At(0, DeviceRule3("Proc0", 0, "UQID0", 1))
    \/ At(1, ReceiveOpcode(Home0, "WrInv"))
    \/ At(2, ReceiveOpcode("Proc0", "WritePull"))
    \/ At(3, ReceiveOpcode(Home0, "Data"))
    \/ At(4, ReceiveGO("Proc0", "I"))

Trace_wrcur ==
    \/ At(0, DeviceRule6("Proc0", 0, "UQID0", 1))
    \/ At(1, ReceiveOpcode(Home0, "WrCur"))
    \/ At(2, ReceiveOpcode("Proc0", "GO_WritePull"))
    \/ At(3, ReceiveOpcode(Home0, "Data"))

Trace_itomwr ==
    \/ At(0, DeviceRule7("Proc0", 0, "UQID0", 1))
    \/ At(1, ReceiveOpcode(Home0, "ItoMWr"))
    \/ At(2, ReceiveOpcode("Proc0", "GO_WritePull"))
    \/ At(3, ReceiveOpcode(Home0, "Data"))

Trace_own_nodata ==
    \/ At(0, DeviceRule11("Proc0", 0, "UQID0"))
    \/ At(1, ReceiveOpcode(Home0, "RdOwnNoData"))
    \/ At(2, ReceiveGO("Proc0", "E"))
    \/ At(3, DeviceRule15("Proc0", 0, 1))

Trace_clean_nodata_snoop ==
    \/ At(0, DeviceRule1("Proc0", 0, "UQID0"))
    \/ At(1, ReceiveOpcode(Home0, "RdOwn"))
    \/ At(2, ReceiveGO("Proc0", "E"))
    \/ At(3, ReceiveOpcode("Proc0", "Data"))
    \/ At(4, DeviceRule5("Proc0", 0, "UQID0"))
    \/ At(5, DeviceRule1("Proc1", 0, "UQID0"))
    \/ At(6, ReceiveOpcode(Home0, "RdOwn"))
    \/ At(7, ReceiveOpcode("Proc0", "SnpInv"))

Trace_id_reuse ==
    \/ At(0, DeviceRule1("Proc0", 0, "UQID0"))
    \/ At(1, ReceiveOpcode(Home0, "RdOwn"))
    \/ At(2, ReceiveGO("Proc0", "E"))
    \/ At(3, ReceiveOpcode("Proc0", "Data"))
    \/ At(4, DeviceRule4("Proc0", 0, "UQID0"))
    \/ At(5, ReceiveOpcode(Home0, "CleanEvict"))
    \/ At(6, ReceiveOpcode("Proc0", "GO_WritePull"))
    \/ At(7, DeviceRule3("Proc0", 1, "UQID0", 1))
    \/ At(8, IF MaxUQID = 1 THEN ReceiveOpcode(Home0, "Data") ELSE ReceiveOpcode(Home1, "WrInv"))
    \/ At(9, IF MaxUQID = 1 THEN ReceiveOpcode(Home1, "WrInv") ELSE ReceiveOpcode(Home0, "Data"))
    \/ At(10, ReceiveOpcode("Proc0", "WritePull"))
    \/ At(11, ReceiveOpcode(Home1, "Data"))
    \/ At(12, ReceiveGO("Proc0", "I"))

Trace_go_before_data ==
    \/ At(0, DeviceRule1("Proc0", 0, "UQID0"))
    \/ At(1, ReceiveOpcode(Home0, "RdOwn"))
    \/ At(2, ReceiveGO("Proc0", "E"))
    \/ At(3, DeviceRule9("Proc1", 0, "UQID0"))
    \/ At(4, ReceiveOpcode(Home0, "RdCurr"))
    \/ At(5, ReceiveOpcode("Proc0", "Data"))
    \/ At(6, ReceiveOpcode("Proc0", "SnpCur"))
    \/ At(7, ReceiveOpcode(Home0, "RspVFwdV"))
    \/ At(8, ReceiveOpcode(Home0, "Data"))
    \/ At(9, ReceiveOpcode("Proc1", "Data"))

ScheduleLength ==
    CASE Scenario = "ids" -> 2
      [] Scenario = "rdshared" -> 4
      [] Scenario = "rdany_clean" -> 4
      [] Scenario = "address" -> 5
      [] Scenario = "rdany_shared" -> 10
      [] Scenario = "history" -> 13
      [] Scenario = "dirty_snoop" -> 9
      [] Scenario = "clean_snoop" -> 8
      [] Scenario = "first_ack" -> 21
      [] Scenario = "stale_read" -> 22
      [] Scenario = "cacheflushed_channel" -> 6
      [] Scenario = "handoff" -> 16
      [] Scenario = "handoff_response_first" -> 16
      [] Scenario = "bogus" -> 17
      [] Scenario = "dirty_cur" -> 9
      [] Scenario = "rdcurr_dirty" -> 11
      [] Scenario = "flush_dirty" -> 11
      [] Scenario = "wrinv" -> 5
      [] Scenario = "wrcur" -> 4
      [] Scenario = "itomwr" -> 4
      [] Scenario = "own_nodata" -> 4
      [] Scenario = "clean_nodata_snoop" -> 8
      [] Scenario = "id_reuse" -> 13
      [] Scenario = "go_before_data" -> 10

Scheduled ==
    CASE Scenario = "ids" -> Trace_ids
      [] Scenario = "rdshared" -> Trace_rdshared
      [] Scenario = "rdany_clean" -> Trace_rdany_clean
      [] Scenario = "address" -> Trace_address
      [] Scenario = "rdany_shared" -> Trace_rdany_shared
      [] Scenario = "history" -> Trace_history
      [] Scenario = "dirty_snoop" -> Trace_dirty_snoop
      [] Scenario = "clean_snoop" -> Trace_clean_snoop
      [] Scenario = "first_ack" -> Trace_first_ack
      [] Scenario = "stale_read" -> Trace_stale_read
      [] Scenario = "cacheflushed_channel" -> Trace_cacheflushed_channel
      [] Scenario = "handoff" -> Trace_handoff
      [] Scenario = "handoff_response_first" -> Trace_handoff_response_first
      [] Scenario = "bogus" -> Trace_bogus
      [] Scenario = "dirty_cur" -> Trace_dirty_cur
      [] Scenario = "rdcurr_dirty" -> Trace_rdcurr_dirty
      [] Scenario = "flush_dirty" -> Trace_flush_dirty
      [] Scenario = "wrinv" -> Trace_wrinv
      [] Scenario = "wrcur" -> Trace_wrcur
      [] Scenario = "itomwr" -> Trace_itomwr
      [] Scenario = "own_nodata" -> Trace_own_nodata
      [] Scenario = "clean_nodata_snoop" -> Trace_clean_nodata_snoop
      [] Scenario = "id_reuse" -> Trace_id_reuse
      [] Scenario = "go_before_data" -> Trace_go_before_data

AuditNext ==
    \/ Scheduled
    \/ /\ step = ScheduleLength /\ step' = step+1 /\ UNCHANGED vars
    \/ /\ step = ScheduleLength+1 /\ DrainNext /\ UNCHANGED step
AuditSpec == AuditInit /\ [][AuditNext]_auditVars /\ WF_auditVars(AuditNext)
EventualDone == <> (step = ScheduleLength+1 /\ Quiescent)
AuditProperty ==
    /\ (Scenario \in {"first_ack", "stale_read"} /\ step = 18 =>
           HomeNodes[Home0].txn # Undefined /\ ~ResponseQueued("GO")
           /\ ~\E m \in DOMAIN Net["Proc0"]: m.mtype = "GO")
    /\ CASE
      Scenario = "rdshared" -> (step # 4 \/ (Procs["Proc0"].state = "P_S"))
      [] Scenario = "rdany_clean" -> (step # 4 \/ (Procs["Proc0"].state = "P_E"))
      [] Scenario = "rdany_shared" -> (step # 10 \/ (Procs["Proc1"].state = "P_S"))
      [] Scenario = "history" -> (step # 13 \/ (Procs["Proc0"].state = "P_I" /\ Procs["Proc1"].state = "P_S"))
      [] Scenario = "first_ack" -> (step # 21 \/ (Procs["Proc0"].state = "P_E" /\ Procs["Proc2"].state = "P_I"))
      [] Scenario = "stale_read" -> (step # 22 \/ (Procs["Proc0"].state = "P_M" /\ Procs["Proc0"].val = 1 /\ Procs["Proc2"].state = "P_I"))
      [] Scenario = "dirty_snoop" -> (step # 9 \/ (ResponseQueued("RspIFwdM") /\ Procs["Proc0"].cmd # Undefined /\ Procs["Proc0"].cmd.raced))
      [] Scenario = "clean_snoop" -> (step # 8 \/ (ResponseQueued("RspIHitSE") /\ Procs["Proc0"].cmd # Undefined /\ Procs["Proc0"].cmd.raced))
      [] Scenario = "clean_nodata_snoop" -> (step # 8 \/ (ResponseQueued("RspIHitI") /\ Procs["Proc0"].cmd # Undefined))
      [] Scenario = "dirty_cur" -> (step # 9 \/ (ResponseQueued("RspVFwdV") /\ ~Procs["Proc0"].cmd.raced /\ Procs["Proc0"].state = "P_M"))
      [] Scenario = "bogus" -> (step # 17 \/ (Procs["Proc1"].state = "P_M" /\ Procs["Proc1"].val = 0 /\ LastWrites[0] = 0 /\ HomeNodes[Home0].val = 1))
      [] Scenario = "handoff" -> (step # 16 \/ (HomeNodes[Home0].state = "H_I" /\ HomeNodes[Home0].val = 1))
      [] Scenario = "handoff_response_first" -> (step # 16 \/ (HomeNodes[Home0].state = "H_I" /\ HomeNodes[Home0].val = 1))
      [] Scenario = "flush_dirty" -> (step # 11 \/ (HomeNodes[Home0].state = "H_I" /\ HomeNodes[Home0].val = 1))
      [] Scenario = "wrinv" -> (step # 5 \/ (LastWrites[0] = 1 /\ HomeNodes[Home0].val = 1))
      [] Scenario = "wrcur" -> (step # 4 \/ (LastWrites[0] = 1 /\ HomeNodes[Home0].val = 1))
      [] Scenario = "itomwr" -> (step # 4 \/ (LastWrites[0] = 1 /\ HomeNodes[Home0].val = 1))
      [] Scenario = "own_nodata" -> (step # 4 \/ (Procs["Proc0"].state = "P_M" /\ Procs["Proc0"].val = 1))
      [] Scenario = "rdcurr_dirty" -> (step # 11 \/ (Procs["Proc0"].state = "P_M" /\ Procs["Proc1"].state = "P_I"))
      [] Scenario = "id_reuse" -> (step # 13 \/ (HomeNodes[Home1].val = 1 /\ LastWrites[1] = 1))
      [] OTHER -> TRUE
=============================================================================
