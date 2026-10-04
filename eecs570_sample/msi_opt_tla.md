# TLA+ translation of `msi_opt.m`

`msi_opt.tla` translates the active code in `msi_opt.m`. The Murphi source is
unchanged. The translation includes all 41 declared home states, 27 declared
device states, 32 message types, 15 device rules, and seven active invariants.
Commented-out rules and invariants remain inactive.

## Representation and semantics

- `HomeNodes`, `Procs`, `Net`, `InBox`, `msg_processed`, and `LastWrites` retain
  their source roles. `error` records the first assertion, unhandled-message,
  unhandled-state, capacity, or assignment-type failure.
- Each processor rule or delivery is one atomic transition. Receive procedures
  evaluate sequential record transformations before committing their result.
  This preserves dependencies on earlier assignments and sends in the same rule.
- Delivery actions are grouped into the six CXL.cache channels and the seventh
  `D2H_REQ2` eviction lane. The source's opcode/channel combinations are preserved.
- `Net[n]` is a bag, preserving duplicate messages and arbitrary delivery order.
  Each `Send` checks capacity before adding a message. A delivery removes its
  incoming message after the receive procedure completes, matching the source.
- `InBox[n][vc]` holds one blocked message or `Undefined`. An occupied inbox blocks
  network delivery on that node/channel; retrying a stalled message remains enabled.
- `Undefined` is a TLC model value, configured as `Undefined = Undefined`.
  Scalar fields can contain this sentinel. Undefined sharer multisets and network
  multisets are represented by empty sets and empty bags respectively.
- Sharer sets preserve the source multiset behavior because `AddToSharersList`
  prevents duplicates. Capacity checks are retained.
- Processor and UQID scalarsets use distinct string labels. Protocol operations
  use equality and membership on these identifiers. No symmetry reduction is
  enabled in the supplied configurations.
- The source explicitly initializes both home values and both `LastWrites` to
  `0`; the translation does the same. Other initially unspecified scalar fields
  are `Undefined`.

Helper names identify the home/device state and incoming message where possible.
Comments such as `msi_opt.m:485` identify the corresponding source statement.
`cnt` is local scratch data in the receive result record and is excluded from
persistent TLA+ variables. Debug `put` output is omitted; errors remain checkable.
No fairness or liveness properties have been added.

## Configurations

| File | Purpose |
| --- | --- |
| `msi_opt.cfg` | Checks `TypeOK`, `NoErrors`, and all seven active source invariants. |
| `msi_opt_smoke.cfg` | Checks representation/type correctness during simulation. Source errors remain recorded but do not stop this smoke run. |
| `msi_opt_checks.tla` / `.cfg` | Seven focused checks of bags, send capacity, data/GO ordering, receiver stalls, invalidation fanout, and source error handling. |

All configurations use the source defaults: three device processors, two homes,
two addresses, one data value, one UQID, seven channels, and `NetMax = 7`.
`ProcCount`, `ValueCount`, and `MaxUQID` can be changed in the configurations.

Deadlock checking is disabled in these configurations to keep the checks focused
on the translation and source invariants. Remove `CHECK_DEADLOCK FALSE` to enable
it. Error states have no further `Next` transitions; `Spec` permits stuttering.

## Run

From `eecs570_sample`, with Java available:

```bash
# Parse, check names, and perform TLA+ semantic analysis.
java -cp ../tla2tools.jar tla2sany.SANY msi_opt.tla

# Focused translation checks.
java -XX:+UseParallelGC -cp ../tla2tools.jar tlc2.TLC \
  -noGenerateSpecTE -config msi_opt_checks.cfg \
  -metadir /tmp/msi-tla-checks msi_opt_checks

# Reproducible representation smoke run.
java -XX:+UseParallelGC -Xmx2g -cp ../tla2tools.jar tlc2.TLC \
  -noGenerateSpecTE -config msi_opt_smoke.cfg \
  -simulate num=2000 -depth 100 -seed 570 \
  -metadir /tmp/msi-tla-smoke msi_opt

# Short run with source invariants and explicit errors enabled.
java -XX:+UseParallelGC -Xmx2g -cp ../tla2tools.jar tlc2.TLC \
  -noGenerateSpecTE -config msi_opt.cfg \
  -simulate num=100 -depth 50 -seed 570 \
  -metadir /tmp/msi-tla-diagnostic msi_opt
```

Omit `-simulate ... -depth ... -seed ...` for exhaustive model checking. That can
require substantially more time and memory and has not been performed here.

Java was unavailable on the original PATH. For this session a Java 21 runtime was
downloaded to `/tmp/msi-tla-jre`; replace `java` in the commands above with
`/tmp/msi-tla-jre/bin/java` to use it. The runtime is temporary and is not part of
this repository.

## Validation results

SANY parsed and semantically checked the translation without errors or warnings.
All seven focused translation checks passed. The representation smoke run passed
`TypeOK` over 2,000 traces and 208,210 evaluated states with no TLC evaluation
exceptions. These checks establish syntax and exercise the translation; they do
not establish protocol correctness or a formal equivalence proof.

The diagnostic simulation reports `NoErrors` failing on an unhandled
`CleanEvictNoData` at `Home0` in `H_M`. The source's `H_M` receive switch has no
`CleanEvictNoData` case and reaches `ErrorUnhandledMsg`; that behavior is
preserved. A normal invariant-enabled run can therefore return a nonzero exit
status even though the TLA+ syntax and evaluation are valid.
