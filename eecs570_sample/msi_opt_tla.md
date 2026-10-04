# Corrected TLA+ model of `msi_opt`

`msi_opt.tla` is the corrected, message-oriented successor to the original
literal translation of `msi_opt.m`. The Murphi file remains the historical
source. The literal translation is available in git commit `eafe09e`.
The [issue investigation](msi_opt_issues.md) records why the state-based
translation needed correction; the supplied
[CXL-cache reference](../CXL-cache-protocol-reference.md) is the protocol target.

## Scope and operation mapping

The model retains the source's two addresses/two homes, one cacheline per device,
and one outstanding device command. All fifteen active source rule names are
retained. Their operations are RdOwn, RdAny, WrInv, CleanEvict,
CleanEvictNoData, WrCur, ItoMWr, RdShared, RdCurr, RdOwnNoData, CLFlush,
CacheFlushed, DirtyEvict, and the local E-to-M store. Two original rules issue
CleanEvictNoData from E and S respectively. RdOwnNoData also supports I, as
allowed by the reference.

Values represent full cachelines. Writes replace a full line; packet chunks,
byte masks, poison/error injection, credits, device-attached memory, and
unissued CXL operations are outside this model's scope. The model chooses the
ordinary error-free response policy. It does not claim to implement every CXL
feature or every optional response policy.

## State and transaction lifetimes

- `Procs[p].state` is the actual cache permission I/S/E/M, independent of
  `Procs[p].cmd`, the device command tracker. The command retains opcode,
  CQID, address, payload, GO/data/pull progress, and the eviction race flag.
- `HomeNodes[h].owner/sharers` describe the directory. `H_E` means one tracked
  exclusive device; the device can be E or M. Home state is not used to reject
  legal clean evictions after ownership handoff.
- `HomeNodes[h].txn` retains the original request, a set of snoop targets,
  per-device UQIDs, responses, and received data. `H_BUSY` marks an active
  transaction. A target remains in this tracker until completion even after
  its directory entry is removed.
- A home serializes its active line transaction. Other device requests remain
  in the network while responses/data progress independently. An eviction can
  be issued concurrently with a snoop; its request waits until the existing
  snoop has completed before the home starts its pull. This is a conservative
  host scheduling policy, not a rule that devices cannot race evictions/snoops.
- Host UQIDs are reserved across both homes within each device link. Allocation
  reserves every needed link atomically. A host tracker survives until its
  required response/data is consumed; device CQID retirement is independent.
- CacheFlushed is address-independent and removes the device's filter entries
  at both homes. Already launched snoop obligations remain active.

For invalidating/downgrading snoops, the host flushes forwarded dirty data into
its abstract memory before granting new read ownership. SnpCur snapshots are
only forwarded to the RdCurr requester and do not fill the home value. It therefore chooses GO-E/GO-S rather than GO-M. Initial
clean data never receives GO-M. The device receiver accepts every legal normal
RdAny grant, including GO-M; focused checks exercise all legal read grants in
both GO/data orders.

## Messages and ordering

`Net[n]` remains a bag, with multiplicity and arbitrary delivery order. Its
six channel numbers correspond to the six CXL.cache channel types. Evictions
use D2H Request; the old seventh eviction lane and per-channel stalled inboxes
are removed. An unavailable receiver leaves the message in the network, where
independent response/data traffic can pass it.

Response/data records carry an internal `addr` annotation derived from the
command tracker. This supports model checks and GO/snoop ordering; it is not
an additional H2D response/data wire field. H2D response/data echo CQID, snoop
responses echo host UQID, and pulled data uses the UQID in response `RspData`.
Existing-line requests use the retained cache address rather than the free
ruleset address argument.

GO updates permission immediately. A read tracker survives until both GO and
data arrive. Data received after a later invalidating snoop is drained without
recreating the invalidated copy. A same-line snoop cannot pass a queued GO;
data-dependent forwarding waits for the data buffer while H2D Data can pass
that snoop. The single active home transaction prevents new same-line snoops
from overlapping an outstanding pull.

Clean S/E snoop responses carry no data. The home waits for data only for
forwarding response classes, in either response/data arrival order. Every
expected snoop must complete before a GO/pull is emitted.

CleanEvict and DirtyEvict retain their writeback payload and snoop responsibility
until the combined pull response. A state-changing snoop sets the retained
tracker's Bogus flag; later evict data is discarded at the host. SnpCur with
RspVFwdV leaves that flag unchanged. CleanEvictNoData drops the clean copy when
issued and retains its notification tracker until GO-I; later misses still
return RspIHitI. An E permission obtained without data can be fully overwritten
or dropped with CleanEvictNoData, but cannot supply an undefined full-line
CleanEvict payload.

## Safety and progress checks

`Safety` includes single-writer exclusivity, readable-copy freshness relative
to `LastWrites`, cache/directory shape and coverage, channel/ID/address and
transaction correlation, host ID uniqueness, complete snoops before grants,
data validity, forwarding data obligations, and snoop/pull exclusion.
`PendingWorkCanDrain` requires an enabled delivery whenever transactions or
messages remain. It catches transport stalls even when unrelated new commands
could still be issued. Original invariant names remain available; memory is
required to match the last write in stable I/S home states.

`Spec` has no fairness assumption and is used for safety. `FairSpec` adds
strong fairness to delivery of each device's sole request and weak fairness to
response/data/snoop delivery on each link. `RequestProgress` checks eventual
completion of every device command. Strong fairness for request acceptance is
needed because competing requests may repeatedly take an intermittently free
home or tracker.

The regression harness schedules an actual prefix from `Init`, then explores
all remaining delivery interleavings. Its temporal `EventualDone` requires the
prefix to finish and all traffic/trackers to drain, preventing a disabled
scheduled action from passing vacuously. The old runner's expected failures
have been replaced by passing safety/progress regressions.

## Configurations and commands

| File | Purpose |
| --- | --- |
| `msi_opt.cfg` | Three devices, two values, two IDs; all safety checks, including simulation. |
| `msi_opt_small.cfg` | Exhaustive safety check with two devices, two values, one ID. |
| `msi_opt_progress.cfg` | Exhaustive fair request progress with one device, two values, two IDs. |
| `msi_opt_checks.tla/.cfg` | Focused normal/invalid message and lifetime checks. |
| `msi_opt_audit.tla` and `msi_opt_audit.py` | Scheduled regressions and exhaustive fair drain. |

From `eecs570_sample`, with Java available:

```sh
java -cp ../tla2tools.jar tla2sany.SANY msi_opt.tla msi_opt_audit.tla msi_opt_checks.tla
java -XX:+UseParallelGC -Xmx2g -cp ../tla2tools.jar tlc2.TLC \
  -workers 8 -noGenerateSpecTE -config msi_opt_checks.cfg \
  -metadir /tmp/msi-focused msi_opt_checks
java -XX:+UseParallelGC -Xmx4g -cp ../tla2tools.jar tlc2.TLC \
  -workers 8 -noGenerateSpecTE -config msi_opt_small.cfg \
  -metadir /tmp/msi-small msi_opt
java -XX:+UseParallelGC -Xmx2g -cp ../tla2tools.jar tlc2.TLC \
  -workers 8 -noGenerateSpecTE -config msi_opt_progress.cfg \
  -metadir /tmp/msi-progress msi_opt
# TLC simulation num is per worker: 8 x 2000 = 16000 traces.
java -XX:+UseParallelGC -Xmx2g -cp ../tla2tools.jar tlc2.TLC \
  -workers 8 -noGenerateSpecTE -config msi_opt.cfg \
  -simulate num=2000 -depth 200 -seed 570 -metadir /tmp/msi-smoke msi_opt
python3 msi_opt_audit.py --workers 8
python3 msi_opt_audit.py --workers 8 --ids 2
```

The runner accepts `--java /path/to/java`, `--scenario NAME`, `--output-dir PATH`,
`--ids N`, and `--workers N` (default four). A `PASS` requires TLC success on
safety and eventual complete drain; unexpected errors return nonzero. Each run
stores configs, logs, failure counterexamples if any, and a summary outside
the repository.

The session Java runtime is `/tmp/msi-tla-jre/bin/java`; it is temporary and not
part of the repository. Replace `java` above with that path if needed.

## Validation

Final checks used eight TLC workers on 2026-10-05:

| Check | Result |
| --- | --- |
| SANY / TLC semantic analysis of all three modules | Passed, no syntax/semantic errors or warnings. |
| Twelve focused protocol/lifetime obligations | Passed. |
| Two-device exhaustive safety, two values, one ID | Passed: 11,031,953 generated states, 2,898,012 distinct states; queue exhausted. |
| One-device exhaustive fair progress, two values, two IDs | Passed: 324,449 generated states, 111,372 distinct states; safety and `RequestProgress` passed. |
| Three-device safety simulation, two values, two IDs | Passed: 16,000 traces with maximum depth 200, 3,871,384 evaluated states; seed 570. |
| Twenty-four regression scenarios, one and two IDs | All 48 runs passed safety, checkpoint obligations, and eventual complete drain. |

Logs for the final checks are in `/tmp/cxl-fix`: `p2-cur.log`,
`progress-cur.log`, `p3-cur-sim.log`, `focused-cur.log`, and the
`validated-cur-one-id` / `validated-cur-two-ids` directories. These temporary
artifacts are reproducible with the commands above.

The exhaustive safety result applies to the two-device configuration. The
full fair-progress result applies to the one-device configuration. Three-device
coverage consists of simulation and targeted exhaustive drain regressions;
a full three-device state-space/liveness check has not been completed. This is
verification of the declared abstract scope, not all CXL.cache behavior.
Earlier literal-translation results are historical.
