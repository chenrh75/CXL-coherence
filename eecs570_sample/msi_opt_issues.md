# Issue investigation and repair status for `msi_opt`

Investigation dated 2026-10-05, against the source retained from commit
`9201030` and its translation in `eafe09e`. The protocol target used here is the
supplied [CXL-cache reference](../CXL-cache-protocol-reference.md), which describes
CXL 4.0 v1. Findings about opcode legality are relative to that document.
Neither source file was changed during the initial investigation. The subsequent
repair updates `msi_opt.tla`; `msi_opt.m` remains the historical reference.

## Repair status

The defects below are repaired in the current TLA+ model. It now uses explicit
command and snoop trackers, six protocol channels, and separate cache permission
and writeback-buffer lifetimes. The old Murphi implementation remains unchanged;
its literal TLA+ translation is available at git commit `eafe09e`.

| Finding | Repair |
| --- | --- |
| Early exclusive grant / stale shared copy | Retain each pending snoop response and required data; grant only after all complete. |
| Read/eviction transaction mix-up | Retain each request's source, opcode, CQID, and address. A busy home holds later requests while responses/data pass them. |
| Lost pending-eviction responses/data | Keep eviction payload and command alive through snoops; set and consume Bogus for state-changing races. |
| E grant followed by unhandled clean eviction | Track exclusive directory ownership independently of the device's E/M state; accept legally issued clean eviction even after a snoop degrades the line. |
| RdAny only accepts M | Accept every legal normal grant in either GO/data order. |
| Address and ID corruption | Use retained line addresses, echo CQID, allocate link-scoped host UQID across both homes, and use pull RspData for returned data. |
| Illegal response/channel/data combinations | RdShared gets S, initial clean RdAny gets E, GO uses H2D Response, and clean snoop responses carry no data. |
| Verification gaps | Add exclusivity, freshness, correlation, complete-snoop, transport-drain, and other safety checks, plus fair progress and regression drain properties. |

A final reference review also corrected SnpCur: current data is forwarded only
for one-use RdCurr consumption and does not fill the home value. An S hit uses
a legal no-data response; RspVFwdV is restricted to E/M hits. These obligations
have focused checks.

CleanEvictNoData deserves a qualification to the original diagnosis in issue 3:
the reference says to drop the clean copy when issuing this notification. The
corrected device does that and replies RspIHitI to later misses while retaining
the notification tracker. CleanEvict/DirtyEvict instead retain cache/writeback
responsibility until the pull response. Regressions cover both behaviors.

See [model notes](msi_opt_tla.md) for representation, runnable configurations,
validation counts, and limits. The current regression runner verifies successful
completion rather than expecting the old failures.

The sections below preserve the **pre-repair findings and counterexamples**.
The most serious was premature exclusive ownership: a subsequent store left
another device with stale readable data while the seven original invariants
still passed.

## Reproduction and scope

Run from the repository root, with Java available:

```sh
python3 eecs570_sample/msi_opt_audit.py --java /path/to/java
python3 eecs570_sample/msi_opt_audit.py --java /path/to/java --scenario stale_read
```

The current runner discovers Java on PATH or the previously downloaded
`/tmp/msi-tla-jre/bin/java`, uses the repository's `tla2tools.jar`, and writes
configs, logs, failure traces, and `summary.json` to a printed temporary directory.
It accepts `--output-dir`, `--workers` (default four), and `--ids`. `PASS` now means
that TLC found no safety failure and proved the scheduled prefix completes and
all remaining transactions drain. All 24 scenarios are checked with one and two
IDs. The old `REPRODUCED` output and the failure table below describe the initial
investigation, not the current runner's expected result.

The initial audit harness extended the then-unchanged translation. Each
scenario starts at the actual `Init` and schedules existing device actions and
network deliveries. It does not manufacture a problematic starting state or
patch the receive handlers. All scenarios use three devices, two data values,
and one ID per link. Every replay checks `TypeOK` and all seven original
invariants before its additional audit property.

| Scenario | Transitions to failure | Observation |
| --- | ---: | --- |
| `first_ack` | 20 | E owner coexists with another S copy. |
| `stale_read` | 21 | M owner holds 1; another S copy still holds 0. |
| `history` | 13 | Eviction GO-I sent to a different transaction's requester. |
| `clean_snoop` | 8 | Pending clean eviction discards a snoop without responding. |
| `dirty_snoop` | 9 | Pending dirty eviction sends snoop data without its response. |
| `handoff` | 13 | GO-E recipient's legal CleanEvict is unhandled by home H_M. |
| `rdany_shared` | 11 | Device refuses the host's legal GO-S for RdAny. |
| `address` | 5 | Eviction routed to Home0 carries address 1. |
| `ids` | 2 | Initial RdOwn completion/data carry undefined CQID. |
| `rdshared` | 2 | RdShared receives GO-E. |
| `rdany_clean` | 2 | Initial clean memory data receives GO-M. |
| `cacheflushed_channel` | 6 | Home H_M emits GO on H2D Request. |

All twelve failures were reproduced before repair. Their historical run artifacts
are in `/tmp/cxl-audit/final-replays`. The current runner instead checks repaired
versions of those scenarios and additional protocol/lifetime cases.

An independent, unscheduled breadth-first TLC run with one device, two values,
the original invariants, and `NoErrors` exhausted 36,985 distinct states without
failure. With two devices, TLC failed `NoErrors` after 1,206,813 distinct states,
with a 13-transition owner-handoff trace. That run stopped at the first error;
it did not exhaust the two-device state space. The three-device replays above
are focused witnesses, not an exhaustive three-device verification or a
liveness proof.

## 1. Invalidations are considered finished before replies arrive

Source: `msi_opt.m:413–436`, `HT_SE_AD` at 2793, and `HT_SI_AD` at 2638.
Reference: §§7, 9.9, and 10.4, covering exclusive ownership and complete snoop
resolution before a new grant.

`SendInvReqToSharers` removes every device from the sharer multiset while
issuing its SnpInv. Consequently, the count used by the receiving transient
state is already zero when the first snoop acknowledgment arrives. There is
no separate set/count of outstanding snoops. `HT_SE_AD` therefore grants E
on that first reply, even if other invalidations remain in flight.

The `first_ack` execution is:

1. Proc0 obtains address 0 with RdOwn. Proc1 and Proc2 subsequently obtain S
   copies, leaving all three devices Shared with value 0.
2. Proc0 issues RdOwnNoData. The home sends SnpInv to Proc1 and Proc2 and
   immediately empties its sharer list.
3. Only Proc1 receives SnpInv and returns RspIHitSE.
4. The home accepts that reply as completion and sends GO-E to Proc0.
5. Proc0 accepts GO-E while Proc2 is still S with value 0.

`stale_read` adds the existing local store action, writing 1 at Proc0. The
result is Proc0 M/value 1, Proc2 S/value 0, and `LastWrites[0] = 1`.
This is a stale readable copy; the model has no separate local-load action,
so the witness checks the readable cache contents directly.

The original shared-value invariants only check devices when the home is
`H_S`. It is now `H_E`, so they miss the stale copy. This also affects other
operations using the same invalidation helper, including flush/write
invalidation completion. Those other operations were inspected statically,
not individually replayed.

Fix direction: keep an outstanding-snoop set keyed by target and transaction.
Removing a directory sharer is distinct from receiving its acknowledgment.
Grant ownership only after every expected response and any required forwarded
data have arrived. Add a per-address single-writer invariant and a readable
copy freshness invariant that do not depend on the home being `H_S`.

## 2. Concurrent eviction and read transactions are mixed together

Source: `HT_ES_AD`, especially `msi_opt.m:2223–2240`.
Reference: §§3 and 11, describing request correlation and eviction races.
Witness: `history`.

While servicing a second device's RdShared, the previous E owner receives
SnpData and downgrades to S. That old owner issues CleanEvictNoData before its
snoop response/data have been processed by the home. The home handles the
eviction by sending GO-I to `HomeNodes[h].requester`, which is the *reader*,
rather than `msg.src`, which is the *evictor*.

The reader later receives both its correct GO-S and the stray GO-I. In the
replay, GO-I is delivered while the reader is `PT_IS_D`, producing
`Unhandled message type at "Proc1": GO`. The evictor never receives its own
completion, and the home retains its sharer entry in this path.

This is the same failure mechanism visible in the historical Murphi output.
The replay starts the first acquisition with RdOwn instead of the historical
RdShared, avoiding reliance on that acquisition's illegal GO-E result.

Fix direction: retain independent transaction context for the read and
eviction. Each completion must use its own source/CQID and update the relevant
directory entry. A single `requester/request_type` pair cannot represent both.

## 3. Pending evictions lose snoop responses and transaction lifetime

Source: `PT_EI_GOI` at `msi_opt.m:4162`, `PT_MI_GP` at 4254, and related
eviction transient handlers. Reference: §§6–7 and 11.2.
Witnesses: `clean_snoop`, `dirty_snoop`.

For a pending CleanEvictNoData, `PT_EI_GOI` handles SnpInv/SnpData by becoming
I and undefining the cache address/value, without sending a snoop response.
It also abandons the state that was waiting for the eviction's GO-I. The clean
replay demonstrates a missing RspIHitSE on SnpInv.

For a pending DirtyEvict, `PT_MI_GP` handles SnpInv by sending data, becoming
I, and discarding its cache state, without RspIFwdM and without retaining the
pending pull transaction. The host cannot properly complete that snoop, and
the later eviction pull has no surviving tracker/state to service it.

The reference explicitly requires a pending eviction to service snoops, keep
its eviction transaction alive, and mark later eviction data Bogus following
a qualifying state-changing snoop. SnpCur/RspVFwdV is the stated exception to
that Bogus rule. The current flags and transient states do not implement this
transaction lifetime consistently. The replays check the immediately missing
responses; they do not claim to prove a global fair-execution deadlock.

Fix direction: separate eviction tracker lifetime/data from current cache
permission. Invalidation may leave the cache I while a tracked eviction still
must accept its completion/pull and drain appropriately marked data.

## 4. Ownership handoff grants E but its home completion path rejects E eviction

Source: `HT_ME_AD` at `msi_opt.m:3509`, `HT_ME_A` at 3566, `HT_ME_D` at 3618,
and `H_M` at 2876. Reference: §§5.1 and 11–12.
Witness: `handoff`, also found by the unrestricted two-device TLC run.

A previous M owner is invalidated for another device's RdOwn. The home sends
GO-E/data to the new owner. Both response/data arrival orders eventually set
the home to `H_M`, though the device enters `P_E`. That E owner can legally
issue CleanEvict, but `H_M` has no CleanEvict handler and reports an unhandled
message. CleanEvictNoData is also absent from that home state.

Internal home state names are not protocol requirements: a home could track
E/M together conservatively. The actual defect is that the grant and the
supported future owner requests disagree. Coordinate those semantics instead
of adding an isolated handler that hides the inconsistency.

There is a second defect in the same path: `HT_ME_AD` sends GO immediately
when snoop data arrives, before RspIFwdM arrives. Reference §10.4 requires
both the response and the expected forwarded data before the new GO. This
early emission is visible in the handoff trace; the replay delivers the GO
only after the response, so its final unhandled eviction does not depend on
exploiting that early grant.

## 5. RdAny device tracking accepts only M

Source: `PT_IM_AD`, `PT_IM_D`, and `PT_IM_A` at `msi_opt.m:3951–4009`.
Reference: §5.1, allowing GO-S, GO-E, or GO-M for RdAny.
Witness: `rdany_shared`.

An RdAny requester follows the I-to-M transient path. A host with another
cached owner can legitimately return GO-S, and the current home does so.
After data arrives, however, the device in `PT_IM_A` only accepts GO-M.
GO-S is left unprocessed in its response inbox, and retrying it does not
change that decision. The request has no implemented successful completion
path for this result. GO-E is likewise not accepted by these handlers.

Fix direction: track the read opcode and granted state separately from data
arrival, and support every legal successful RdAny result in either arrival
order.

## 6. Addresses and transaction identifiers are not preserved correctly

Source: request rules at `msi_opt.m:4530`, 4545, 4643, 4658, and 4718;
initial RdOwn home handler at 479–490; pull handlers at 4062 and 4100.
Reference: §§3–4.
Witnesses: `address`, `ids`.

Eviction and upgrade rules choose the destination from `p.addr` but populate
the message address using the independent ruleset variable `ad`, without
requiring `ad = p.addr`. The address replay owns address 0 and emits
CleanEvictNoData to Home0 with address 1. The home largely dispatches using
its own identity, and device receives do not check that a snoop addresses the
cached line, which masks/address-amplifies this modeling error.

Device requests populate `cqid` and leave `uqid` undefined. Many home response
and data calls nevertheless put `msg.uqid` into the outgoing CQID position.
The initial RdOwn replay already produces undefined completion/data CQIDs.
The home record does not retain the originating request CQID needed when a
later snoop response/data triggers the completion.

Other pull handlers return data using `msg.cqid` or `msg.uqid` instead of the
pull UQID carried by `RspData`. One ID per link and receivers that ignore
correlation fields conceal these errors. Copying a device CQID into a host
snoop UQID also does not provide an independent host tracker allocator.

Fix direction: use the retained line address for existing-line operations;
explicitly retain and validate request CQIDs and host snoop/pull UQIDs, with
their source/link context. An abstract finite ID space is sufficient, but
its allocation, correlation, and reuse must be modeled.

## 7. Several emitted messages violate the supplied opcode/channel rules

These are protocol mismatches even when existing state invariants pass:

| Source location | Current behavior | Reference requirement | Evidence |
| --- | --- | --- | --- |
| `H_I`, line 533 | RdShared gets GO-E. | §5.1: successful RdShared gets GO-S. | `rdshared` replay |
| `H_I`, line 552 | Initial RdAny gets GO-M for clean initialized memory. | §2.2: GO-M transfers genuinely modified data. | `rdany_clean` replay |
| `H_M`, line 2968 | CacheFlushed GO uses `H2D_REQ`. | §§3, 8: GO belongs to H2D Response. | `cacheflushed_channel` replay |
| `P_E`, lines 4140–4156 | SnpData/SnpInv send data along with RspSHitSE/RspIHitSE. | §§6–7: these clean response classes have no data. | Source inspection; extra data also occurs in sharing replays |

The clean-snoop data defect is coupled to home handlers that expect that
extra data, such as `HT_ES_AD/A/D`. Correct both ends; merely removing the
device data send would expose a home that waits for data it should not expect.

These are concrete problems in the operations already represented. Absence
of unrelated CXL 4.0 features, such as bundling, HDM forwarding, or additional
write classes, is not treated here as a defect in this scoped model.

## Historical debugging review

`git log -- eecs570_sample/msi_opt.m` identifies `6763c98` and `9201030`, both
dated 2025-12-08. The retained source is the latter debugging version.

The historical `9201030:eecs570_sample/output.txt` ends with an unhandled
message after 3,188,024 explored states and 11,313,023 rule firings, not a
successful verification. Its trace is the misdirected eviction GO described
in issue 2. That underlying transaction mix-up remains reproducible.

The debugging commit introduced a seventh virtual channel, `D2H_REQ2`, for
evictions. This can avoid some inbox blocking, but does not supply independent
transaction context or fix misdirected completions. It is an abstraction
choice rather than a seventh CXL.cache wire channel; the reference has six.

The diff also comments out snoop responses and pending-eviction transitions
in `PT_EI_GOI`, replacing them with I/discard behavior. The clean-eviction
missing response in issue 3 is therefore an identifiable regression in that
debugging change. The analogous `PT_MI_GP` dirty-eviction defect was already
present in `6763c98`. Other changes, including some initial
RdOwn and response/data arrival-order corrections, are locally sensible;
the history should not be reverted wholesale.

## Historical verification gaps and suggested repair order

The original `ValueCount = 1` configuration cannot expose disagreement between
two valid data values. Even with two values, the existing invariants omit
single-writer exclusivity, freshness outside home `H_S`, transaction
correlation, legal opcode/data/channel combinations, and snoop completion.
Representation smoke tests establish type consistency, not these properties.

The original network was an unordered bag and did not enforce GO-before-later-same-line
snoop transport ordering required by reference §§10 and 13. Arbitrarily
reordered traces must therefore be checked against that ordering before
calling them realizable protocol executions. The ownership and stale-copy
witnesses above wait for acquisition GO/data before processing subsequent
snoops; they do not rely on bypassing that ordering. Some paths already emit
nonconforming messages, as separately identified above, so these witnesses
demonstrate defects in the current model rather than a complete conforming
wire implementation.

Deadlock checking is disabled in the supplied configurations. Retry actions
can also stutter, so enabling a simple deadlock check alone would not prove
eventual completion. The initial audit did not include fair progress analysis with explicit pending
transactions. The corrected model now has such trackers and fairness, with the
validation limits documented in the model notes. No full liveness or exhaustive protocol
conformance claim is made by this audit.

Recommended order:

1. Add the missing safety/transaction checks, especially single writer,
   readable-copy freshness, and pending snoop completion.
2. Fix outstanding invalidation accounting and concurrent transaction
   context; these cause the coherence violation and old crash.
3. Repair eviction tracker lifetime and response/data obligations together.
4. Coordinate grants, home completion states, and legal device outcomes.
5. Correct address/ID/channel handling and clean-snoop data semantics.
6. Encode required transport ordering and then check fair transaction progress.

The architectural issue behind several failures is that cache permission,
directory ownership, and transaction completion are compressed into large
state enums plus one home requester. A message-oriented rewrite can help,
provided it still models those three concepts explicitly and preserves
pending snoop/eviction trackers until all obligations finish.
