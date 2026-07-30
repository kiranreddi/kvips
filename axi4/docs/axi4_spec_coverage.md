# AXI4 specification coverage audit

This is a protocol audit of the KVIPS AXI4 Full implementation.  It is
deliberately narrower than a vendor-VIP feature checklist: a feature is only
called covered when the implementation, a runnable stimulus path, and a
checker or observable result are identified.

The normative baseline is Arm's [AMBA AXI and ACE Protocol Specification,
Issue H (IHI0022H)](https://developer.arm.com/-/media/Arm%20Developer%20Community/PDF/IHI0022H_amba_axi_protocol_spec.pdf).
The specification identifies AXI4 and AXI4-Lite as AMBA 4 releases, defines
the VALID/READY transfer rule, limits transactions to 4KB without crossing a
4KB boundary, and defines same-ID response ordering.  This audit does not
claim ACE or AXI5 support, and the AXI4-Lite result is limited to the separate
standalone loopback rather than the Full UVM agent.

## Status key

- **Enforced**: an assertion, constraint, or driver/slave invariant rejects or
  prevents the illegal behavior.
- **Stimulated**: a named back-to-back test intentionally exercises the path.
- **Observed**: the monitor/scoreboard reports the result, but does not prove
  every protocol rule.
- **Gap**: not implemented, only pass-through, or not checked strongly enough
  to claim compliance.

## Requirement matrix

| AXI4 area | Enforced | Stimulated/observed | Honest status and limitation |
|---|---|---|---|
| Five independent channels (AW, W, B, AR, R) | Interface handshakes and stateful SVA | Smoke, backpressure, delay, and phase-control tests | **Covered for the supplied master/slave pair**; no interconnect model is included. |
| VALID/READY transfer and payload stability | SVA hold checks for every channel | Random READY and master BREADY/RREADY tests | **Covered** for stability while stalled; source-side “VALID must not wait for READY” is not proven by an interface-only assertion. |
| AW/W independence and WLAST | Slave AW FIFO plus stateful WLAST tracking | AW/W skew and phase-control tests | **Covered** for the BFM behavior; no negative DUT agent is provided to inject malformed WLAST. |
| AR/R and RLAST | Stateful per-ID R tracking plus the independent channel checker | Burst, backpressure, interleave, and delay tests | **Covered** for generated traffic and checked for orphaned/mis-framed R responses; negative-DUT injection is not included. |
| INCR bursts, 1–256 beats | Transaction constraint, SVA length check | 256-beat and randomized tests | **Covered**. |
| FIXED bursts, at most 16 beats | Transaction constraint, SVA length check | Burst-types and fixed-narrow tests | **Covered** for legal generated traffic. |
| WRAP bursts (2/4/8/16 beats and aligned start) | Constraint and SVA length/alignment checks | Burst-types, dedicated WRAP, and corner tests | **Covered** for legal generated traffic. |
| 4KB maximum and boundary rule | Transaction constraint and AW/AR SVA checks | Corner and randomized legal-boundary tests | **Covered** for generated AXI4 transfers, including the total-size cap; intentional negative crossing is not in the passing regression. |
| SIZE and narrow transfers | SIZE constraint/SVA; byte-lane memory model | Lane sweep, fixed-narrow, and unaligned-byte tests | **Covered** for the configured bus width. |
| WSTRB byte enables, including zero strobes | Byte-accurate slave and scoreboard | Explicit full/alternating/single/zero pattern test | **Covered** for the memory model; no independent WSTRB legality checker exists for every possible DUT policy. |
| IDs and response association | ID queues in master/slave, scoreboard, and independent B/R channel checker | Random-ID pipeline, same-ID pipeline, B/R reorder tests | **Covered for generated traffic**: the checker rejects orphaned B/R responses, same-ID order violations, beat overflow, and RLAST framing errors; exhaustive negative permutations are not included. |
| Read-data interleaving | Per-ID R scheduling | Interleaved pipeline tests | **Covered** for inter-ID interleaving; all interleaving permutations are not exhaustively covered. |
| Cross-direction ordering | Optional conservative semaphore or range-aware issue gating using issue sequence and byte ranges | Ordered read/write and range-aware disjoint-region tests | **Partial**: disjoint ranges can overlap while older overlapping opposite-direction traffic is held; ranges are conservative bounding intervals (especially for WRAP), and no exhaustive hazard matrix exists. |
| OKAY/SLVERR/DECERR responses | Response enums, range/decode/rate injection | Error, region, and rate tests | **Covered as a model feature**, not as a proof of target-DUT decode or protection semantics. |
| EXOKAY and exclusive accesses | Per-ID reservation model, cross-ID invalidation, and AXI LOCK legality checks | Exclusive success, failure, restricted-request, and cross-ID tests | **Partial**: this closes cross-ID invalidation within one interface; full architectural multi-master exclusivity and all attribute matching rules are not. |
| AWCACHE/AWPROT/AWQOS/AWREGION and AR equivalents | Fields are carried through the interface and an optional configurable allow-mask checker | Sideband policy test plus monitor coverage | **Partial**: disallowed values can be rejected as an environment policy; memory/peripheral permission, cacheability, QoS arbitration, or region behavior is not modeled. |
| USER sidebands | Configurable common USER width and pass-through | Phase/trace paths | **Partial**: one shared USER width is supported; independent per-channel widths and semantic checking are absent. |
| Reset | Interface reset, reset-aware slave workers/queue flush, pipelined response aborts, and non-pipelined item abort marking | Pipelined and non-pipelined reset-recovery tests | **Covered for configured driver semantics**: every accepted request is marked/returned once with `reset_aborted`; all five channel-phase timings are not exhaustively randomized. |
| Timeout | Configurable master handshake timeout recovery marks an item `timeout_aborted`; default remains fail-fast | Timeout-recovery test with a deliberately stalled slave | **Partial**: configured address/data handshake paths recover; this is not a universal target-DUT timeout protocol or a proof that every external pending state can drain. |
| Memory initialization and mapping | Base/size/wrap, valid-byte tracking, fill/random/X policy | Configuration is available; default scoreboard assumes zero | **Partial**: non-zero/X policies require a matching environment checker. |
| AXI4-Lite | Separate `axi4_lite_if` and a byte-strobe/independent-channel memory loopback | `axi4_lite/examples/loopback` passes on Questa, VCS, and Xcelium | **Partial**: this is a standalone basic example, not a Full-agent-equivalent Lite UVM package. |
| Coverage, performance, replay | Monitor coverage/counters plus a simulator-neutral CSV validator and closure target document | `axi4/tools/axi4_csv_replay.py` validates a checked-in replay sample | **Partial**: no toggle model, occupancy/bandwidth reference, or automatic simulator replay injection is claimed. |

## What the test count means

The current default back-to-back list contains **33 runnable tests** after the
portable additions in this revision.  The local comparison inventory contains
**68 test classes**, including two base classes and nine DMA-derived classes;
the remaining classes include several overlapping stress/statistics variants
and integration-specific tests.  Therefore the counts are not a compliance
ratio.  The meaningful comparison is the requirement matrix above: KVIPS now
has explicit portable coverage for strobes, unaligned byte lanes, fixed narrow
bursts, dedicated WRAP bursts, same-ID pipelining, per-beat R delays, reset
recovery, and independent B/R channel checks. It still does not have a full
AXI4-Lite UVM agent, exhaustive reset timing for every channel phase, or
universal semantic sideband behavior.

## Priority gaps

1. Expand the checker tests with intentional malformed B/R and WLAST stimuli,
   plus a complete same-ID/cross-ID ordering matrix.
2. Decide whether a full AXI4-Lite UVM package is in scope; the current
   standalone interface/loopback is intentionally not presented as parity.
3. Add simulator-specific toggle/functional coverage closure and automatic
   sequence replay if a consuming environment requires them.
4. Only after the above, consider generic integration/DMA examples.  Those are
   not protocol proof and should not be counted as portable AXI4 compliance.
