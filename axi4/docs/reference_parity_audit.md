# AXI4 Reference-Parity Audit

This audit compares KVIPS AXI4 with the locally available, working AXI4
reference implementation used during this review. It records behavioral
coverage, not source compatibility: KVIPS keeps its own parameterization,
layout, and vendor-neutral API.

## Closed in this revision

- B response selection may reorder between IDs but never bypasses an older
  transaction with the same ID.
- Whole-burst R response selection has the same per-ID ordering guarantee.
- Address-range error injection evaluates every actual beat address, including
  WRAP bursts; it no longer assumes a WRAP transfer is contiguous.
- The pipelined master supports a combined outstanding limit and optional
  BREADY randomization in addition to existing RREADY randomization.
- The slave provides independent AW/W/AR/B/R timing controls, optional per-R-
  beat delays, region decode, deterministic/random error-rate injection, and
  selectable unwritten-memory behavior.
- New runnable tests cover response reordering/backpressure, region decode,
  and error-rate paths.
- The slave now supports random READY toggling, response accumulation windows,
  outstanding limits, and reset-time queue/reservation flushing.
- Address, write-beat, read-beat, response, and READY-control helper items are
  available for phase-oriented sequence construction.
- The pipelined master provides an optional conservative cross-direction
  serialization policy for environments that require ordered read/write issue.
- The AXI4 transaction constraint and interface SVA now enforce the 4KB total
  transaction-size cap in addition to the no-crossing rule.
- Portable directed tests now cover explicit full/alternating/zero WSTRB,
  unaligned byte lanes, fixed narrow bursts, dedicated WRAP bursts, same-ID
  pipelining, and per-beat R-response delays.
- Pipelined master reset recovery now flushes each accepted request exactly
  once with `reset_aborted`, and the slave workers restart safely across reset
  without duplicate channel consumers.
- Range-aware cross-direction issue gating allows disjoint read/write ranges
  to overlap while conservatively holding older overlapping hazards.
- An independent interface channel checker now validates B/R association,
  same-ID ordering, beat counts, and RLAST framing.
- Cross-ID exclusive invalidation, non-pipelined reset recovery, configurable
  sideband allow-mask checking, and timeout-aborted item recovery now have
  directed tests.
- A separate AXI4-Lite interface and byte-strobe loopback example passes on all
  three supported commercial simulators; it is intentionally not a claim of
  Full-agent-equivalent Lite UVM parity.
- A simulator-neutral AXI4 CSV validator and coverage-target document provide
  a reproducible replay-input sanity check.

## Spec audit

`axi4/docs/axi4_spec_coverage.md` is the normative AXI4 requirement matrix.
It separates rules that are enforced from traffic that is stimulated and
results that are merely observed.  The default back-to-back list is now 33
tests.  The larger local comparison inventory is 68 test classes, but includes
two base classes, nine DMA-derived classes, overlapping stress/statistics
variants, and integration-specific tests; it is not a one-to-one compliance
target.

## Present in the reference but not yet at KVIPS parity

| Area | Why it remains a gap |
|---|---|
| Sequence-library breadth | The reference has a much broader set of directed negative, boundary, overlap, replay, and project-specific DMA sequences. KVIPS now has explicit portable strobe, unaligned-byte, fixed-narrow, WRAP-only, same-ID, and per-beat-delay tests, but not all variants. |
| Master overlap ordering | `AXI4_RW_ORDER_RANGE_AWARE` now allows disjoint ranges to overlap and holds older overlapping opposite-direction hazards. The interval model is conservative for WRAP and is not an exhaustive hazard proof. |
| Reset recovery | Pipelined requests are flushed deterministically and both pipelined and non-pipelined items are marked `reset_aborted`; dedicated timing cases pass on all three supported simulators. Exhaustive channel-phase timing remains. |
| Checker depth | The independent channel checker covers B/R association, same-ID ordering, beat counts, and RLAST. It is procedural and does not replace a complete negative/assertion suite. |
| Coverage and performance | Monitor-based functional coverage and basic statistics exist; a portable closure target is documented. Toggle coverage, latency distributions, occupancy/bandwidth models, and automatic simulator closure remain absent. |
| Trace/replay | UVM recording/text logging exist, and a simulator-neutral CSV validator is included; direct sequence injection and beat-level transaction tracking remain open. |
| Integration collateral | Reference DMA and DUT/RTL tests are project-specific. KVIPS should add generic integration examples only when a vendor-neutral contract is defined. |

## Required next work before claiming full vendor-VIP parity

1. Add malformed-channel negative tests and a complete RAW/WAR/WAW ordering
   matrix around the new checker and range-aware issue policy.
2. Expand coverage/performance with simulator-specific toggle/latency closure.
3. Add direct simulator sequence replay/tracker integration and then consider generic replacements
   for the reference's DMA and DUT
   integration sequences; do not import project-specific collateral into KVIPS.

## Verification record for this revision

The full `tests_questa.list` back-to-back suite is submitted through LSF for
the supported Questa, VCS, and Xcelium versions. The exact job results belong
in release/CI records rather than this source document, because they are
environment- and revision-specific.
