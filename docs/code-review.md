---
layout: default
title: KVIPS Code Review
permalink: /docs/code-review/
---

# Code Review Status

This page records engineering status, not a protocol-compliance certification.
The runnable AXI4 source and tests are the source of truth.

## AXI4 assessment

### Strengths

- Parameterized SystemVerilog/UVM architecture with separate interface, agent,
  driver, monitor, scoreboard, and sequence layers.
- Portable compile/run flows for Questa, VCS, and Xcelium; the back-to-back
  suite is exercised through LSF.
- Legal burst generation, starter protocol SVA, reactive memory-model slave,
  write-derived scoreboard, functional-coverage hooks, and basic statistics.
- Pipelined traffic, exclusive access modeling, response errors, region decode,
  B/R ordering controls, random READY, slave limits, and phase-oriented helper
  items are implemented and tested.
- An RTL-DUT milestone now connects the KVIPS AXI4 master to a synthesizable,
  byte-addressed AXI4 RAM device.  Commercial simulator runners and a directed
  DUT test list cover bursts, narrow strobes, boundaries, DECERR, pipelining,
  and master-side backpressure.

### Boundaries and risks

- This is not an exhaustive AMBA protocol checker or a replacement for a
  vendor-specific verification component.
- The scoreboard assumes zero for unwritten memory. Tests that use fill,
  random, or X unwritten-read behavior require a compatible checker.
- `order_overlapping_rw=0` intentionally serializes opposite-direction traffic
  conservatively; it is not yet a range-aware dependency scheduler.
- Reactive slave reset flushes queues and reservations. Master reset-abort
  behavior and reset-during-traffic coverage remain work items.
- The RTL-DUT target is a deliberately small single-device slave; it is not an
  interconnect, arbitration model, or independent external-master proof.
- Coverage, performance, trace/replay, negative testing, and integration
  collateral are useful baselines, not full closure methodology.

## Required review gates

1. Compile and run the relevant back-to-back list on every supported simulator.
2. Check for nonzero UVM error/fatal summaries and tool diagnostics.
3. Add a directed test for every new configuration path and protocol rule.
4. Keep `axi4/docs/testplan.md`, `axi4/docs/supported_features.md`, and the
   reference-parity audit synchronized with code changes.
5. Do not claim compliance, coverage closure, or vendor parity without
   evidence tied to a specific release.

## Review artifacts

- `axi4/docs/testplan.md`
- `axi4/docs/supported_features.md`
- `axi4/docs/reference_parity_audit.md`
- `axi4/docs/axi4_spec_coverage.md`
- `axi4/examples/uvm_back2back/sim/tests_questa.list`

## AHB assessment

The AHB VIP now has a 16-test UVM back-to-back list covering SINGLE,
INCR/WRAP bursts, wait states, error responses, BUSY, legality boundaries,
security-policy deny/allow behavior, big-endian byte lanes, Full RETRY/SPLIT
response encoding, and mid-run reset recovery. The list was
run through the LSF Questa, VCS, and Xcelium flows with zero UVM errors/fatals
and zero simulator errors in the validated runs.

The honest boundary is that this is a single-master/single-slave reference
environment. It carries HNONSEC, supports an attachable security-policy
callback, and models Full response encodings, but does not claim multi-master
arbitration, HSPLIT routing, multi-slave interconnect decode, or formal/toggle
coverage closure. See `ahb/docs/amba_spec_coverage.md` for the protocol-area
matrix and remaining work.

## APB assessment

The APB4 DUT milestone connects the KVIPS master to a byte-addressed RTL RAM
responder. Its eight-test list covers masked writes, protection attributes,
wait-state stability, mapped boundaries, and both unmapped `PSLVERR` cases.
Questa, VCS, and Xcelium runners use an evidence gate requiring nonzero
monitor handshakes, zero scoreboard mismatches, and no UVM or simulator
errors. The target remains a single-device integration example; multi-slave
decode and independent-master interoperability are not claimed.
