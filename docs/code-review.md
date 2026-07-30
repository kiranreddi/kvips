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

### Boundaries and risks

- This is not an exhaustive AMBA protocol checker or a replacement for a
  vendor-specific verification component.
- The scoreboard assumes zero for unwritten memory. Tests that use fill,
  random, or X unwritten-read behavior require a compatible checker.
- `order_overlapping_rw=0` intentionally serializes opposite-direction traffic
  conservatively; it is not yet a range-aware dependency scheduler.
- Reactive slave reset flushes queues and reservations. Master reset-abort
  behavior and reset-during-traffic coverage remain work items.
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
- `axi4/examples/uvm_back2back/sim/tests_questa.list`
