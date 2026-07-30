---
layout: default
title: AXI4 Verification IP
permalink: /vips/axi4/
---

# AXI4 Full Verification IP

KVIPS AXI4 is a parameterized SystemVerilog/UVM verification component for
AXI4 Full. It provides master and reactive-slave BFMs, a passive monitor,
starter assertions, functional coverage hooks, a write-derived readback
scoreboard, and runnable back-to-back examples.

This is an example-tested VIP, not a certification or vendor-equivalence
claim. The exact implemented scope and remaining work are maintained in
`axi4/docs/testplan.md` and `axi4/docs/reference_parity_audit.md`.

## Implemented behavior

- INCR, FIXED, and WRAP bursts; generated items enforce legal length, WRAP
  shape/alignment, and 4KB behavior by default.
- Parameterized address, data, ID, and user widths.
- Blocking and pipelined master operation with read, write, and combined
  outstanding limits.
- Configurable master AW/AR/W timing and pipelined BREADY/RREADY backpressure.
- Reactive slave memory with base, size, wrapping, byte backdoor access,
  region decode, address-range errors, response-rate injection, exclusives,
  response reordering, and R-channel interleaving.
- Same-ID ordering is retained when B or whole-burst R responses reorder across
  IDs.
- Independent slave AW/W/AR/B/R latency controls, random READY controls,
  response accumulation windows, and slave outstanding limits.
- Public address, write-beat, read-beat, response, and READY-control helper
  items for phase-oriented sequence construction.

## Minimal configuration

```systemverilog
axi4_env_cfg#(32, 64, 4, 1) env_cfg;
axi4_agent_cfg#(32, 64, 4, 1) master_cfg;
axi4_agent_cfg#(32, 64, 4, 1) slave_cfg;

master_cfg = axi4_agent_cfg#(32, 64, 4, 1)::type_id::create("master_cfg");
master_cfg.set_role_master();
master_cfg.vif = vif;
master_cfg.master_pipelined = 1'b1;
master_cfg.max_outstanding_reads = 8;
master_cfg.max_outstanding_writes = 8;

slave_cfg = axi4_agent_cfg#(32, 64, 4, 1)::type_id::create("slave_cfg");
slave_cfg.set_role_slave();
slave_cfg.vif = vif;
slave_cfg.slave_mem_enable = 1'b1;
slave_cfg.slave_mem_base = 'h8000_0000;
slave_cfg.slave_mem_bytes = 64*1024;

env_cfg.add_agent_cfg(master_cfg);
env_cfg.add_agent_cfg(slave_cfg);
uvm_config_db#(axi4_env_cfg#(32, 64, 4, 1))::set(this, "env", "cfg", env_cfg);
```

When master and slave share a testbench interface, enable monitoring on one
agent only to avoid duplicate analysis transactions.

## Phase-oriented helper items

`axi4_addr_phase_item`, `axi4_wdata_beat_item`, `axi4_rdata_beat_item`,
`axi4_resp_phase_item`, and `axi4_ready_ctrl_item` adapt to `axi4_item` and
configuration. They do not expose driver internals.

```systemverilog
axi4_addr_phase_item#(32, 64, 4, 1) aw;
axi4_wdata_beat_item#(32, 64, 4, 1) beat;
axi4_item#(32, 64, 4, 1) wr;

wr = new("wr");
aw = new("aw");
aw.is_write = 1;
aw.addr = 'h1000;
aw.len = 3;                         // four beats
aw.size = $clog2(64/8);
aw.burst = AXI4_BURST_INCR;
aw.apply_to(wr);

beat = new("beat0");
beat.beat_index = 0;
beat.data = 'hCAFE0000;
beat.strb = '1;
beat.apply_to(wr);
```

## Reactive-slave controls

```systemverilog
slave_cfg.slave_reorder_b = 1;
slave_cfg.slave_reorder_r = 1;
slave_cfg.slave_b_accum_cycles = 3;
slave_cfg.slave_r_accum_cycles = 3;
slave_cfg.slave_max_outstanding_wr = 8; // zero means unlimited
slave_cfg.slave_max_outstanding_rd = 8;

slave_cfg.slave_aw_random_ready = 1;
slave_cfg.slave_aw_ready_min = 0;
slave_cfg.slave_aw_ready_max = 4;

slave_cfg.slave_region_decode_enable = 1;
slave_cfg.add_slave_region('h1000, 'h1FFF);
slave_cfg.slave_rd_decerr_rate_pct = 5;
```

`slave_reorder_b` and `slave_reorder_r` reorder only across IDs. A later
transaction never bypasses an older transaction with the same ID.

## Memory-model note

The default unwritten-read policy is zero and matches the supplied scoreboard.
The slave can instead return a fill byte, random byte values, or X for
unwritten memory. Those modes require a matching environment-specific checker;
disable the supplied scoreboard for those reads if it remains zero-based.

## Running the example

From `axi4/examples`:

```bash
make questa TEST=axi4_b2b_test SEED=1
make vcs TEST=axi4_b2b_test SEED=1
make xcelium TEST=axi4_b2b_test SEED=1
```

For LSF, source the site profile, load the required simulator module in the
job environment, and use the matching `regress-*` target. The complete test
list is `axi4/examples/uvm_back2back/sim/tests_questa.list`.

## Known boundaries

- No full protocol-checker, coverage, or performance-model equivalence claim.
- Reset flushes slave reactive state; exhaustive reset-during-traffic coverage
  remains a verification objective.
- Full independent phase sequencers and project-specific integration/DMA
  collateral are intentionally outside the portable core.
