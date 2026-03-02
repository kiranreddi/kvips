---
layout: default
title: AHB Verification IP — KVIPS
description: Complete AMBA AHB-Lite and AHB Full verification IP with UVM agents, protocol assertions, scoreboard, and example testbench.
permalink: /docs/ahb-vip/
---

# AHB-Lite / AHB Full Verification IP

<div class="badge-row-lg">
  <span class="badge badge-green">Stable v1.0</span>
  <span class="badge badge-blue">AMBA 3.0</span>
  <span class="badge badge-gray">SystemVerilog + UVM</span>
</div>

## Overview

The KVIPS AHB VIP provides a complete, production-ready AMBA AHB verification solution supporting both **AHB-Lite** and **AHB Full** in a single compiled image. The mode is selectable at runtime via plusargs.

Key capabilities:

- **Master agent** with sequencer + driver for bus stimulus
- **Slave agent** with memory model and two-cycle error response
- **Passive monitor** with functional coverage and transaction recording
- **Protocol assertions (SVA)** with runtime enable/disable
- **Scoreboard** for byte-accurate data integrity checking
- **8 pre-built regression tests** covering smoke, bursts, wait states, error injection, and stress

## Quick Start

```bash
# Clone repository
git clone https://github.com/kiranreddi/kvips.git && cd kvips

# Run AHB smoke test
cd ahb/examples/uvm_back2back/sim
./run_questa.sh +UVM_TESTNAME=ahb_smoke_test

# Run full regression
cd ../..
make regress-questa
```

## Directory Structure

```
kvips/ahb/
├── sv/
│   ├── if/          ahb_if.sv              — Parameterized interface
│   ├── assertions/  ahb_if_sva.svh         — Protocol SVA
│   ├── pkg/         ahb_types_pkg.sv       — Types, enums, utilities
│   │                ahb_uvm_pkg.sv         — UVM package (all includes)
│   └── uvm/
│       ├── ahb_transaction.svh             — Transaction item
│       ├── ahb_cfg.svh                     — Agent configuration
│       ├── ahb_sequencer.svh               — Sequencer
│       ├── ahb_master_driver.svh           — Master BFM
│       ├── ahb_slave_driver.svh            — Slave BFM + memory model
│       ├── ahb_monitor.svh                 — Monitor + coverage
│       ├── ahb_scoreboard.svh              — Data integrity checker
│       ├── ahb_sequences.svh               — Sequence library
│       ├── ahb_agent.svh                   — Agent wrapper
│       └── ahb_env.svh                     — Environment
├── examples/
│   └── uvm_back2back/                      — Self-contained demo
│       ├── tb/      top.sv, tb_pkg.sv      — Testbench + tests
│       └── sim/     run scripts, filelists  — Simulator scripts
└── docs/                                    — VIP-specific documentation
```

## Protocol Mode Selection

The VIP supports runtime switching between AHB-Lite and AHB Full modes:

| Plusarg | Effect |
|---------|--------|
| `+AHB_MODE=AHB_LITE` | AHB-Lite mode (default) — single master, no arbitration |
| `+AHB_MODE=AHB_FULL` | AHB Full mode — multi-master semantics |

## Agent Configuration

The `ahb_agent_cfg` class provides extensive configuration knobs:

```systemverilog
class ahb_agent_cfg extends uvm_object;
  // Role
  bit is_master = 1;               // 1 = master agent, 0 = slave agent
  virtual ahb_if vif;              // Interface handle

  // Burst control
  bit allow_bursts = 1;            // Enable burst transfers
  bit allow_wrap   = 1;            // Allow WRAP burst types
  int max_incr_len = 16;           // Max INCR burst length

  // Wait state control (slave)
  bit allow_wait_states = 1;       // Enable HREADYOUT stalling
  int min_wait = 0;                // Minimum wait state cycles
  int max_wait = 4;                // Maximum wait state cycles

  // Error injection
  bit error_injection_enable = 0;  // Enable HRESP=ERROR
  logic [ADDR_W-1:0] error_addr_lo;// Error range start
  logic [ADDR_W-1:0] error_addr_hi;// Error range end

  // Monitor
  bit monitor_enable = 1;          // Enable passive monitor
  bit coverage_enable = 1;         // Enable functional coverage
endclass
```

## Interface Signals

The `ahb_if` interface supports the full AHB signal set:

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `HCLK` | 1 | Input | Bus clock |
| `HRESETn` | 1 | Input | Active-low reset |
| `HADDR` | ADDR_W | Master→Slave | Transfer address |
| `HTRANS` | 2 | Master→Slave | Transfer type (IDLE/BUSY/NONSEQ/SEQ) |
| `HWRITE` | 1 | Master→Slave | Write select |
| `HSIZE` | 3 | Master→Slave | Transfer size |
| `HBURST` | 3 | Master→Slave | Burst type |
| `HWDATA` | DATA_W | Master→Slave | Write data |
| `HRDATA` | DATA_W | Slave→Master | Read data |
| `HRESP` | 1 | Slave→Master | Transfer response (OKAY/ERROR) |
| `HREADYOUT` | 1 | Slave→Master | Slave ready signal |
| `HREADY` | 1 | Multiplexed | Transfer done (shared bus) |

## Error Response Protocol

The AHB VIP implements the AMBA-compliant two-cycle error response:

1. **Cycle 1:** `HREADYOUT=0`, `HRESP=ERROR` — stall the master
2. **Cycle 2:** `HREADYOUT=1`, `HRESP=ERROR` — complete the error transfer

Error injection is configured per address range:

```systemverilog
// Enable error responses for addresses 0x100–0x1FF
cfg.error_injection_enable = 1;
cfg.error_addr_lo = 16'h0100;
cfg.error_addr_hi = 16'h01FF;
```

## Sequence Library

| Sequence | Description |
|----------|-------------|
| `ahb_single_rw_seq` | Single read/write transaction |
| `ahb_incr_burst_seq` | INCR burst (configurable length) |
| `ahb_wrap_burst_seq` | WRAP4/WRAP8/WRAP16 bursts |
| `ahb_back_to_back_seq` | Continuous back-to-back transfers |
| `ahb_random_stress_seq` | Randomized stress traffic |

## Test Suite

The example testbench includes 8 regression tests:

| Test | Description |
|------|-------------|
| `ahb_smoke_test` | Basic connectivity and single transfers |
| `ahb_single_read_write_test` | Single read and write verification |
| `ahb_wait_state_test` | Wait state insertion (0–8 cycles) |
| `ahb_incr_burst_test` | INCR burst transfers |
| `ahb_wrap_burst_test` | WRAP burst transfers |
| `ahb_back_to_back_test` | 1000 back-to-back transactions |
| `ahb_error_response_test` | Error injection at 100% in address range |
| `ahb_random_stress_test` | 2000 randomized transactions |

## Protocol Assertions

Built-in SVA checks include:

- HTRANS stability during wait states
- HADDR/HWRITE/HSIZE/HBURST stability during stalls
- HREADY/HREADYOUT protocol compliance
- Reset behavior verification

## Debug Plusargs

| Plusarg | Effect |
|---------|--------|
| `+KVIPS_WAVES` | Enable VCD waveform dump |
| `+UVM_VERBOSITY=UVM_HIGH` | Increase monitor verbosity |
| `+AHB_MODE=AHB_LITE` | Select AHB-Lite mode |
| `+AHB_MODE=AHB_FULL` | Select AHB Full mode |

## Resources

- [AHB Source Code](https://github.com/kiranreddi/kvips/tree/main/ahb)
- [Example Testbench](https://github.com/kiranreddi/kvips/tree/main/ahb/examples/uvm_back2back)
- [Getting Started Guide]({{ '/docs/getting-started/' | relative_url }})
- [Best Practices]({{ '/docs/best-practices/' | relative_url }})
