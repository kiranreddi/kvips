---
layout: default
title: APB Verification IP — KVIPS
description: Complete AMBA APB3 and APB4 verification IP with UVM agents, protocol assertions, scoreboard, and example testbench.
permalink: /docs/apb-vip/
---

# APB3 / APB4 Verification IP

<div class="badge-row-lg">
  <span class="badge badge-green">Stable v1.0</span>
  <span class="badge badge-blue">AMBA 4.0</span>
  <span class="badge badge-gray">SystemVerilog + UVM</span>
</div>

## Overview

The KVIPS APB VIP provides a complete AMBA APB verification solution supporting both **APB3** and **APB4** in a single compiled image with runtime protocol switching. Ideal for register-level access testing and system-level integration.

Key capabilities:

- **Master agent** — drives SETUP→ACCESS state machine for reads and writes
- **Slave agent** — reactive responder with built-in byte-addressed memory model
- **Passive monitor** — captures transactions with functional coverage
- **Protocol assertions (SVA)** — comprehensive APB protocol checking
- **Scoreboard** — expected vs. observed data integrity verification
- **8 pre-built regression tests** — smoke, wait states, APB4 features, stress

## Quick Start

```bash
# Clone repository
git clone https://github.com/kiranreddi/kvips.git && cd kvips

# Run APB smoke test (any simulator)
cd apb/examples/uvm_back2back/sim
./run_questa.sh +UVM_TESTNAME=apb_b2b_smoke_test

# Run on Verilator (no commercial license needed)
cd ../..
make verilator TEST=apb_b2b_smoke_test
```

## Directory Structure

```
kvips/apb/
├── sv/
│   ├── if/          apb_if.sv              — Parameterized interface
│   ├── assertions/  apb_if_sva.svh         — Protocol SVA
│   ├── pkg/         apb_types_pkg.sv       — Types and enums
│   │                apb_uvm_pkg.sv         — UVM package
│   └── uvm/
│       ├── apb_transaction.svh             — Transaction item
│       ├── apb_cfg.svh                     — Agent configuration
│       ├── apb_sequencer.svh               — Sequencer
│       ├── apb_master_driver.svh           — Master BFM
│       ├── apb_slave_driver.svh            — Slave BFM + memory model
│       ├── apb_monitor.svh                 — Monitor + coverage
│       ├── apb_scoreboard.svh              — Data integrity checker
│       ├── apb_sequences.svh               — Sequence library
│       ├── apb_agent.svh                   — Agent wrapper
│       └── apb_env.svh                     — Environment
├── examples/
│   └── uvm_back2back/                      — Self-contained demo
│       ├── tb/      top.sv, tb_pkg.sv      — Testbench + tests
│       └── sim/     run scripts            — All 4 simulators
└── docs/                                    — VIP documentation
```

## Protocol Mode Selection

Runtime protocol selection between APB3 and APB4:

| Plusarg | Effect |
|---------|--------|
| `+APB_PROTOCOL=APB3` | APB3 mode — no PSTRB or PPROT |
| `+APB_PROTOCOL=APB4` | APB4 mode (default) — PSTRB and PPROT enabled |

## Agent Configuration

```systemverilog
class apb_agent_cfg extends uvm_object;
  // Role
  bit is_master = 1;                // 1 = master, 0 = slave
  virtual apb_if vif;               // Interface handle

  // Protocol version
  apb_protocol_e protocol = APB4;   // APB3 or APB4

  // Wait state control (slave)
  bit allow_wait_states = 0;        // Enable PREADY stalling
  int min_wait = 0;                 // Min wait cycles
  int max_wait = 4;                 // Max wait cycles

  // Error injection
  bit error_injection_enable = 0;   // Enable PSLVERR
  logic [ADDR_W-1:0] error_addr_lo; // Error range start
  logic [ADDR_W-1:0] error_addr_hi; // Error range end

  // Monitor
  bit monitor_enable = 1;           // Enable passive monitor
  bit coverage_enable = 1;          // Enable functional coverage
endclass
```

## APB Transfer Protocol

The APB protocol uses a two-phase state machine:

```
IDLE → SETUP → ACCESS → SETUP (back-to-back)
                    ↓
               IDLE (if no more transfers)
```

**SETUP Phase (1 cycle):**
- PSEL asserted, PENABLE deasserted
- Address (PADDR), write (PWRITE), write data (PWDATA) driven

**ACCESS Phase (1+ cycles):**
- PENABLE asserted
- Slave responds with PREADY (can insert wait states)
- PRDATA valid on reads, PSLVERR indicates errors

## Interface Signals

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `PCLK` | 1 | Input | Bus clock |
| `PRESETn` | 1 | Input | Active-low reset |
| `PSEL` | N_SEL | Master→Slave | Slave select (per-slave) |
| `PENABLE` | 1 | Master→Slave | Transfer enable (ACCESS phase) |
| `PWRITE` | 1 | Master→Slave | Write select |
| `PADDR` | ADDR_W | Master→Slave | Transfer address |
| `PWDATA` | DATA_W | Master→Slave | Write data |
| `PRDATA` | DATA_W | Slave→Master | Read data |
| `PREADY` | 1 | Slave→Master | Slave ready (wait state control) |
| `PSLVERR` | 1 | Slave→Master | Slave error response |
| `PSTRB` | DATA_W/8 | Master→Slave | Write strobes (APB4 only) |
| `PPROT` | 3 | Master→Slave | Protection type (APB4 only) |

## APB4 Features

### Write Strobes (PSTRB)

APB4 adds byte-level write enables, allowing partial writes:

```systemverilog
// Write only bytes 0 and 2 of a 32-bit word
apb_item tr = apb_item::type_id::create("tr");
tr.addr  = 32'h0000_0100;
tr.write = 1;
tr.data  = 32'hDEAD_BEEF;
tr.strb  = 4'b0101;  // Only bytes 0 and 2 written
```

### Protection (PPROT)

APB4 PPROT signal bits:

| Bit | Value=0 | Value=1 |
|-----|---------|---------|
| [0] | Normal access | Privileged access |
| [1] | Secure access | Non-secure access |
| [2] | Data access | Instruction access |

## Sequence Library

| Sequence | Description |
|----------|-------------|
| `apb_single_write_seq` | Single write transaction |
| `apb_single_read_seq` | Single read transaction |
| `apb_write_read_seq` | Write then read-back verification |
| `apb_back_to_back_seq` | Continuous PSEL without idle gaps |
| `apb_random_stress_seq` | Randomized mixed traffic |

## Test Suite

8 regression tests are included:

| Test | Description |
|------|-------------|
| `apb_b2b_reset_sanity_test` | Reset deassert sanity check |
| `apb_b2b_smoke_test` | 10 basic read/write transactions |
| `apb_b2b_wait_state_test` | Wait states 0–8 cycles, 200 transactions |
| `apb_b2b_back_to_back_test` | 500 transactions without PSEL drop |
| `apb_b2b_error_injection_test` | 100% PSLVERR in address range |
| `apb_b2b_apb4_strobe_mask_test` | PSTRB byte-lane masking |
| `apb_b2b_apb4_pprot_variation_test` | All PPROT encoding variations |
| `apb_b2b_random_stress_test` | 2000 random transactions |

## Protocol Assertions

Built-in SVA protocol checks:

- PSEL → PENABLE sequencing (SETUP must precede ACCESS)
- PENABLE only active with PSEL
- Address/control stability during ACCESS phase
- PSTRB only valid on writes (APB4)
- No X/Z on control signals during active transfers
- Reset behavior validation

## Debug Plusargs

| Plusarg | Effect |
|---------|--------|
| `+KVIPS_WAVES` | Enable VCD waveform dump |
| `+APB_PROTOCOL=APB3` | Switch to APB3 mode |
| `+APB_PROTOCOL=APB4` | Switch to APB4 mode (default) |
| `+KVIPS_APB_LOG_TXNS` | Enable transaction logging |
| `+UVM_VERBOSITY=UVM_HIGH` | Increase verbosity |

## Resources

- [APB Source Code](https://github.com/kiranreddi/kvips/tree/main/apb)
- [Example Testbench](https://github.com/kiranreddi/kvips/tree/main/apb/examples/uvm_back2back)
- [Getting Started Guide]({{ '/docs/getting-started/' | relative_url }})
- [Best Practices]({{ '/docs/best-practices/' | relative_url }})
