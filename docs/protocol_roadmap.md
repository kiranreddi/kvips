---
layout: default
title: Protocol VIP Roadmap (Detailed)
permalink: /docs/protocol-roadmap/
---

# Protocol VIP Roadmap (Detailed)

This document is the engineering plan for adding new protocol VIPs to KVIPS with the **same “EDA-quality” structure** as `axi4/` (docs, examples, assertions, regression scripts, and portable UVM).

## Context from real integration (NIC bring-up)

- The NIC DUT integrated so far (`nic400_1`) is an ARM NIC-400 **AXI-only** instance (no APB/AHB ports exposed in this configuration).
- Even when the target DUT is AXI-only, the **next SoC blocks** usually introduce APB/AHB (CSR access) and peripheral links (I2C/UART), so KVIPS should standardize those VIPs now.

## Standard directory template (apply to every new VIP)

Create new VIPs using the same top-level structure as `axi4/`:

```
<proto>/
├── docs/
│   ├── directory_structure.md
│   ├── integration_guide.md
│   ├── supported_features.md
│   ├── assertions.md
│   ├── testplan.md
│   ├── user_guide.md
│   ├── avery_gap_analysis.md
│   └── questa_gap_analysis.md
├── examples/
│   └── uvm_back2back/
│       ├── tb/
│       └── sim/
└── sv/
    ├── if/
    ├── pkg/
    ├── uvm/
    └── assertions/
```

All VIPs should support:
- Multiple instances in a single simulation (no global singletons).
- Optional assertions/checkers with runtime disable switches.
- Transaction recording hooks (portable UVM TR; simulator-specific waveform is optional).
- A small set of “golden” examples and a documented regression flow.

## Gap-driven development workflow (Avery/QVIP parity)

For each protocol:
1. Create `docs/supported_features.md` and `docs/testplan.md` first (spec-mapped checklist).
2. Create `docs/avery_gap_analysis.md` and `docs/questa_gap_analysis.md`:
   - List features present in the reference VIPs (Avery/QVIP) that KVIPS must match.
   - Mark each item as: `missing`, `partial`, `implemented`, and link to the test(s) that prove it.
3. Implement features + add tests until gap analyses are all `implemented` (or clearly documented limitations).

## APB (APB3/APB4) VIP plan

**Core features**
- APB3 + APB4 signals: `PADDR`, `PSELx`, `PENABLE`, `PWRITE`, `PWDATA`, `PRDATA`, `PREADY`, `PSLVERR`, `PPROT`, `PSTRB`.
- Configurable wait states and `PREADY` behavior (fixed and randomized).
- Error response injection (`PSLVERR`) with address-range configuration.
- Optional functional coverage for address ranges, read/write mix, wait-states.

**Assertions**
- Correct APB state machine sequencing (setup/access phases).
- Stable address/control during access.
- `PSEL`/`PENABLE` legality and reset behavior.

**UVM components**
- `apb_agent_cfg`, `apb_item`, master/slave drivers, monitor, sequencer.
- Simple memory-mapped slave model (byte-addressable) with base mapping (same pattern as AXI4 `slave_mem_base`).
- Scoreboard: write-derived expected vs read observed.

**Tests (examples/uvm_back2back)**
- Smoke: basic read/write.
- Wait-state sweep: 0..N cycles.
- Error injection: SLVERR on reads/writes in a range.
- Randomized stress: address/data/byte-enables (APB4).

## AHB (AHB-Lite / AHB) VIP plan

**Core features**
- Address/control phase + data phase modeling, bursts, `HTRANS`, `HBURST`, `HSIZE`, `HWRITE`.
- `HREADY`/`HRESP` backpressure and error modeling.
- Optional split/retry support (if targeting full AHB; otherwise document “AHB-Lite only”).

**Assertions**
- Protocol phase legality, stable control during wait-states.
- Burst address progression rules.

**Tests**
- Single/burst read/write, wait-state stress.
- Error injection and recovery behavior.

## I2C VIP plan

**Core features**
- Master VIP: START/STOP, address + R/W, ACK/NACK, repeated start.
- Slave VIP: programmable address, ACK/NACK behavior, clock stretching.
- Support Standard/Fast/Fast+ timing parameterization (digital cycle-based modeling).
- Optional multi-master arbitration modeling (at least detection; full arbitration optional with clear doc).

**Assertions**
- SDA stability rules relative to SCL, START/STOP legality.
- ACK sampling timing checks (cycle-based).

**Tests**
- Read/write register model style sequences (typical SoC use).
- Clock stretching and NACK/error paths.

## UART VIP plan

**Core features**
- Configurable baud rate (cycle-based), data bits, parity, stop bits.
- TX/RX monitor + decoder, optional BFMs for driving bytes/frames.
- Error injection: parity error, framing error, break.

**Assertions**
- Frame structure checks, stop-bit timing, parity correctness.

**Tests**
- Loopback (TX->RX), random stream, parity/framing error cases.

## Deliverable quality bar (same as AXI4)

For each protocol VIP, do not “declare done” until:
- `docs/testplan.md` is complete and mapped to tests.
- Example regression runs cleanly on Questa/VCS/Xcelium (and Verilator-lint where applicable).
- Assertions are present, documented, and have disable switches.
- User guide shows minimal integration snippets and debug knobs.

