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

## APB (APB3/APB4) VIP status

Implemented under `kvips/apb/` as a single-image APB3/APB4 VIP with runtime mode switch (`+APB_PROTOCOL=APB3|APB4`).

**Docs**
- `kvips/apb/docs/integration_guide.md`
- `kvips/apb/docs/supported_features.md`
- `kvips/apb/docs/assertions.md`
- `kvips/apb/docs/testplan.md`

**Example**
- `kvips/apb/examples/uvm_back2back/`

**Assertions**
- Setup/access sequencing, stability during wait-states, known-value checks, APB4-only rules (runtime gated).

**Regression targets**
- Questa: `questa/2025_3_2`
- VCS: `vcs/2025.06_1`
- Xcelium: `xcelium/25.03.007`

**Next improvements (incremental)**
- Add additional examples (master-only, slave-only, passive monitor)
- Expand directed sequences/tests (more corner cases)

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
