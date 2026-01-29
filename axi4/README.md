# KVIPS AXI4 VIP (UVM + SVA)

UVM-based AXI4 (full) VIP with:
- **Master** and **Slave** agents (BFMs) + passive **monitor**
- Built-in **memory model** slave for back-to-back demos
- **Scoreboard** (write-derived expected vs observed reads)
- **Assertions (SVA)** with runtime switches
- Optional **transaction recording** (UVM TR) and lightweight **performance stats**

Designed for IEEE 1800 SystemVerilog + Accellera UVM (validated on UVM-1.1d and UVM-1.2).

## Supported simulators (validated versions)
- Siemens Questa: `2025_3_2`
- Synopsys VCS: `2025.06_1`
- Cadence Xcelium: `25.03.007`

## Quick start (back-to-back demo)
See `kvips/axi4/examples/uvm_back2back/README.md`.

Common single-test usage (from repo root):
- Questa: `kvips/axi4/examples/uvm_back2back/sim/run_questa.sh +UVM_TESTNAME=axi4_b2b_test`
- VCS: `kvips/axi4/examples/uvm_back2back/sim/run_vcs.sh +UVM_TESTNAME=axi4_b2b_test`
- Xcelium: `kvips/axi4/examples/uvm_back2back/sim/run_xcelium.sh +UVM_TESTNAME=axi4_b2b_test`

Regression list:
- `kvips/axi4/examples/uvm_back2back/sim/tests_questa.list`

## Repository layout
- `kvips/axi4/sv/if/` : `axi4_if` interface + modports + included SVA
- `kvips/axi4/sv/pkg/` : `axi4_types_pkg`, `axi4_uvm_pkg`
- `kvips/axi4/sv/uvm/` : agent, drivers, monitor, scoreboard, sequences
- `kvips/axi4/sv/assertions/` : `axi4_if_sva.svh` (included in `axi4_if`)
- `kvips/axi4/examples/` : runnable demos (Questa/VCS/Xcelium scripts)
- `kvips/axi4/docs/` : user guide, testplan, assertions, supported features, gap analyses

## Key capabilities
- **Bursts**: INCR/FIXED/WRAP; legality enforced for generated items (INCR up to 256 beats; FIXED/WRAP up to 16; WRAP lengths 2/4/8/16)
- **4KB rule**: generation avoids crossing; SVA checks enforce no 4KB crossing
- **Multiple outstanding**: optional pipelined master with per-direction outstanding limits; monitor associates by **BID/RID** (supports slave B reordering and R interleaving)
- **Exclusive accesses (AxLOCK)**: reservation tracking + EXOKAY/OKAY behavior (configurable max-bytes)
- **Error injection**: address-range based SLVERR/DECERR injection for reads and/or writes
- **Delays/backpressure**: master AW/AR delay, W beat gaps, randomized RREADY; slave ready/response latency knobs
- **Stats** (optional): cycle/handshake/stall counters, outstanding max, basic latency min/mean/max

## Debug knobs
Plusargs (demo-friendly):
- `+VIP_TRACE` : verbose driver/monitor prints (UVM_INFO)
- `+VIP_TR` : UVM transaction recording hooks from monitor
- `+VIP_STATS` : enable monitor stats summary
- `+VIP_PIPE` / `+VIP_MAX_OUTS=<n>` : enable pipelined master and set outstanding

Assertions:
- Disable all: `+KVIPS_AXI4_ASSERT_OFF`
- Enable X/Z checks: `+KVIPS_AXI4_ASSERT_KNOWN`
- Disable burst legality: `+KVIPS_AXI4_ASSERT_BURST_OFF`
- Disable exclusive restrictions: `+KVIPS_AXI4_ASSERT_EXCL_OFF`

Scoreboard:
- Disable: `+KVIPS_AXI4_SB_OFF`
- Warn on reads of unwritten bytes: `+KVIPS_AXI4_SB_WARN_UNINIT`

## Documentation
- `kvips/axi4/docs/user_guide.md`
- `kvips/axi4/docs/integration_guide.md`
- `kvips/axi4/docs/supported_features.md`
- `kvips/axi4/docs/testplan.md`
- `kvips/axi4/docs/assertions.md`
- Gap analyses:
  - `kvips/axi4/docs/avery_gap_analysis.md`
  - `kvips/axi4/docs/questa_gap_analysis.md`
