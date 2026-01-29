# AXI4 VIP Test Plan (initial)

This document maps **implemented** AXI4 VIP functionality to runnable tests and highlights **gaps** to implement next.

## Conventions
- VIP: `kvips/axi4/sv/pkg/axi4_uvm_pkg.sv`
- Example regression: `kvips/axi4/examples/uvm_back2back/`
- All tests are self-checking via `axi4_scoreboard` (byte-accurate expected vs observed reads).

## Implemented (covered)

### Channels / handshakes
- AW/W/B: VALID/READY handshakes, burst writes
- AR/R: VALID/READY handshakes, burst reads
- VALID stability while stalled: SVA in `kvips/axi4/sv/assertions/axi4_if_sva.svh`

### Bursts
- INCR: supported
- FIXED: supported (addressing in slave + scoreboard via `axi4_beat_addr`)
- WRAP: supported (addressing in slave + scoreboard via `axi4_beat_addr`)
- LEN: INCR 1..256 beats; FIXED/WRAP 1..16 beats (AMBA4 legality enforced in `axi4_item` constraints)
- SIZE: full-width and narrow sizes (example tests use 1B..bus-width)

### Narrow transfers / strobes
- WSTRB honored by slave memory model and scoreboard (lane-aligned to bus word)

### Backpressure / latency
- Slave READY and response latency knobs (`ready_min/max`, `resp_min/max`)

### Multiple outstanding / reordering / interleaving
- Master pipelined mode with configurable outstanding depth
- Slave response scheduling knobs (B reordering, R beat interleaving across IDs)

### Exclusive accesses (AXI4 LOCK)
- Slave reservation tracking (per-ID) with EXOKAY on successful exclusive read/write
- Failed exclusive writes do not update memory (self-checked)

### Error response injection
- Address-range based `SLVERR/DECERR` injection for reads and/or writes
- Error writes do not update memory (self-checked)

## Regression tests
| Feature area | Test | Where |
|---|---|---|
| Basic write+readback | `axi4_b2b_test` (alias of smoke) | `kvips/axi4/examples/uvm_back2back/tb/tb_pkg.sv` |
| Burst types (INCR/FIXED/WRAP) | `axi4_b2b_burst_types_test` | `kvips/axi4/examples/uvm_back2back/tb/tb_pkg.sv` |
| Backpressure | `axi4_b2b_backpressure_test` | `kvips/axi4/examples/uvm_back2back/tb/tb_pkg.sv` |
| SIZE+lane sweep (directed narrow/full) | `axi4_b2b_lane_sweep_test` | `kvips/axi4/examples/uvm_back2back/tb/tb_pkg.sv` |
| Corner cases (4KB edge, length extremes) | `axi4_b2b_corner_case_test` | `kvips/axi4/examples/uvm_back2back/tb/tb_pkg.sv` |
| Randomized features (sizes/len/burst/id) | `axi4_b2b_randomized_features_test` | `kvips/axi4/examples/uvm_back2back/tb/tb_pkg.sv` |
| Multiple outstanding + response reordering/interleaving | `axi4_b2b_pipelined_outstanding_test` | `kvips/axi4/examples/uvm_back2back/tb/tb_pkg.sv` |
| Master-side RREADY backpressure (pipelined) | `axi4_b2b_pipelined_rready_backpressure_test` | `kvips/axi4/examples/uvm_back2back/tb/tb_pkg.sv` |
| Exclusive: success path | `axi4_b2b_exclusive_basic_test` | `kvips/axi4/examples/uvm_back2back/tb/tb_pkg.sv` |
| Exclusive: fail path (invalidation) | `axi4_b2b_exclusive_fail_test` | `kvips/axi4/examples/uvm_back2back/tb/tb_pkg.sv` |
| Exclusive: configurable restriction behavior | `axi4_b2b_exclusive_illegal_test` | `kvips/axi4/examples/uvm_back2back/tb/tb_pkg.sv` |
| Error injection: write DECERR | `axi4_b2b_error_write_test` | `kvips/axi4/examples/uvm_back2back/tb/tb_pkg.sv` |
| Error injection: read DECERR | `axi4_b2b_error_read_test` | `kvips/axi4/examples/uvm_back2back/tb/tb_pkg.sv` |
| INCR bursts up to 256 beats | `axi4_b2b_incr_256beat_test` | `kvips/axi4/examples/uvm_back2back/tb/tb_pkg.sv` |
| Master delay/backpressure knobs | `axi4_b2b_delay_stress_test` | `kvips/axi4/examples/uvm_back2back/tb/tb_pkg.sv` |
| Concurrent reads+writes | `axi4_b2b_concurrent_rw_test` | `kvips/axi4/examples/uvm_back2back/tb/tb_pkg.sv` |

## Feature-to-test mapping (summary)
| AXI feature | Covered by |
|---|---|
| AW/AR/W/R/B handshakes | `axi4_b2b_test`, `axi4_b2b_backpressure_test` |
| Burst types (INCR/FIXED/WRAP) | `axi4_b2b_burst_types_test`, `axi4_b2b_randomized_features_test` |
| LEN 1..16 beats | `axi4_b2b_backpressure_test`, `axi4_b2b_randomized_features_test` |
| SIZE 1B..bus-width | `axi4_b2b_lane_sweep_test`, `axi4_b2b_randomized_features_test` |
| Narrow write strobes | `axi4_b2b_lane_sweep_test`, `axi4_b2b_randomized_features_test` |
| 4KB “edge of window” cases | `axi4_b2b_corner_case_test` |
| ID propagation (no interleaving) | `axi4_b2b_randomized_features_test` |
| Outstanding + B reorder + R interleave | `axi4_b2b_pipelined_outstanding_test` |
| Master RREADY backpressure | `axi4_b2b_pipelined_rready_backpressure_test` |
| Exclusive success/fail semantics | `axi4_b2b_exclusive_basic_test`, `axi4_b2b_exclusive_fail_test` |
| Exclusive configurable restriction | `axi4_b2b_exclusive_illegal_test` |
| Error injection (write/read) | `axi4_b2b_error_write_test`, `axi4_b2b_error_read_test` |
| INCR up to 256 beats | `axi4_b2b_incr_256beat_test` |
| Master delays + read backpressure | `axi4_b2b_delay_stress_test` |
| Concurrent read/write traffic | `axi4_b2b_concurrent_rw_test` |
| Basic protocol SVA (hold/size) | Always-on unless `+KVIPS_AXI4_ASSERT_OFF` |

## Not implemented yet (gaps)
These are AXI4 features not yet modeled/checked by this initial VIP:
- Full AXI4 protection/cache/QoS/region semantics beyond signal presence
- Low-power / clock gating considerations
- Protocol corner cases (additional unaligned/addressing corner coverage beyond current directed set)
- Comprehensive SVA parity vs vendor VIPs (KVIPS includes a starter + stateful set; extend as needed)
