# Testplan (AHB VIP)

This file maps AHB features to the self-checking examples in
`kvips/ahb/examples/uvm_back2back` and the signal-level DUT flow in
`kvips/ahb/examples/uvm_dut`.

## Tests

| Test | Purpose | Features covered |
|------|---------|------------------|
| `ahb_smoke_test` | Basic sanity | SINGLE, read/write mix, basic scoreboard |
| `ahb_single_read_write_test` | Deterministic SINGLE traffic | `HSIZE` variation, data integrity |
| `ahb_wait_state_test` | Stall correctness | `HREADY` stalls, stability, scoreboard under stalls |
| `ahb_incr_burst_test` | Incrementing bursts | INCR4/8/16, sequential addressing |
| `ahb_wrap_burst_test` | Wrap bursts | WRAP4/8/16 address wrap behavior |
| `ahb_back_to_back_test` | Throughput | back-to-back transfers, mixed burst/size, stress |
| `ahb_error_response_test` | Error handling | ERROR responses via address-range injection |
| `ahb_random_stress_test` | Coverage-driven stress | random mix of size/burst/rw, occasional lock |
| `ahb_busy_test` | BUSY control phase | BUSY between INCR16 beats, burst-state preservation, HNONSEC transport |
| `ahb_boundary_test` | Boundary legality | aligned INCR4 ending exactly at a 1KB boundary |
| `ahb_security_policy_test` | AHB5 security policy | deny non-secure access and allow secure access through `ahb_security_policy` |
| `ahb_big_endian_test` | Byte-lane mapping | big-endian reference memory and scoreboard readback |
| `ahb_legality_test` | Negative/unit legality | misalignment, bus-width, 1KB crossing, and legal-transfer checks |
| `ahb_full_retry_test` | AHB Full response | directed two-cycle RETRY response (`+AHB_MODE=AHB_FULL`) |
| `ahb_full_split_test` | AHB Full response | directed two-cycle SPLIT response (`+AHB_MODE=AHB_FULL`) |
| `ahb_reset_recovery_test` | Reset robustness | reset asserted during active traffic, pipeline flush/recovery |

## Coverage targets (v0.1)

## RTL-DUT integration gate

The `uvm_dut` list adds executable evidence against a synthesizable RAM
responder: `ahb_dut_smoke_test`, `ahb_dut_incr_burst_test`,
`ahb_dut_wrap_burst_test`, `ahb_dut_wait_state_test`, `ahb_dut_stress_test`,
and `ahb_dut_full_mode_test`. Commercial regressions require nonzero writes
and reads, zero responder errors, zero scoreboard mismatches, and observed
stall cycles for the wait-state test. Verilator runs the same gate in CI; it
is not counted as commercial simulator equivalence.

Monitor coverpoints:
- Read vs write
- Size bins (8/16/32/64)
- Burst bins (SINGLE/INCR*/WRAP*)
- Stall bins (0/1/2-3/4-7/8+)
- Response bins (OKAY/ERROR; RETRY/SPLIT are directed Full-mode bins)
- Crosses: (rw x size), (burst x stall)
- Security policy deny/allow outcome
- Endian byte-lane readback
- Master metadata transport (`HMASTER`/lock) is available for fabric integrations; arbitration is not claimed
