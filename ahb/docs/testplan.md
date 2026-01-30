# Testplan (AHB VIP)

This file maps AHB features to example tests in `kvips/ahb/examples/uvm_back2back`.

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

## Coverage targets (v0.1)

Monitor coverpoints:
- Read vs write
- Size bins (8/16/32/64)
- Burst bins (SINGLE/INCR*/WRAP*)
- Stall bins (0/1/2-3/4-7/8+)
- Response bins (OKAY/ERROR)
- Crosses: (rw x size), (burst x stall)

