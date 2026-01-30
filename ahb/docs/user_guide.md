# User guide (AHB VIP)

## Configuration (`ahb_cfg`)

Key knobs:
- `mode`: `AHB_MODE_LITE` or `AHB_MODE_FULL` (also settable via `+AHB_MODE=...`)
- Wait states (slave): `allow_wait_states`, `min_wait`, `max_wait`
- Error injection (slave): `err_enable`, `err_addr_lo`, `err_addr_hi`, `err_pct`
- Burst policy (master): `allow_bursts`, `allow_wrap`, `max_incr_len`
- Debug:
  - `trace_enable` (monitor prints concise transaction logs)
  - `coverage_enable` (monitor coverage sampling)

## Debug workflow

Recommended bring-up:
1. Start with `ahb_smoke_test` (SINGLE transfers)
2. Enable stalls: `ahb_wait_state_test`
3. Enable burst stress: `ahb_back_to_back_test` / `ahb_random_stress_test`

Useful knobs:
- `+UVM_VERBOSITY=UVM_HIGH` for more UVM messaging
- `+VIP_TRACE` to enable transaction printing in the monitor/config

## Scoreboard expectations

The scoreboard is a monitor-based reference model:
- Writes update expected byte-addressed memory using `HSIZE` and address lane mapping.
- Reads compare returned `HRDATA` against expected.
- Error responses skip read comparison.

Use `+KVIPS_AHB_SB_WARN_UNINIT` to highlight reads from unwritten locations.

