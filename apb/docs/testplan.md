# Testplan (APB3/APB4)

This testplan maps example tests to protocol features. Example tests live under `kvips/apb/examples/uvm_back2back/`.

## Bring-up / sanity
- `apb_b2b_reset_sanity_test`
  - Reset behavior and idle stability
- `apb_b2b_smoke_test`
  - Deterministic write/readback sweep (scoreboard + sequence check)

## Protocol behavior
- `apb_b2b_wait_state_test`
  - Slave inserts wait-states; master holds control stable; monitor tracks wait cycles
- `apb_b2b_back_to_back_test`
  - Continuous transfers (no forced idle) by setting `drop_psel_between=0`
- `apb_b2b_error_injection_test`
  - PSLVERR injection by address range; scoreboard disabled to avoid expected-error reads

## APB4-specific
- `apb_b2b_apb4_strobe_mask_test`
  - Directed `PSTRB` masked write update + readback check
- `apb_b2b_apb4_pprot_variation_test`
  - Randomizes `PPROT` values during traffic (coverage exercise)

## Stress / regression
- `apb_b2b_random_stress_test`
  - Large randomized mix (reads/writes, wait-states, APB4 extras when enabled)

## Modes
- APB4 mode: `+APB_PROTOCOL=APB4` (default)
- APB3 mode: `+APB_PROTOCOL=APB3` (APB4-only tests auto-skip)

