# Assertions (SVA)

Assertions are interface-bound via `kvips/apb/sv/if/apb_if.sv` which includes:
- `kvips/apb/sv/assertions/apb_if_sva.svh`

## Enable/disable switches
- Disable all assertions: `+KVIPS_APB_ASSERT_OFF`
- Disable X/known-value checks: `+KVIPS_APB_ASSERT_KNOWN_OFF`
- Disable strict checks: `+KVIPS_APB_ASSERT_STRICT_OFF`

## Protocol mode interaction
- APB4-only checks are enabled when `+APB_PROTOCOL=APB4` (default).
- APB4-only checks are disabled when `+APB_PROTOCOL=APB3`.

## What is checked
- `PENABLE` only asserted when `PSEL` is asserted
- Setup precedes access (checked on entry into ACCESS; wait-states are allowed)
- Stability during wait-states (`PADDR/PWRITE/PWDATA/PSEL/PPROT/PSTRB` stable while `PENABLE && !PREADY`)
- Optional known-value checks on key controls during transfers
- Optional strict `PSEL` onehot0 check
- APB4-only: `PSTRB != 0` on writes, `PPROT` known when selected

