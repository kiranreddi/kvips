# Assertions (AHB VIP)

Assertions are bound into `ahb_if` via `kvips/ahb/sv/assertions/ahb_if_sva.svh`.

## Runtime switches

- Disable all: `+KVIPS_AHB_ASSERT_OFF`
- Disable known/X checks: `+KVIPS_AHB_ASSERT_KNOWN_OFF`
- Disable strict checks: `+KVIPS_AHB_ASSERT_STRICT_OFF`

Mode selection:
- `+AHB_MODE=AHB_LITE` (default)
- `+AHB_MODE=AHB_FULL`

## Implemented properties (v0.1)

- Control stability during stall: when `HREADY==0`, hold `HADDR/HTRANS/HWRITE/HSIZE/HBURST/HPROT/HSEL` stable
- Write data stability during stall (strict): when `HREADY==0`, hold `HWDATA` stable
- BUSY disallowed by default (strict): rejects `HTRANS==BUSY`
- AHB-Lite response legality: for 2-bit `HRESP`, disallow RETRY/SPLIT in LITE mode
- Known/X checks (optional): no X on key control fields during active transfers

## Notes

These checks focus on the most common integration and VIP failure modes (stall stability + X-pollution). More strict burst/address progression assertions are planned.

