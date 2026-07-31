# Assertions (AHB VIP)

Assertions are bound into `ahb_if` via `kvips/ahb/sv/assertions/ahb_if_sva.svh`.

## Runtime switches

- Disable all: `+KVIPS_AHB_ASSERT_OFF`
- Disable known/X checks: `+KVIPS_AHB_ASSERT_KNOWN_OFF`
- Disable strict checks: `+KVIPS_AHB_ASSERT_STRICT_OFF`
- When strict checks are enabled, allow the directed BUSY example with `+KVIPS_AHB_BUSY_ON`

Mode selection:
- `+AHB_MODE=AHB_LITE` (default)
- `+AHB_MODE=AHB_FULL`

## Implemented properties (v0.1)

- Control stability during an extended stall: when `HREADY==0` for consecutive cycles, hold `HADDR/HTRANS/HWRITE/HSIZE/HBURST/HPROT/HSEL` stable
- Write data stability during an extended stall: hold `HWDATA` stable across consecutive wait cycles
- BUSY disallowed by default (strict): rejects `HTRANS==BUSY`
- AHB-Lite response legality: for 2-bit `HRESP`, disallow RETRY/SPLIT in LITE mode
- Known/X checks (optional): no X on key control fields during active transfers

## Notes

The driver performs immediate legality checks for alignment, transfer width,
wrap length/alignment, and 1KB boundaries. The SVA layer intentionally keeps
those checks runtime-portable; stronger burst/address progression assertions
remain a future extension.
