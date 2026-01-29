# Assertions

The VIP includes SVA protocol assertions for the AXI4 interface.

## Enabling
Assertions are compiled by default and can be runtime-disabled with:
- `+KVIPS_AXI4_ASSERT_OFF`

Additional per-category disables:
- Disable burst legality checks: `+KVIPS_AXI4_ASSERT_BURST_OFF`
- Disable exclusive restriction checks: `+KVIPS_AXI4_ASSERT_EXCL_OFF`

## Optional limits
You can enable simple outstanding-limit checks (portable “starter compliance”):
- Writes: `+KVIPS_AXI4_ASSERT_MAX_OUTS_W=<N>`
- Reads: `+KVIPS_AXI4_ASSERT_MAX_OUTS_R=<N>`

## Known-value checks
If enabled, the checker flags X/Z on key signals:
- Enable: `+KVIPS_AXI4_ASSERT_KNOWN`

## Scope
Assertions include (at minimum):
- VALID must remain stable until handshake (per channel)
- Payload must remain stable while VALID is high and READY is low
- Basic burst legality checks (e.g. size vs data width)
- Burst legality checks (LEN vs BURST type, WRAP length+alignment, 4KB boundary)
- Exclusive restrictions (LOCK implies INCR, <=16 beats, <=128B, aligned, no 4KB crossing)
- Stateful protocol checks (starter set):
  - W channel ordering vs AW (WLAST vs AWLEN)
  - R channel ordering vs AR (RLAST vs ARLEN, per-ID)
  - B only after write data completion (per BID)
  - EXOKAY only for exclusive read/write

## Binding
For widest simulator compatibility, the assertions are included directly inside
`axi4_if` via `kvips/axi4/sv/assertions/axi4_if_sva.svh`.
