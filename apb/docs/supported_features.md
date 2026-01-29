# Supported Features (APB3/APB4)

## APB3
- Master driver: setup/access sequencing, optional drop/continuous style (`drop_psel_between`)
- Slave responder: simple word-addressed memory model
- Optional wait-state insertion (`min_wait_cycles`, `max_wait_cycles`)
- Optional error injection (`PSLVERR`) by address range + probability
- Monitor: transaction reconstruction on completion cycle and analysis port broadcast
- Scoreboard: expected memory model + read data check (optional)

## APB4 (APB3 + extras)
- `PPROT` generation/checking (optional randomization)
- `PSTRB` generation/checking (optional randomization)
- Byte-lane masked writes in slave memory model (`PSTRB` applied)
- APB4-only assertion gating when `+APB_PROTOCOL=APB4`

## Multi-select (`PSEL[NSEL-1:0]`)
- Interface supports vector `PSEL` with `NSEL` parameter.
- Master selects `sel_index` (defaults to 0).

## Runtime protocol mode switch
- Single interface includes APB4 signals always.
- Use `+APB_PROTOCOL=APB3|APB4` (default APB4).

## Limitations (current)
- Slave model is a simple memory (not a full register model). It is intended as a robust demo/reference and for integration smoke checks.
- No “negative/bad-driver” mode tests yet; assertion toggles exist for bring-up.

