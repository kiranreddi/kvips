# User Guide (APB3/APB4 VIP)

## Choosing master/slave/passive

The VIP is built from:
- Master agent (sequencer + driver + monitor)
- Slave agent (responder + monitor)
- Passive monitor (monitor only)

See `kvips/apb/examples/uvm_back2back/tb/tb_pkg.sv` for a reference environment that instantiates:
- 1 active master agent
- 1 active slave agent (simple memory model)
- 1 monitor (enabled on master agent only to avoid duplication)

## Common knobs

### Protocol mode
- `+APB_PROTOCOL=APB4` (default)
- `+APB_PROTOCOL=APB3`

### Back-to-back style
- Drop `PSEL` between transfers (default): `cfg.drop_psel_between = 1`
- Continuous mode: `cfg.drop_psel_between = 0`

### Wait-states (slave)
- Enable/disable: `cfg.allow_wait_states`
- Range: `cfg.min_wait_cycles`, `cfg.max_wait_cycles`

### Error injection (slave)
- Enable: `cfg.slverr_enable`
- Probability (0..100): `cfg.slverr_pct`
- Address range: `cfg.slverr_start`, `cfg.slverr_end`

### APB4 extras
- Randomize `PPROT`: `cfg.randomize_pprot`
- Randomize `PSTRB`: `cfg.randomize_pstrb`

## Debug

### Logging
Enable the per-transaction trace prints (example TB wiring):
- `+VIP_TRACE`

### Waves (FSDB/VCD)
Enable waves via:
- `+KVIPS_WAVES`

For FSDB on Questa, use:
- `make -C kvips/apb/examples questa-waves ...`

### Assertions
See `kvips/apb/docs/assertions.md` for assertion switches.

