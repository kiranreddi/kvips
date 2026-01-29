# APB VIP Integration Guide

## 1. Instantiate the interface

`apb_if` always contains APB4 signals (`PPROT`, `PSTRB`) so that a single compiled image can run in APB3 or APB4 mode.

Example:

```systemverilog
localparam int ADDR_W = 16;
localparam int DATA_W = 32;
localparam int NSEL   = 1;

logic PCLK, PRESETn;
apb_if #(ADDR_W, DATA_W, NSEL) apb (.*);
```

## 2. Connect virtual interface

```systemverilog
uvm_config_db#(virtual apb_if #(ADDR_W, DATA_W, NSEL))::set(null, "*", "vif", apb);
```

## 3. Create master/slave agents

Use `apb_env_cfg` + `apb_agent_cfg`:
- One agent configured as `master` (active)
- One agent configured as `slave` (active) with a simple memory model

See the example implementation in `kvips/apb/examples/uvm_back2back/tb/tb_pkg.sv`.

## 4. Select APB3 vs APB4 (runtime)

- APB4 (default): `+APB_PROTOCOL=APB4`
- APB3: `+APB_PROTOCOL=APB3`

Notes:
- APB3 mode forces `PPROT=0` and `PSTRB='1` in the master driver.
- APB4-only assertions are disabled when `+APB_PROTOCOL=APB3`.

## 5. Scoreboard and validation

The example connects:
- `apb_monitor` → analysis port
- `apb_scoreboard` → checks read data against expected memory updates

Disable scoreboard via:
- `+KVIPS_APB_SB_OFF` or `uvm_config_db#(bit)::set(this, "sb", "enable", 1'b0)`

## 6. Transaction recording (optional)

Enable transaction recording via:
- `+VIP_TR` (example TB maps this to `cfg.tr_record_enable`)

## 7. Debug switches

Common plusargs in the example TB:
- `+VIP_TRACE` – enable concise per-transaction prints
- `+VIP_COV` – enable monitor functional coverage sampling
- `+VIP_TR` – enable transaction recording

Assertions:
- `+KVIPS_APB_ASSERT_OFF` – disable all APB assertions
- `+KVIPS_APB_ASSERT_KNOWN_OFF` – disable X/known-value checks
- `+KVIPS_APB_ASSERT_STRICT_OFF` – disable strict rules (e.g. strobe nonzero)

