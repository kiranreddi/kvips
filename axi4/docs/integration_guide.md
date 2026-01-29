# AXI4 VIP Integration Guide (minimal)

This guide shows how to integrate the AXI4 VIP as a **master** and/or **slave** in a UVM testbench.

## 1) Instantiate the interface

In your top module:

- Instantiate `axi4_if` (one per AXI4 bus instance you want to drive/monitor).
- Put the virtual interface into the UVM config DB.

See the working demo in `kvips/axi4/examples/uvm_back2back/tb/top.sv`.

## 2) Build an environment with agents

Typical flow (same as the demo):

- Create `axi4_env_cfg`
- Add one `axi4_agent_cfg` configured as **master**
- Add one `axi4_agent_cfg` configured as **slave** (memory enabled) or connect the interface to your DUT slave
- Set `cfg` into `uvm_config_db` at `env`
- Create `axi4_env`

Working reference: `kvips/axi4/examples/uvm_back2back/tb/tb_pkg.sv`

## 3) Connect analysis (scoreboard / logging)

The demo connects the environment analysis port:
- `axi4_txn_logger` (optional debug)
- `axi4_scoreboard` (self-checking: write-derived expected vs read observed)

See `kvips/axi4/examples/uvm_back2back/tb/tb_pkg.sv`.

## 4) Start sequences

- Use `env.get_master_sequencer(<idx>)`
- Start sequences from `axi4_sequences.svh`

Example tests live in `kvips/axi4/examples/uvm_back2back/tb/tb_pkg.sv`.

## Multi-instance / multi-master note

- One `axi4_agent` (master) drives a single `axi4_if`.
- For **multiple masters**, instantiate **multiple `axi4_if`** (or connect to an interconnect DUT) and create one master agent per interface instance.
- The `axi4_env_cfg.agent_cfgs[]` array is intended to hold multiple **independent** AXI interfaces (each with its own `vif`), not multiple drivers on the same shared bus.
- If you configure both a master and a slave agent on the same `vif` (as in the demo), disable duplicate monitoring with `axi4_agent_cfg.monitor_enable=0` on one of them.

## Debug and recording knobs

- VIP trace: `+VIP_TRACE`
- Transaction recording (monitor): `+VIP_TR` plus simulator/UVM enable (commonly `+UVM_TR_RECORD`)
- Stats: set `axi4_agent_cfg.stats_enable=1` (demo shortcut: `+VIP_STATS`)
- Exclusive accesses (slave model): set `axi4_item.lock=1` in sequences/items; slave enables by default via `axi4_agent_cfg.slave_exclusive_enable`
- Error injection (slave model): enable `axi4_agent_cfg.slave_err_enable` and configure `slave_err_start/slave_err_end/slave_err_resp` (+ direction flags)
- Assertions:
  - Disable: `+KVIPS_AXI4_ASSERT_OFF`
  - Known-value checks: `+KVIPS_AXI4_ASSERT_KNOWN`
  - Disable burst legality: `+KVIPS_AXI4_ASSERT_BURST_OFF`
  - Disable exclusive restrictions: `+KVIPS_AXI4_ASSERT_EXCL_OFF`
- Scoreboard:
  - Disable: `+KVIPS_AXI4_SB_OFF`
  - Warn on unwritten read bytes: `+KVIPS_AXI4_SB_WARN_UNINIT`

## Running on Questa via LSF/ignrc

From repo root:

- Regression: `kvips/axi4/examples/uvm_back2back/sim/regress_questa_ignrc.sh`
- Single test: `module load questa/2025_3_2 && module load lsf && ignrc kvips/axi4/examples/uvm_back2back/sim/run_questa.sh +UVM_TESTNAME=axi4_b2b_test`
