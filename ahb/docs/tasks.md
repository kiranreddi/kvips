# AHB VIP task list (tracked in-repo)

This file is a permanent, in-repo task checklist for the AHB VIP. Do not delete it; update status as work completes.

## Build-out tasks

- [x] Directory skeleton created under `kvips/ahb/`
- [x] `ahb_if.sv` with clocking blocks + modports
- [x] `ahb_if_sva.svh` assertions with runtime switches
- [x] `ahb_types_pkg.sv` enums/types
- [x] `ahb_cfg.svh` (protocol mode, timing, decode, wait-states, error injection)
- [x] `ahb_transaction.svh` transaction model (burst-capable)
- [x] `ahb_master_driver.svh` pipelined master driver (AHB address/data phase)
- [x] `ahb_slave_driver.svh` slave responder + memory model + wait-states
- [x] `ahb_monitor.svh` robust pipeline monitor + coverage hooks
- [x] `ahb_scoreboard.svh` memory/reference scoreboard (data integrity)
- [x] `ahb_txn_logger.svh` summary logger / easy debug
- [x] `ahb_agent.svh` (ACTIVE/PASSIVE, role master/slave)
- [x] `ahb_env.svh` (multi-agent environment, analysis connections)
- [x] `ahb_sequences.svh` comprehensive sequence library
- [x] `ahb_uvm_pkg.sv` package assembly

## Examples + tests

- [ ] `examples/uvm_back2back` testbench compiles
- [x] Test list includes: smoke, single rw, wait-state, incr burst, wrap burst, back-to-back, error response, random stress
- [x] Simulator scripts: Questa/VCS/Xcelium
- [x] Example README describes how to run + debug

## Documentation

- [x] `docs/supported_features.md` (what is supported vs not yet)
- [x] `docs/integration_guide.md` (how to integrate into a DUT TB)
- [x] `docs/user_guide.md` (cfg knobs, logging, debug switches)
- [x] `docs/assertions.md` (assertion list + disable switches)
- [x] `docs/testplan.md` mapping tests to AHB features
- [x] `docs/directory_structure.md`
- [ ] Top-level `kvips/README.md` updated (AHB entry)
- [x] Top-level `kvips/README.md` updated (AHB entry)
- [x] `kvips/docs/getting-started.md` updated (AHB quickstart)
- [x] `kvips/AGENTS.md` updated with AHB context

## Quality gates (best-effort in this environment)

- [ ] Verilator lint clean (where applicable) / no obvious SV syntax issues
- [ ] Example compiles on at least one available simulator flow
- [ ] All tests pass in the example environment
