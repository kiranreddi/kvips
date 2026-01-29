# User Guide (AXI4 VIP)

## What you get
- `axi4_agent`: Configure as master or slave
- `axi4_env`: Hold multiple agents and common infrastructure
- `axi4_sequences`: Basic, stress, concurrent, delay, exclusive, and error-injection sequences (see `axi4_sequences.svh`)
- `axi4_assertions`: SVA protocol checker (optional runtime enable)
- `axi4_scoreboard`: Passive data checker (write-derived expected vs read observed)
- `axi4_monitor` stats (optional): stall/throughput/outstanding/latency summary when enabled

## Integrating in your testbench
1. Instantiate `axi4_if` for each interface instance.
2. Put the interface into the UVM config DB for each agent instance.
3. Build `axi4_env` and configure agent roles.
4. Start sequences on the master sequencers.

See also: `kvips/axi4/docs/integration_guide.md`

## Multi-instance pattern
Use an env config object with arrays of agent configs, each with:
- `is_master` / `is_slave`
- `vif` (virtual interface handle)
- Per-agent knobs (timeouts, trace, outstanding limits)
- `monitor_enable`: disable duplicate monitoring when multiple agents share a `vif`

## Running examples
See `kvips/axi4/examples/uvm_back2back/README.md`.
