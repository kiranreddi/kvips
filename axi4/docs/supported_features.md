# Supported features

## Parameters
The VIP is parameterized by:
- Address width
- Data width
- ID width
- User width (per-channel user fields are mapped to a single configurable width)

## Protocol
Target protocol: AXI4 (full). The initial implementation focuses on:
- Independent read/write address channels
- Bursts (INCR/FIXED/WRAP addressing supported in the example slave + scoreboard)
- ID field carried end-to-end
- Multiple outstanding (optional): enable master pipelining via `axi4_agent_cfg.master_pipelined` and set `max_outstanding_reads/writes`
- Exclusive accesses (optional): drive `axi4_item.lock=1` and enable `axi4_agent_cfg.slave_exclusive_enable`
- Error injection (optional): enable `axi4_agent_cfg.slave_err_enable` and configure `[slave_err_start, slave_err_end]` + response
- Master delay/backpressure knobs (optional): `master_aw_delay_*`, `master_ar_delay_*`, `master_w_beat_gap_*`, `master_rready_random`
  - Note: `master_rready_random` is exercised in pipelined mode tests.

## Multi-instance
The environment supports multiple agents:
- Multiple masters: one master agent per `axi4_if` instance (separate interfaces or via an interconnect DUT)
- Multiple slaves: one slave agent per `axi4_if` instance (separate interfaces or via an interconnect DUT)
- When multiple agents share the same `vif`, disable duplicate monitoring with `axi4_agent_cfg.monitor_enable=0` on all but one agent.

## Debug / observability
- Transaction-level logging knobs (`+UVM_VERBOSITY`, per-agent `trace_enable`)
- Optional UVM transaction recording from the monitor (`+VIP_TR` plus simulator/UVM recording enable)
- Optional performance statistics summary from the monitor (`axi4_agent_cfg.stats_enable`, demo shortcut `+VIP_STATS`)
- Optional wave dumping (`+KVIPS_WAVES`)
- Optional assertion enable/disable switches (see assertions doc)
