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
- Address sideband attributes supported on the bus:
  - `axi4_item.cache`, `axi4_item.prot`, `axi4_item.qos`, `axi4_item.region`
- Multiple outstanding (optional): enable master pipelining via `axi4_agent_cfg.master_pipelined` and set `max_outstanding_reads/writes`
- Exclusive accesses (optional): drive `axi4_item.lock=1` and enable `axi4_agent_cfg.slave_exclusive_enable`
- Error injection (optional): enable `axi4_agent_cfg.slave_err_enable` and configure `[slave_err_start, slave_err_end]` + response
- Master delay/backpressure knobs (optional): `master_aw_delay_*`, `master_ar_delay_*`, `master_w_beat_gap_*`, `master_rready_random`
  - Note: `master_rready_random` is exercised in pipelined mode tests.
- Per-transaction timing overrides (optional):
  - `axi4_item.aw_delay_cycles`, `axi4_item.ar_delay_cycles`, `axi4_item.w_beat_gap_cycles` (`-1` means “use cfg”)

## Multi-instance
The environment supports multiple agents:
- Multiple masters: one master agent per `axi4_if` instance (separate interfaces or via an interconnect DUT)
- Multiple slaves: one slave agent per `axi4_if` instance (separate interfaces or via an interconnect DUT)
- When multiple agents share the same `vif`, disable duplicate monitoring with `axi4_agent_cfg.monitor_enable=0` on all but one agent.

## Debug / observability
- Transaction-level logging knobs (`+UVM_VERBOSITY`, per-agent `trace_enable`)
- Optional UVM transaction recording from the monitor (`+VIP_TR` plus simulator/UVM recording enable)
- Optional performance statistics summary from the monitor (`axi4_agent_cfg.stats_enable`, demo shortcut `+VIP_STATS`)
- Optional windowed statistics reporting (`axi4_agent_cfg.stats_window_cycles`)
- Optional functional coverage sampling (`axi4_agent_cfg.coverage_enable`)
- Optional wave dumping (`+KVIPS_WAVES`)
- Optional assertion enable/disable switches (see assertions doc)
