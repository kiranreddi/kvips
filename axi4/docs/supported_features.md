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
- Multiple outstanding (optional): enable master pipelining via `axi4_agent_cfg.master_pipelined`; set `max_outstanding_reads/writes` and, when needed, `max_outstanding_total`
- Conservative cross-direction ordering (optional): set `order_overlapping_rw=0` to serialize pipelined reads and writes when an environment requires explicit ordering.
- Slave response scheduling (optional): B and whole-burst R reordering across IDs, with issue order preserved for a shared ID; R beat interleaving across IDs
- Exclusive accesses (optional): drive `axi4_item.lock=1` and enable `axi4_agent_cfg.slave_exclusive_enable`
- Error injection (optional): configure address-range injection, `slave_region_decode_enable` + regions, or per-direction response rates
- Master delay/backpressure knobs (optional): `master_aw_delay_*`, `master_ar_delay_*`, `master_w_beat_gap_*`, `master_rready_random`, and `master_bready_random`
  - Ready randomization is exercised in pipelined mode tests.
- Slave timing knobs (optional): legacy `ready_*`/`resp_*` defaults, plus per-channel `slave_aw_ready_*`, `slave_w_ready_*`, `slave_ar_ready_*`, `slave_b_resp_*`, `slave_r_resp_*`, and `slave_r_beat_delays[]`
- Reactive flow control (optional): `slave_aw_random_ready`, `slave_w_random_ready`, `slave_ar_random_ready`, `slave_b_accum_cycles`, `slave_r_accum_cycles`, `slave_max_outstanding_wr`, and `slave_max_outstanding_rd`
- Memory model (optional): base/size/wrap mapping, byte backdoor read/write on the slave driver, clear-on-reset, and zero/fill/random/X unwritten-read policy
- Phase-oriented construction (optional): `axi4_addr_phase_item`, `axi4_wdata_beat_item`, `axi4_rdata_beat_item`, `axi4_resp_phase_item`, and `axi4_ready_ctrl_item`
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

## Important checker boundary
`axi4_scoreboard` treats unwritten bytes as zero. This matches the default slave-memory policy only. If a test enables fill, random, or X unwritten reads, disable the supplied scoreboard for those reads or attach a checker that implements the selected policy.
