# Supported features (AHB VIP)

## Supported today (v0.1)

Protocol / electrical
- Single-bus, single master usage (AHB-Lite style)
- AHB-Lite vs AHB-Full **mode selection** via `+AHB_MODE=AHB_LITE|AHB_FULL` (single-image build)
- Basic responses: **OKAY** and **ERROR** in Lite; directed **RETRY**/**SPLIT** encodings in Full
- AHB5 `HNONSEC` sideband is transported through the interface, driver, monitor, and transaction item
- Address/control pipelining with stall handling (`HREADY` low holds stable)

VIP roles
- Master agent: drives AHB transfers (including bursts) with correct address/control vs data phasing
- Slave agent: responds with `HREADYOUT/HRESP/HRDATA` and captures writes
- Passive monitor: reconstructs completed transfers and publishes transactions
- Scoreboard: monitor-based expected memory model for data integrity, including beat-by-beat burst reads
- Transaction logger: per-transfer logging + end-of-test summary counters

Traffic
- SINGLE transfers
- INCR4/8/16 bursts
- WRAP4/8/16 bursts (wrap addressing)
- Variable `HSIZE` (byte/half/word/dword bins in coverage)
- Wait-state insertion by the slave (configurable min/max)
- Error injection by address range or probability (slave)
- BUSY insertion between burst beats (configurable percentage)
- Master-side legality checks for transfer alignment, bus width, fixed burst length, wrap alignment, and 1KB boundaries

Checks / debug
- Interface-bound SVA:
  - Hold-stability while stalled
  - Known/X checks on control
  - AHB-Lite response legality (no RETRY/SPLIT)
  - Full-mode response encoding and two-cycle directed RETRY/SPLIT behavior
- Coverage (monitor-based):
  - read/write, size, burst, stall bins, response bins, crosses

## Not yet implemented (planned / pending)

AHB Full multi-master semantics
- Arbitration, `HMASTER` behavior, multi-master scheduling
- Interconnect-level `HSPLITx` routing and SPLIT ownership

Protocol details / corner cases
- Full wrap legality assertions beyond the driver-side legality guard
- Endianness configurability beyond little-endian default (memory model assumes little-endian lane mapping)
- Multiple slave regions with interconnect-like decode (`HSEL`/address map) beyond single-slave default
- Security permission checking associated with `HNONSEC` (the VIP transports the sideband but does not enforce a firewall policy)

Advanced debug
- Full transaction recording streams (UVM TR) integrated across all components (hooks exist in cfg; not yet wired everywhere)
