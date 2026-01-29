# UVM Back-to-Back Demo (AXI4 Master VIP <-> AXI4 Slave VIP)

This example instantiates one AXI4 interface and attaches:
- `axi4_agent` configured as **master**
- `axi4_agent` configured as **slave** (memory model enabled)
- `axi4_assertions` attached to the interface

The test performs a set of burst writes followed by reads to the same addresses and checks data integrity.

## Run
From the repo root:

- Questa: `kvips/axi4/examples/uvm_back2back/sim/run_questa.sh`
- Questa (FSDB): `kvips/axi4/examples/uvm_back2back/sim/run_questa_fsdb.sh`
- VCS: `kvips/axi4/examples/uvm_back2back/sim/run_vcs.sh`
- Xcelium: `kvips/axi4/examples/uvm_back2back/sim/run_xcelium.sh`

## Regressions via LSF (bsub)
From the repo root:
- Questa: `module load lsf && make -C kvips/axi4/examples regress-questa USE_LSF=1`
- VCS: `module load lsf && make -C kvips/axi4/examples regress-vcs USE_LSF=1`
- Xcelium: `module load lsf && make -C kvips/axi4/examples regress-xcelium USE_LSF=1`

## FSDB report (Verdi)
After generating an FSDB (see `run_questa_fsdb.sh`), you can dump key AXI signals with `fsdbreport`:
- Run on a node with Verdi available (e.g. via LSF `bsub`): `kvips/axi4/examples/uvm_back2back/sim/run_fsdbreport_lsf.sh <fsdb> --bt 0ns --et 2us`
- Submit with `bsub` (optional): `kvips/axi4/examples/uvm_back2back/sim/submit_fsdbreport_bsub.sh <fsdb> --bt 0ns --et 2us`

## Useful debug knobs
- UVM verbosity: `+UVM_VERBOSITY=UVM_MEDIUM`
- VIP tracing: `+VIP_TRACE` (enables per-agent trace in this demo)
- Transaction recording: `+VIP_TR` (typically also pass `+UVM_TR_RECORD`)
- Enable pipelined (multi-outstanding) master: `+VIP_PIPE` (or use test `axi4_b2b_pipelined_outstanding_test`)
- Scoreboard: enabled by default (disable with `+KVIPS_AXI4_SB_OFF`)
- Enable waves: `+KVIPS_WAVES` (VCD by default; FSDB where available)
- Stats (monitor): `+VIP_STATS` (prints a summary in `report_phase`)
- Assertions:
  - Disable: `+KVIPS_AXI4_ASSERT_OFF`
  - Known-value checks: `+KVIPS_AXI4_ASSERT_KNOWN`
  - Disable burst legality: `+KVIPS_AXI4_ASSERT_BURST_OFF`
  - Disable exclusive restrictions: `+KVIPS_AXI4_ASSERT_EXCL_OFF`

## Included tests
All tests live in `kvips/axi4/examples/uvm_back2back/tb/tb_pkg.sv` and are listed in `kvips/axi4/examples/uvm_back2back/sim/tests_questa.list`:
- `axi4_b2b_test` (smoke)
- `axi4_b2b_pipelined_outstanding_test` (multi-outstanding + reorder/interleave)
- `axi4_b2b_pipelined_rready_backpressure_test` (master RREADY backpressure, pipelined)
- `axi4_b2b_exclusive_basic_test`, `axi4_b2b_exclusive_fail_test` (LOCK/EXOKAY)
- `axi4_b2b_exclusive_illegal_test` (configurable exclusive restrictions)
- `axi4_b2b_error_write_test`, `axi4_b2b_error_read_test` (DECERR injection)
- `axi4_b2b_incr_256beat_test` (INCR bursts up to 256 beats)
- `axi4_b2b_delay_stress_test` (master delays + slave backpressure)
- `axi4_b2b_concurrent_rw_test` (concurrent reads+writes + stats)
