# AXI4 DUT verification example

This example keeps the `uvm_back2back` suite untouched and adds an RTL-DUT
flow with a synthesizable AXI4 RAM slave (`tb/dut/axi4_ram_slave.sv`).  KVIPS
is the active AXI4 master; the DUT is connected at signal level, so the
monitor, protocol checker, assertions, coverage hooks, and scoreboard observe
the same traffic that an integration design would see.

Run a commercial-simulator DUT test:

```bash
make -C axi4/examples rtl-questa TEST=axi4_dut_smoke_test SEED=1 USE_LSF=1
make -C axi4/examples rtl-vcs TEST=axi4_dut_burst_mix_test SEED=1 USE_LSF=1
make -C axi4/examples rtl-xcelium TEST=axi4_dut_narrow_test SEED=1 USE_LSF=1
```

Run the complete DUT list on one simulator:

```bash
make -C axi4/examples regress-rtl-questa USE_LSF=1
```

Verilator remains a CI-only path on this workstation:

```bash
make -C axi4/examples regress-verilator-dut
```

## DUT tests

The list in `sim/tests_questa.list` covers basic read/write, INCR/FIXED/WRAP,
narrow and partial strobes, unaligned byte lanes, 4KB/length boundaries,
same-ID pipelining, unmapped DECERR, and master-side timing/backpressure.
The RAL test also drives a small four-register front-door map through the
KVIPS AXI4 sequencer and predictor.
All tests are self-checking and must finish without UVM errors/fatals or
scoreboard mismatches.

The DUT is intentionally small and single-outstanding on each channel.  It is
an executable integration target, not a claim that every interconnect feature
is implemented.  Multi-master arbitration, external-master interoperability,
and a second independent open-source RTL target are follow-up milestones.
