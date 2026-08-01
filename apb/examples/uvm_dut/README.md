# APB4 DUT verification example

This is the executable APB4 RTL-DUT integration flow.  The KVIPS APB master
drives a signal-level, byte-addressed synthesizable RAM slave in
`tb/dut/apb_ram_slave.sv`; the KVIPS monitor, APB assertions, and scoreboard
observe the same pins as an integration design.

Run one commercial-simulator test:

```bash
make -C apb/examples rtl-questa RTL_TEST=apb_dut_smoke_test USE_LSF=1 \
  LSF_BSUB='bsub -Ip -P boxsteru4 -q interactive'
make -C apb/examples rtl-vcs RTL_TEST=apb_dut_apb4_strobe_test USE_LSF=1 \
  LSF_BSUB='bsub -Ip -P boxsteru4 -q interactive'
make -C apb/examples rtl-xcelium RTL_TEST=apb_dut_pprot_test USE_LSF=1 \
  LSF_BSUB='bsub -Ip -P boxsteru4 -q interactive'
```

Run the complete APB4 DUT list through the evidence gate:

```bash
make -C apb/examples regress-rtl-questa USE_LSF=1 \
  LSF_BSUB='bsub -Ip -P boxsteru4 -q interactive'
make -C apb/examples regress-rtl-vcs USE_LSF=1 \
  LSF_BSUB='bsub -Ip -P boxsteru4 -q interactive'
make -C apb/examples regress-rtl-xcelium USE_LSF=1 \
  LSF_BSUB='bsub -Ip -P boxsteru4 -q interactive'
```

The regression only reports PASS when the simulator exits successfully, the
monitor observes nonzero writes and reads, the expected error behavior matches
the test, the scoreboard has zero mismatches, and no UVM error/fatal or
simulator error is present in the per-test log.

## DUT test coverage

`sim/tests_questa.list` covers deterministic read/writeback, continuous
back-to-back transfers, APB4 byte strobes, PPROT variation, fixed wait-state
behavior, the last mapped word, unmapped `PSLVERR`, and randomized APB4
traffic.  The wait-state sequence explicitly checks that the DUT held
`PREADY` low for the configured delay, and the error sequence checks both
unmapped writes and reads.

Verilator is retained as a CI-only path on this workstation.  GitHub Actions
runs the DUT list, but it is not used as evidence for the three
commercial-simulator DUT regressions:

```bash
make -C apb/examples regress-verilator-dut
```

The DUT is intentionally a single APB slave.  Interconnect decode, multiple
`PSEL` targets, and a separately sourced external APB master remain follow-up
integration work.
