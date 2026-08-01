# AHB RTL-DUT verification example

This example connects the KVIPS AHB master to a synthesizable, byte-lane-aware
RAM slave (`tb/dut/ahb_ram_slave.sv`). It is a signal-level DUT flow: the RAM
is the responder under test, while the VIP drives and monitors the bus.

The default DUT is AHB-Lite. Use `+AHB_MODE=AHB_FULL` to exercise the same
environment with the full AHB protocol mode.

## Tests

The six tests in `sim/tests_questa.list` cover basic transfers, incrementing
and wrapping bursts, fixed wait states, back-to-back stress, and full-mode
compilation:

```text
ahb_dut_smoke_test
ahb_dut_incr_burst_test
ahb_dut_wrap_burst_test
ahb_dut_wait_state_test
ahb_dut_stress_test
ahb_dut_full_mode_test
```

Every test requires completed write and read traffic, zero DUT errors and
scoreboard mismatches. The wait-state test also requires observed stall
cycles. The RAM is reset to known values, uses one responder wait state, and
implements byte/halfword/word write strobes.

## Run

Commercial simulator regressions are the evidence-bearing checks:

```bash
make -C ahb/examples regress-rtl-questa USE_LSF=1
make -C ahb/examples regress-rtl-vcs USE_LSF=1
make -C ahb/examples regress-rtl-xcelium USE_LSF=1
make -C ahb/examples rtl-questa TEST=ahb_dut_full_mode_test PLUSARGS='+AHB_MODE=AHB_FULL'
```

The Verilator flow is retained for CI/lint portability and is not a substitute
for the three commercial regressions:

```bash
make -C ahb/examples regress-verilator-dut
```

The raw-interface Verilator path samples HREADY and single-transfer HWDATA at
the active clock edge, before the DUT's nonblocking update; burst HRDATA is
sampled after that update. This preserves the AHB rule that a stalled
address/control phase remains on the bus, while the clocking-block commercial
paths use their normal sampled timing.

Results are written to
`ahb/examples/uvm_dut/sim/out/verilator/summary.md` (or the corresponding
commercial simulator output directory). Each summary is derived from the
scoreboard and transaction logger; a process exit alone is not considered a
pass.

See [the DUT verification guide](../../docs/dut_verification.md) for topology,
evidence rules, simulator commands, and remaining integration boundaries.
