# AHB RTL-DUT verification

The `examples/uvm_dut` environment proves the AHB VIP against an actual
signal-level responder rather than another VIP. The KVIPS master drives
`ahb_if`; `tb/dut/ahb_ram_slave.sv` implements a synthesizable byte-addressed
RAM with one configured wait state; the passive monitor feeds the transaction
logger and beat-accurate scoreboard.

## Test matrix

| Test | Focus | Required evidence |
|---|---|---|
| `ahb_dut_smoke_test` | single transfers and readback | completed writes/reads, no errors or mismatches |
| `ahb_dut_incr_burst_test` | INCR4/8/16 bursts | completed writes/reads, no errors or mismatches |
| `ahb_dut_wrap_burst_test` | WRAP4/8/16 bursts | completed writes/reads, no errors or mismatches |
| `ahb_dut_wait_state_test` | responder wait states | completed traffic plus nonzero `stall_cycles` |
| `ahb_dut_stress_test` | back-to-back mixed traffic | completed traffic, no errors or mismatches |
| `ahb_dut_full_mode_test` | AHB Full mode build/run | completed traffic, no errors or mismatches |

The default mode is `+AHB_MODE=AHB_LITE`; run the last test with
`+AHB_MODE=AHB_FULL`. Every commercial regression parses the scoreboard and
logger summaries. A simulator exit code by itself is not accepted as proof.

## Commands

From the repository root:

```bash
make -C ahb/examples regress-rtl-questa USE_LSF=1
make -C ahb/examples regress-rtl-vcs USE_LSF=1
make -C ahb/examples regress-rtl-xcelium USE_LSF=1
make -C ahb/examples rtl-questa RTL_TEST=ahb_dut_full_mode_test PLUSARGS='+AHB_MODE=AHB_FULL'
```

Verilator runs the same list in CI with its no-DPI UVM compatibility flow:

```bash
make -C ahb/examples regress-verilator-dut
```

Commercial logs and regression summaries are stored under
`ahb/examples/uvm_dut/sim/out/{questa,vcs,xcelium}/`; the CI artifact is under
`ahb/examples/uvm_dut/sim/out/verilator/summary.md`.

The CI-only raw-interface path preserves cycle semantics explicitly: the
driver samples the pre-update HREADY value before advancing a held control
phase, the monitor captures single-transfer HWDATA before the driver update,
and burst read data is sampled after the DUT response update. Commercial
simulators retain the standard clocking-block path.

## Scope and remaining boundaries

This milestone intentionally validates one AHB master, one selected RAM
responder, reset recovery, byte/halfword/word writes, burst handshakes, and
fixed wait states. It does not claim multi-master arbitration, HMASTER/HSPLIT
routing, interconnect decode, unmapped-address/error behavior, formal or code
coverage closure, or an external production master. Those require a separate
interconnect/DUT harness and are tracked in
[`amba_spec_coverage.md`](amba_spec_coverage.md).
