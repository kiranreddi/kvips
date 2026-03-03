# AHB DUT-design example

Separate real DUT verification flow that uses a synthesizable AHB RAM slave (`tb/dut/ahb_ram_slave.sv`) and KVIPS AHB master VIP.

Run Verilator DUT regression:

```bash
make -C ahb/examples regress-verilator-dut
```

Legacy compatibility alias:

```bash
make -C ahb/examples regress-verilator-real
```

## Results page (pretty summary)

After regression, open:

`/home/runner/work/kvips/kvips/ahb/examples/uvm_real_design/sim/out/verilator/summary.md`

It contains a Markdown table with PASS/FAIL plus AHB counters (`wr`, `rd`, `err`, `mismatch`, `stall_cycles`) per test.
Under Verilator UVM/no-DPI flow, an additional end-of-run `[AHB_SCB]` summary line is emitted after the timed DUT window so scoreboard counters are visible in logs even if UVM `report_phase` prints early.
