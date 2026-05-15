# APB DUT-design example

Separate real DUT verification flow that uses a synthesizable APB RAM slave (`tb/dut/apb_ram_slave.sv`) and KVIPS APB master VIP.

Run Verilator DUT regression:

```bash
make -C apb/examples regress-verilator-dut
```

Legacy compatibility alias:

```bash
make -C apb/examples regress-verilator-real
```

## Results page (pretty summary)

After regression, open:

`/home/runner/work/kvips/kvips/apb/examples/uvm_real_design/sim/out/verilator/summary.md`

It contains a Markdown table with PASS/FAIL plus APB scoreboard counters (`wr`, `rd`, `err`, `mismatch`) per test.
Under Verilator UVM/no-DPI flow, an additional end-of-run `[APB_SCB]` summary line is emitted after the timed DUT window so scoreboard counters are visible in logs even if UVM `report_phase` prints early.
