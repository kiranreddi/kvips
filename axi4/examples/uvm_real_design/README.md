# AXI4 DUT-design example

This example keeps the existing `uvm_back2back` suite untouched and adds a separate real DUT flow with a synthesizable AXI4 RAM slave (`tb/dut/axi4_ram_slave.sv`).

Run Verilator DUT regression:

```bash
make -C axi4/examples regress-verilator-dut
```

Legacy compatibility alias:

```bash
make -C axi4/examples regress-verilator-real
```

## Results page (pretty summary)

After regression, open:

`/home/runner/work/kvips/kvips/axi4/examples/uvm_real_design/sim/out/verilator/summary.md`

It contains a Markdown table with PASS/FAIL plus `wr_txns`, `rd_txns`, and error/mismatch counters for each test.
Under Verilator UVM/no-DPI flow, an additional end-of-run `[AXI4_SCB]` summary line is emitted after the timed DUT window so scoreboard counters are visible in logs even if UVM `report_phase` prints early.
