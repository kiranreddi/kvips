# AXI4 real-design example

This example keeps the existing `uvm_back2back` suite untouched and adds a separate real DUT flow with a synthesizable AXI4 RAM slave (`tb/dut/axi4_ram_slave.sv`).

Run Verilator regression:

```bash
make -C axi4/examples regress-verilator-real
```
