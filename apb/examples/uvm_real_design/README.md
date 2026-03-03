# APB real-design example

Separate real DUT verification flow that uses a synthesizable APB RAM slave (`tb/dut/apb_ram_slave.sv`) and KVIPS APB master VIP.

Run Verilator regression:

```bash
make -C apb/examples regress-verilator-real
```
