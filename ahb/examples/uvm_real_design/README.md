# AHB real-design example

Separate real DUT verification flow that uses a synthesizable AHB RAM slave (`tb/dut/ahb_ram_slave.sv`) and KVIPS AHB master VIP.

Run Verilator regression:

```bash
make -C ahb/examples regress-verilator-real
```
