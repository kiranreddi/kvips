# AXI4 RTL-DUT verification milestone

This milestone adds an executable AXI4 integration target under
`axi4/examples/uvm_dut/`.  The name refers to the RTL device under
test (DUT), not to a second VIP implementation.

## Topology

```text
KVIPS AXI4 master agent
        |
   axi4_if + SVA + passive monitor
        |
axi4_ram_slave (synthesizable byte-addressed RTL DUT)
        |
KVIPS scoreboard / protocol checker / transaction logger
```

The adapter uses explicit signal connections.  It does not use clocking-block
`force` statements, DPI, or simulator-specific encrypted code.  This is the
portable baseline for Questa, VCS, and Xcelium.  Verilator remains a CI-only
path because it is not required on the development workstation.

## Coverage now exercised

| Area | DUT tests |
|---|---|
| Single-beat and burst read/write | `axi4_dut_smoke_test`, `axi4_dut_burst_mix_test` |
| INCR/FIXED/WRAP addressing | `axi4_dut_wrap_test` |
| Narrow transfers and WSTRB | `axi4_dut_narrow_test`, `axi4_dut_strobe_test` |
| Unaligned byte lanes | `axi4_dut_unaligned_test` |
| 4KB edge and maximum INCR length | `axi4_dut_boundary_test` |
| Same-ID pipelined issue and response framing | `axi4_dut_pipeline_test` |
| Unmapped address response | `axi4_dut_error_test` |
| Master delays and RREADY/BREADY backpressure | `axi4_dut_delay_test` |
| Front-door UVM RAL writes/reads and prediction | `axi4_dut_ral_test` |

The DUT and scoreboard both use AMBA byte-lane addressing.  WRAP addresses
are calculated from the original burst start address and wrap container;
unmapped byte accesses return DECERR and do not create false scoreboard
updates.

## Required evidence

For a release candidate, run the complete list using each supported commercial
simulator through LSF:

```bash
make -C axi4/examples regress-rtl-questa USE_LSF=1
make -C axi4/examples regress-rtl-vcs USE_LSF=1
make -C axi4/examples regress-rtl-xcelium USE_LSF=1
```

A passing run requires zero simulator errors, zero UVM ERROR/FATAL reports,
zero protocol-checker failures, and zero scoreboard mismatch beats.  The logs
under `axi4/examples/uvm_dut/sim/out/<sim>/` are the evidence record.

## Remaining work

This target is deliberately a small single-device slave.  It does not prove
multi-master arbitration, interconnect decode, independent external-master
interoperability, or formal/toggle coverage closure.  The next integration
step is an independently sourced open RTL master driving the KVIPS slave
responder, followed by a width/ID parameter matrix.
