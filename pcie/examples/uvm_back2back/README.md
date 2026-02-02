# PCIe Back-to-Back Example

Simple UVM bring-up testbench demonstrating `kvips/pcie` build/run across simulators.

This example is currently a **scaffold**:
- It validates compile/elaborate/run on Questa/VCS/Xcelium.
- It does **not** yet model a real back-to-back PCIe link that carries end-to-end traffic.

## Directory Structure

```
uvm_back2back/
├── sim/
│   ├── filelist.f        # Source file list
│   ├── run_questa.sh     # Questa run script
│   ├── run_vcs.sh        # VCS run script
│   └── run_xcelium.sh    # Xcelium run script
└── tb/
    ├── tb_pkg.sv         # Test package with test classes
    └── top.sv            # Testbench top module
```

## Running the Example

### Questa
```bash
cd kvips/pcie/examples/uvm_back2back/sim
./run_questa.sh
```

### With specific test
```bash
./run_questa.sh +UVM_TESTNAME=pcie_b2b_smoke_test
./run_questa.sh +UVM_TESTNAME=pcie_b2b_mem_test
```

### If tools require LSF
```bash
source /tools/lsf/conf/profile.lsf
bsub -Ip -app gnrc -P boxsteru4 -Lp boxsteru4 -q interactive bash -lc 'cd kvips/pcie/examples/uvm_back2back/sim && ./run_questa.sh +UVM_TESTNAME=pcie_b2b_smoke_test'
```

## Available Tests

| Test Name | Description |
|-----------|-------------|
| `pcie_b2b_smoke_test` | Basic compile/elab/run sanity |
| `pcie_b2b_mem_test` | Constructs a `pcie_transaction` object (does not yet drive it) |

## Configuration

The testbench uses these default parameters:
- **NUM_LANES**: 16
- **MAX_GEN**: 5
- **DATA_WIDTH**: 32

Agent configuration (current example):
- RC agent: active
- EP agent: `PCIE_MONITOR` (monitor-only) to avoid multi-driving a single interface instance

## Output

Compilation logs: `out/questa/compile.log`
Simulation logs: `out/questa/run.log`
