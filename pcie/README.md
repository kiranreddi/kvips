# KVIPS PCIe VIP (UVM + SVA)
# KVIPS PCIe VIP (UVM + SVA) — Work In Progress

This is an early-stage PCIe VIP scaffold intended to grow into a full-featured VIP over time.

UVM-based PCIe Gen4/Gen5/Gen6 VIP with:
- **Root Complex (RC)** and **Endpoint (EP)** agents (BFMs) + passive **monitor**
- **PIPE interface** mode (PHY-MAC boundary) and **Serial interface** mode (full PHY)
- Built-in **memory model** for endpoint responder demos
- **Scoreboard** (TLP-level transaction checking)
- **Protocol Assertions (SVA)** with runtime switches covering all layers
- Back-to-back (B2B) examples for verification without DUT
- Optional **transaction recording** (UVM TR) and **performance stats**
- **Coverage models** for protocol compliance
Today it provides:
- SystemVerilog **PIPE** and **Serial** interface definitions (`pcie_pipe_if`, `pcie_serial_if`)
- A buildable UVM skeleton: `pcie_cfg`, `pcie_transaction`, `pcie_sequencer`, `pcie_driver`, `pcie_monitor`, `pcie_scoreboard`, `pcie_agent`
- A runnable back-to-back (B2B) example that is validated to **compile/elaborate/run** on Questa/VCS/Xcelium
- Placeholder SVA modules for PHY/DLL/TL (not yet integrated/bound into the example TB)

It does **not** yet implement a complete PCIe stack (LTSSM/DLL/TL behavior, real TLP/DLLP exchange, credit model, replay, etc.). The default example tests are “bring-up” style and currently do not generate end-to-end PCIe traffic.

Designed for IEEE 1800 SystemVerilog + Accellera UVM (validated on UVM-1.1d and UVM-1.2).
Designed for IEEE 1800 SystemVerilog + Accellera UVM.

## Supported Generations
| Generation | Data Rate | Encoding | Supported |
|------------|-----------|----------|-----------|
| Gen1 | 2.5 GT/s | 8b/10b | ✅ |
| Gen2 | 5.0 GT/s | 8b/10b | ✅ |
| Gen3 | 8.0 GT/s | 128b/130b | ✅ |
| Gen4 | 16.0 GT/s | 128b/130b | ✅ |
| Gen5 | 32.0 GT/s | 128b/130b | ✅ |
| Gen6 | 64.0 GT/s | PAM4/FLIT | ✅ |
## Protocol coverage status
- PCIe generation/width enums exist up to Gen6/x32 in `pcie_types_pkg`, but functional “Gen1–Gen6 compliance” is **not implemented/validated** yet.

## Supported simulators (validated versions)
- Siemens Questa: `2025_3_2`
See `kvips/pcie/examples/uvm_back2back/README.md`.

Common single-test usage (from repo root):
- Questa: `kvips/pcie/examples/uvm_back2back/sim/run_questa.sh +UVM_TESTNAME=pcie_b2b_basic_test`
- VCS: `kvips/pcie/examples/uvm_back2back/sim/run_vcs.sh +UVM_TESTNAME=pcie_b2b_basic_test`
- Xcelium: `kvips/pcie/examples/uvm_back2back/sim/run_xcelium.sh +UVM_TESTNAME=pcie_b2b_basic_test`

Regression list:
- `kvips/pcie/examples/uvm_back2back/sim/tests.list`
- Questa: `kvips/pcie/examples/uvm_back2back/sim/run_questa.sh +UVM_TESTNAME=pcie_b2b_smoke_test`
- VCS: `kvips/pcie/examples/uvm_back2back/sim/run_vcs.sh +UVM_TESTNAME=pcie_b2b_smoke_test`
- Xcelium: `kvips/pcie/examples/uvm_back2back/sim/run_xcelium.sh +UVM_TESTNAME=pcie_b2b_smoke_test`

## Repository layout
- `kvips/pcie/sv/if/` : Interface definitions (PIPE, Serial)
- `kvips/pcie/sv/pkg/` : `pcie_types_pkg`, `pcie_uvm_pkg`
- `kvips/pcie/sv/uvm/` : Agent, drivers, monitor, scoreboard, sequences
- `kvips/pcie/sv/assertions/` : Protocol assertions (all layers)
- `kvips/pcie/sv/phy/` : PHY layer components (SerDes model, lane handling)
- `kvips/pcie/sv/dll/` : Data Link Layer components (DLLP, retry buffer)
- `kvips/pcie/sv/tl/` : Transaction Layer components (TLP handling)
- `kvips/pcie/examples/` : Runnable demos (Questa/VCS/Xcelium scripts)
- `kvips/pcie/docs/` : User guide, testplan, assertions, supported features

## Key capabilities
- **All TLP Types**: Memory (MRd/MWr), IO, Config (Type0/Type1), Message, Completion
- **Flow Control**: VC0-VC7, Posted/Non-Posted/Completion credit management
- **Power Management**: L0, L0s, L1, L1.1, L1.2, L2, ASPM
- **Link Training**: Full LTSSM with equalization (Gen3+)
- **Error Injection**: TLP/DLLP/PLP level error injection
- **Performance Modes**: Pipelined transactions, multiple outstanding
## Current limitations (important)
- The example does not bring up a real link (LTSSM is disabled by default via `pcie_cfg.enable_ltssm=0`).
- The example “memory test” currently only constructs a `pcie_transaction` object; it does not yet drive a TLP through a modeled link.
- Assertions exist as standalone SVA modules but are not bound/instantiated in the example TB yet.

## Debug knobs
Plusargs (demo-friendly):
- `kvips/pcie/docs/supported_features.md`
- `kvips/pcie/docs/testplan.md`
- `kvips/pcie/docs/assertions.md`
- `kvips/pcie/docs/avery_integration.md` (Avery VIP wrapper guide)

## LSF Access for /tools/ path
```bash
source /tools/lsf/conf/profile.lsf

# Use bsub for simulator access
bsub -Is -R "rusage[mem=8000]" <command>
bsub -Ip -app gnrc -P boxsteru4 -Lp boxsteru4 -q interactive <command>
```
