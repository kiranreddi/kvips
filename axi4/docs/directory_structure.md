# Directory structure

`kvips/axi4/` is organized as:

- `sv/if/`: Synthesizable interface(s) (AXI4 bus interface)
- `sv/pkg/`: Package(s) with types and shared utilities
- `sv/uvm/`: UVM classes (agents, env, sequences, tests)
- `sv/assertions/`: SVA protocol assertions/checkers + bind helpers
- `rtl/`: Optional synthesizable example DUTs (reference RAM, etc.)
- `examples/`: Runnable examples (UVM, and later cocotb)

Each file contains a short header describing its intent and how it is used.

## Key files
- `kvips/axi4/sv/if/axi4_if.sv`: AXI4 interface (signals + modports + clocking blocks)
- `kvips/axi4/sv/pkg/axi4_types_pkg.sv`: Enums/helpers shared by VIP + assertions
- `kvips/axi4/sv/pkg/axi4_uvm_pkg.sv`: UVM package that includes all AXI4 UVM classes
- `kvips/axi4/sv/uvm/axi4_agent.svh`: Master/slave agent wrapper (instantiates role-appropriate driver)
- `kvips/axi4/sv/uvm/axi4_master_driver.svh`: Master BFM (drives AW/W/AR and consumes B/R)
- `kvips/axi4/sv/uvm/axi4_slave_driver.svh`: Reactive slave (ready/response + optional memory model)
- `kvips/axi4/sv/uvm/axi4_monitor.svh`: Passive monitor producing completed read/write `axi4_item` transactions
- `kvips/axi4/sv/assertions/axi4_if_sva.svh`: Protocol assertions (SVA) included inside `axi4_if`
