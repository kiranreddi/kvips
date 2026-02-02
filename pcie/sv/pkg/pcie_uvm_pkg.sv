//------------------------------------------------------------------------------
// PCIe UVM Package
//------------------------------------------------------------------------------
// Accellera UVM components for PCIe VIP.
//
// Compile order:
// - kvips/common/sv on +incdir
// - kvips/pcie/sv/uvm on +incdir
//------------------------------------------------------------------------------

`ifndef KVIPS_PCIE_UVM_PKG_SV
`define KVIPS_PCIE_UVM_PKG_SV

`timescale 1ns/1ps

package pcie_uvm_pkg;
  timeunit 1ns;
  timeprecision 1ps;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import pcie_types_pkg::*;

  `include "kvips_macros.svh"

  `include "pcie_cfg.svh"
  `include "pcie_transaction.svh"
  `include "pcie_sequencer.svh"
  `include "pcie_driver.svh"
  `include "pcie_monitor.svh"
  `include "pcie_scoreboard.svh"
  `include "pcie_agent.svh"

endpackage

`endif // KVIPS_PCIE_UVM_PKG_SV
