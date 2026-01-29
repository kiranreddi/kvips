//------------------------------------------------------------------------------
// AXI4 UVM Package
//------------------------------------------------------------------------------
// Accellera UVM components for AXI4 (full) VIP.
//
// Compile order:
// - kvips/common/sv on +incdir
// - kvips/axi4/sv/uvm on +incdir
//------------------------------------------------------------------------------

`ifndef KVIPS_AXI4_UVM_PKG_SV
`define KVIPS_AXI4_UVM_PKG_SV

package axi4_uvm_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import axi4_types_pkg::*;

  `include "kvips_macros.svh"

  `include "axi4_transaction.svh"
  `include "axi4_cfg.svh"
  `include "axi4_sequencer.svh"
  `include "axi4_master_driver.svh"
  `include "axi4_slave_driver.svh"
  `include "axi4_monitor.svh"
  `include "axi4_txn_logger.svh"
  `include "axi4_scoreboard.svh"
  `include "axi4_agent.svh"
  `include "axi4_env.svh"
  `include "axi4_sequences.svh"
  `include "axi4_base_test.svh"

endpackage

`endif // KVIPS_AXI4_UVM_PKG_SV
