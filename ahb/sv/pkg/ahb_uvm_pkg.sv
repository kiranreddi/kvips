//------------------------------------------------------------------------------
// AHB UVM Package
//------------------------------------------------------------------------------
`ifndef KVIPS_AHB_UVM_PKG_SV
`define KVIPS_AHB_UVM_PKG_SV

package ahb_uvm_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import ahb_types_pkg::*;

  `include "ahb_cfg.svh"
  `include "ahb_transaction.svh"
  `include "ahb_sequencer.svh"
  `include "ahb_master_driver.svh"
  `include "ahb_slave_driver.svh"
  `include "ahb_monitor.svh"
  `include "ahb_txn_logger.svh"
  `include "ahb_scoreboard.svh"
  `include "ahb_agent.svh"
  `include "ahb_env.svh"
  `include "ahb_sequences.svh"

endpackage

`endif // KVIPS_AHB_UVM_PKG_SV

