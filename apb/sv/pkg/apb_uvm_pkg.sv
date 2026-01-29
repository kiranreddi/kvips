//------------------------------------------------------------------------------
// APB UVM Package
//------------------------------------------------------------------------------
`ifndef KVIPS_APB_UVM_PKG_SV
`define KVIPS_APB_UVM_PKG_SV

package apb_uvm_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import apb_types_pkg::*;

  `include "apb_cfg.svh"
  `include "apb_transaction.svh"
  `include "apb_sequencer.svh"
  `include "apb_master_driver.svh"
  `include "apb_slave_driver.svh"
  `include "apb_monitor.svh"
  `include "apb_txn_logger.svh"
  `include "apb_scoreboard.svh"
  `include "apb_agent.svh"
  `include "apb_env.svh"
  `include "apb_sequences.svh"

endpackage

`endif // KVIPS_APB_UVM_PKG_SV

