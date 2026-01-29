//------------------------------------------------------------------------------
// AXI4 Transaction Logger (Debug Utility)
//------------------------------------------------------------------------------
// Simple subscriber that prints transactions from a monitor/env analysis port.
//
// Enable via:
// - Set `enable = 1` from your test, or
// - Plusarg `+KVIPS_AXI4_LOG_TXNS`
//------------------------------------------------------------------------------

`ifndef KVIPS_AXI4_TXN_LOGGER_SVH
`define KVIPS_AXI4_TXN_LOGGER_SVH

class axi4_txn_logger #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends uvm_subscriber #(axi4_item#(ADDR_W, DATA_W, ID_W, USER_W));

  bit enable = 1'b0;

  `uvm_component_param_utils(axi4_txn_logger#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if ($test$plusargs("KVIPS_AXI4_LOG_TXNS")) enable = 1'b1;
  endfunction

  virtual function void write(axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) t);
    if (!enable) return;
    `uvm_info(get_type_name(), {"AXI4 txn:\n", t.sprint()}, UVM_LOW)
  endfunction

endclass

`endif // KVIPS_AXI4_TXN_LOGGER_SVH

