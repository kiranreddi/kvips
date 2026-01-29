//------------------------------------------------------------------------------
// APB Transaction Logger (Debug Utility)
//------------------------------------------------------------------------------
`ifndef KVIPS_APB_TXN_LOGGER_SVH
`define KVIPS_APB_TXN_LOGGER_SVH

class apb_txn_logger #(
  int ADDR_W = 32,
  int DATA_W = 32
) extends uvm_subscriber #(apb_item#(ADDR_W, DATA_W));

  localparam string RID = "APB_LOG";

  bit enable = 1'b0;

  `uvm_component_param_utils(apb_txn_logger#(ADDR_W, DATA_W))

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if ($test$plusargs("KVIPS_APB_LOG_TXNS")) enable = 1'b1;
  endfunction

  virtual function void write(apb_item#(ADDR_W, DATA_W) t);
    if (!enable) return;
    if (t == null) return;
    `uvm_info(RID, {"APB txn:\n", t.sprint()}, UVM_LOW)
  endfunction

endclass

`endif // KVIPS_APB_TXN_LOGGER_SVH

