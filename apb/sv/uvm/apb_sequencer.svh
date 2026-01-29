//------------------------------------------------------------------------------
// APB Sequencer
//------------------------------------------------------------------------------
`ifndef KVIPS_APB_SEQUENCER_SVH
`define KVIPS_APB_SEQUENCER_SVH

class apb_sequencer #(
  int ADDR_W = 32,
  int DATA_W = 32
) extends uvm_sequencer #(apb_item#(ADDR_W, DATA_W));

  `uvm_component_param_utils(apb_sequencer#(ADDR_W, DATA_W))

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

endclass

`endif // KVIPS_APB_SEQUENCER_SVH

