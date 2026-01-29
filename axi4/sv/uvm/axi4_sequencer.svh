//------------------------------------------------------------------------------
// AXI4 Sequencer
//------------------------------------------------------------------------------

`ifndef KVIPS_AXI4_SEQUENCER_SVH
`define KVIPS_AXI4_SEQUENCER_SVH

class axi4_sequencer #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends uvm_sequencer #(axi4_item#(ADDR_W, DATA_W, ID_W, USER_W));

  `uvm_component_param_utils(axi4_sequencer#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

endclass

`endif // KVIPS_AXI4_SEQUENCER_SVH

