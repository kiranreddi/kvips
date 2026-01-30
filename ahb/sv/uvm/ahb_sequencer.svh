//------------------------------------------------------------------------------
// AHB Sequencer
//------------------------------------------------------------------------------
`ifndef KVIPS_AHB_SEQUENCER_SVH
`define KVIPS_AHB_SEQUENCER_SVH

class ahb_sequencer #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2
) extends uvm_sequencer #(ahb_item#(ADDR_W, DATA_W, HRESP_W));

  `uvm_component_param_utils(ahb_sequencer#(ADDR_W, DATA_W, HRESP_W))

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
endclass

`endif // KVIPS_AHB_SEQUENCER_SVH

