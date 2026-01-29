//------------------------------------------------------------------------------
// AXI4 Base Test
//------------------------------------------------------------------------------

`ifndef KVIPS_AXI4_BASE_TEST_SVH
`define KVIPS_AXI4_BASE_TEST_SVH

class axi4_base_test extends uvm_test;
  `uvm_component_utils(axi4_base_test)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
endclass

`endif // KVIPS_AXI4_BASE_TEST_SVH

