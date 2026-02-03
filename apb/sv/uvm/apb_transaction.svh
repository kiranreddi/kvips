//------------------------------------------------------------------------------
// APB Transaction
//------------------------------------------------------------------------------
`ifndef KVIPS_APB_TRANSACTION_SVH
`define KVIPS_APB_TRANSACTION_SVH

class apb_item #(
  int ADDR_W = 32,
  int DATA_W = 32
) extends uvm_sequence_item;

  localparam int STRB_W = (DATA_W/8);

  rand bit               write;
  rand logic [ADDR_W-1:0] addr;
  rand logic [DATA_W-1:0] wdata;
       logic [DATA_W-1:0] rdata;
  rand logic [STRB_W-1:0] strb;
  rand logic [2:0]        prot;

  bit        slverr;
  apb_resp_e resp = APB_RESP_OK;

  int unsigned wait_cycles;
  time         start_t;
  time         end_t;

  function new(string name = "apb_item");
    super.new(name);
  endfunction

`ifdef VERILATOR
  /* verilator lint_off WIDTHEXPAND */
  /* verilator lint_off WIDTHTRUNC */
`endif
  `uvm_object_param_utils_begin(apb_item#(ADDR_W, DATA_W))
    `uvm_field_int(write, UVM_DEFAULT)
    `uvm_field_int(addr,  UVM_DEFAULT)
    `uvm_field_int(wdata, UVM_DEFAULT)
    `uvm_field_int(rdata, UVM_DEFAULT | UVM_NOCOMPARE)
    `uvm_field_int(strb,  UVM_DEFAULT)
    `uvm_field_int(prot,  UVM_DEFAULT)
    `uvm_field_int(slverr, UVM_DEFAULT)
    `uvm_field_enum(apb_resp_e, resp, UVM_DEFAULT)
    `uvm_field_int(wait_cycles, UVM_DEFAULT)
  `uvm_object_utils_end
`ifdef VERILATOR
  /* verilator lint_on WIDTHTRUNC */
  /* verilator lint_on WIDTHEXPAND */
`endif

endclass

`endif // KVIPS_APB_TRANSACTION_SVH

