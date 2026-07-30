//------------------------------------------------------------------------------
// AXI4-Lite interface
//------------------------------------------------------------------------------
// AXI4-Lite deliberately has no transaction IDs, bursts, locks, or USER
// sidebands.  Keep it separate from axi4_if so a Lite integration cannot
// accidentally claim Full-channel semantics by constraining an AXI4 interface.
//------------------------------------------------------------------------------
`ifndef KVIPS_AXI4_LITE_IF_SV
`define KVIPS_AXI4_LITE_IF_SV

interface axi4_lite_if #(
  parameter int ADDR_W = 32,
  parameter int DATA_W = 32
) (
  input logic aclk,
  input logic areset_n
);
  localparam int STRB_W = DATA_W / 8;

  logic [ADDR_W-1:0] awaddr;
  logic              awvalid;
  logic              awready;

  logic [DATA_W-1:0] wdata;
  logic [STRB_W-1:0] wstrb;
  logic              wvalid;
  logic              wready;

  logic [1:0]        bresp;
  logic              bvalid;
  logic              bready;

  logic [ADDR_W-1:0] araddr;
  logic              arvalid;
  logic              arready;

  logic [DATA_W-1:0] rdata;
  logic [1:0]        rresp;
  logic              rvalid;
  logic              rready;
endinterface

`endif
