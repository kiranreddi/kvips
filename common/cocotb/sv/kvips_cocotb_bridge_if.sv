//------------------------------------------------------------------------------
// KVIPS cocotb <-> UVM command/response/monitor bridge interface
//------------------------------------------------------------------------------
`timescale 1ns/1ps

interface kvips_cocotb_bridge_if (
  input logic clk,
  input logic rst_n
);
  // Mark bridge controls public for cocotb without --public-flat-rw (which
  // breaks Verilator UVM std::process codegen).
  // Host (cocotb) -> UVM bridge
  logic         req_valid  /* verilator public_flat_rw */;
  logic         req_ready  /* verilator public_flat_rw */;
  logic [7:0]   req_opcode /* verilator public_flat_rw */;
  logic [63:0]  req_a0     /* verilator public_flat_rw */;
  logic [63:0]  req_a1     /* verilator public_flat_rw */;
  logic [63:0]  req_a2     /* verilator public_flat_rw */;
  logic [63:0]  req_a3     /* verilator public_flat_rw */;
  logic [63:0]  req_a4     /* verilator public_flat_rw */;
  logic [63:0]  req_a5     /* verilator public_flat_rw */;
  logic [63:0]  req_a6     /* verilator public_flat_rw */;
  logic [63:0]  req_a7     /* verilator public_flat_rw */;

  // Burst payload (up to 16 beats x 64-bit) written by cocotb before WRITE_BURST
  logic [63:0]  beat_data [0:15] /* verilator public_flat_rw */;
  logic [7:0]   beat_strb [0:15] /* verilator public_flat_rw */;

  // UVM bridge -> Host
  logic         rsp_valid   /* verilator public_flat_rw */;
  logic         rsp_ready   /* verilator public_flat_rw */;
  logic [31:0]  rsp_status  /* verilator public_flat_rw */;
  logic [63:0]  rsp_d0      /* verilator public_flat_rw */;
  logic [63:0]  rsp_d1      /* verilator public_flat_rw */;
  logic [63:0]  rsp_d2      /* verilator public_flat_rw */;
  logic [63:0]  rsp_d3      /* verilator public_flat_rw */;

  // Read-burst response beats
  logic [63:0]  rsp_beat [0:15] /* verilator public_flat_rw */;

  // Monitor stream (UVM -> Host), one completed txn at a time
  logic         mon_valid  /* verilator public_flat_rw */;
  logic         mon_ready  /* verilator public_flat_rw */;
  logic [7:0]   mon_proto  /* verilator public_flat_rw */;
  logic         mon_write  /* verilator public_flat_rw */;
  logic [63:0]  mon_addr   /* verilator public_flat_rw */;
  logic [63:0]  mon_data   /* verilator public_flat_rw */;
  logic [31:0]  mon_resp   /* verilator public_flat_rw */;
  logic [31:0]  mon_strb   /* verilator public_flat_rw */;
  logic [31:0]  mon_len    /* verilator public_flat_rw */;
  logic [31:0]  mon_id     /* verilator public_flat_rw */;

  // Bridge readiness (UVM env built and serving)
  logic         bridge_ready /* verilator public_flat_rw */;

  modport host (
    input  clk, rst_n, req_ready, rsp_valid, rsp_status, rsp_d0, rsp_d1, rsp_d2, rsp_d3,
           rsp_beat, mon_valid, mon_proto, mon_write, mon_addr, mon_data, mon_resp,
           mon_strb, mon_len, mon_id, bridge_ready,
    output req_valid, req_opcode, req_a0, req_a1, req_a2, req_a3, req_a4, req_a5, req_a6, req_a7,
           beat_data, beat_strb, rsp_ready, mon_ready
  );

  modport uvm (
    input  clk, rst_n, req_valid, req_opcode, req_a0, req_a1, req_a2, req_a3, req_a4, req_a5, req_a6, req_a7,
           beat_data, beat_strb, rsp_ready, mon_ready,
    output req_ready, rsp_valid, rsp_status, rsp_d0, rsp_d1, rsp_d2, rsp_d3, rsp_beat,
           mon_valid, mon_proto, mon_write, mon_addr, mon_data, mon_resp, mon_strb, mon_len, mon_id,
           bridge_ready
  );
endinterface
