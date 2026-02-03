//------------------------------------------------------------------------------
// Demo Top
//------------------------------------------------------------------------------

`timescale 1ns/1ps

module top;

  import uvm_pkg::*;
  import tb_pkg::*;

  localparam int ADDR_W = 32;
  localparam int DATA_W = 64;
  localparam int ID_W   = 4;
  localparam int USER_W = 1;

  logic aclk;
  logic areset_n;

  axi4_if #(ADDR_W, DATA_W, ID_W, USER_W) axi (.*);

  // Clock/reset
  initial begin
    aclk = 0;
    forever #5 aclk = ~aclk;
  end

  initial begin
    areset_n = 0;
    repeat (10) @(posedge aclk);
    areset_n = 1;
  end

  // Optional wave dump
  initial begin
    `include "kvips_wave_dump.svh"
    `KVIPS_MAYBE_ENABLE_WAVES("kvips_axi4_b2b")
  end

  // Provide vif to the test
  initial begin
    uvm_config_db#(virtual interface axi4_if #(ADDR_W, DATA_W, ID_W, USER_W))::set(null, "*", "vif", axi);
    run_test();
  end

endmodule
