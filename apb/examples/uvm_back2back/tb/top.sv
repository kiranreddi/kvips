//------------------------------------------------------------------------------
// APB back2back example top
//------------------------------------------------------------------------------
`timescale 1ns/1ps

module tb_top;

  import uvm_pkg::*;
  import tb_pkg::*;

  localparam int ADDR_W = 16;
  localparam int DATA_W = 32;
  localparam int NSEL   = 1;

  logic PCLK;
  logic PRESETn;

  apb_if #(ADDR_W, DATA_W, NSEL) apb (.*);

  // Clock/reset
  initial begin
    PCLK = 0;
    forever #5ns PCLK = ~PCLK;
  end

  initial begin
    PRESETn = 1'b0;
    repeat (5) @(posedge PCLK);
    PRESETn = 1'b1;
  end

  // Optional wave dump
  initial begin
    `include "kvips_wave_dump.svh"
    `KVIPS_MAYBE_ENABLE_WAVES("kvips_apb_b2b")
  end

  initial begin
    uvm_config_db#(virtual interface apb_if #(ADDR_W, DATA_W, NSEL))::set(null, "*", "vif", apb);
    run_test();
  end

endmodule
