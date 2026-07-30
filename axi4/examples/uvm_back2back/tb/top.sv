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
    string test_name;
    bit do_midrun_reset;
    test_name = "";
    void'($value$plusargs("UVM_TESTNAME=%s", test_name));
    do_midrun_reset = (test_name == "axi4_b2b_reset_recovery_test") ||
                      (test_name == "axi4_b2b_nonpipelined_reset_test") ||
                      $test$plusargs("AXI4_RESET_PULSE");
    areset_n = 0;
    repeat (10) @(posedge aclk);
    areset_n = 1;
    if (do_midrun_reset) begin
      // Leave enough time for the pipelined BFM to have requests in flight,
      // then exercise the reset-flush path before traffic resumes.
      repeat (20) @(posedge aclk);
      areset_n = 0;
      repeat (5) @(posedge aclk);
      areset_n = 1;
    end
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
