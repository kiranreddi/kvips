//------------------------------------------------------------------------------
// Demo Top
//------------------------------------------------------------------------------

`timescale 1ns/1ps

module top;

  import uvm_pkg::*;
  import tb_pkg::*;

  localparam int NUM_LANES   = 16;
  localparam int MAX_GEN     = 5;
  localparam int DATA_WIDTH  = 32;

  logic pclk;
  logic reset_n;
  logic refclk;

  pcie_pipe_if #(NUM_LANES, MAX_GEN, DATA_WIDTH) pcie (
    .pclk(pclk),
    .reset_n(reset_n)
  );

  // Dummy serial interface instance (allows running PIPE-mode tests on toolflows
  // that still elaborate Serial-mode code paths).
  pcie_serial_if #(NUM_LANES, MAX_GEN) pcie_ser (
    .refclk(refclk),
    .perst_n(reset_n)
  );

  // Clock/reset
  initial begin
    pclk = 0;
    forever #2 pclk = ~pclk;  // 250 MHz
  end

  initial begin
    refclk = 0;
    forever #5 refclk = ~refclk; // 100 MHz
  end

  initial begin
    reset_n = 0;
    repeat (20) @(posedge pclk);
    reset_n = 1;
  end

  // Optional wave dump
  initial begin
    `include "kvips_wave_dump.svh"
    `KVIPS_MAYBE_ENABLE_WAVES("kvips_pcie_b2b")
  end

  // Provide vif to the test
  initial begin
    // Set vif for the test (whole interface)
    uvm_config_db#(virtual pcie_pipe_if #(NUM_LANES, MAX_GEN, DATA_WIDTH))::set(null, "*", "vif", pcie);
    // Set vif_pipe mac modport for driver
    uvm_config_db#(virtual pcie_pipe_if #(NUM_LANES, MAX_GEN, DATA_WIDTH).mac)::set(null, "*drv*", "vif_pipe", pcie.mac);
    // Set vif_pipe monitor modport for monitor
    uvm_config_db#(virtual pcie_pipe_if #(NUM_LANES, MAX_GEN, DATA_WIDTH).monitor)::set(null, "*mon*", "vif_pipe", pcie.monitor);

    // Also register serial vifs (safe no-op for PIPE-mode tests)
    uvm_config_db#(virtual pcie_serial_if #(NUM_LANES, MAX_GEN).tx)::set(null, "*drv*", "vif_serial", pcie_ser.tx);
    uvm_config_db#(virtual pcie_serial_if #(NUM_LANES, MAX_GEN).monitor)::set(null, "*mon*", "vif_serial", pcie_ser.monitor);
    run_test();
  end

endmodule
