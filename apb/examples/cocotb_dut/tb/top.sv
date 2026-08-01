`timescale 1ns/1ps

module tb_top;
  import uvm_pkg::*;
  import apb_uvm_pkg::*;
  import tb_pkg::*;

  localparam int ADDR_W = 16;
  localparam int DATA_W = 32;
  localparam int NSEL   = 1;

  logic PCLK    /* verilator public_flat_rw */;
  logic PRESETn /* verilator public_flat_rw */;

  apb_if #(ADDR_W, DATA_W, NSEL) apb (.*);
  kvips_cocotb_bridge_if bridge (.clk(PCLK), .rst_n(PRESETn));

  apb_ram_slave #(
    .ADDR_W(ADDR_W), .DATA_W(DATA_W), .NSEL(NSEL),
    .MEM_BASE(0), .MEM_BYTES(4096), .WAIT_STATES(2)
  ) dut (
    .PCLK(PCLK), .PRESETn(PRESETn),
    .PADDR(apb.PADDR), .PSEL(apb.PSEL), .PENABLE(apb.PENABLE), .PWRITE(apb.PWRITE),
    .PWDATA(apb.PWDATA), .PRDATA(apb.PRDATA), .PREADY(apb.PREADY), .PSLVERR(apb.PSLVERR),
    .PPROT(apb.PPROT), .PSTRB(apb.PSTRB)
  );

  initial begin
    PCLK = 0;
    forever #5 PCLK = ~PCLK;
  end

  initial begin
    PRESETn = 1'b0;
    repeat (5) @(posedge PCLK);
    PRESETn = 1'b1;
  end

  initial begin
    uvm_config_db#(virtual interface apb_if #(ADDR_W, DATA_W, NSEL))::set(null, "*", "vif", apb);
    uvm_config_db#(virtual interface kvips_cocotb_bridge_if)::set(null, "*", "bridge", bridge);
`ifdef VERILATOR
    uvm_root::get().set_finish_on_completion(1'b0);
`endif
    run_test("apb_cocotb_bridge_test");
  end
endmodule
