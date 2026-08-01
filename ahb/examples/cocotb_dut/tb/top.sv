`timescale 1ns/1ps

module top;
  import uvm_pkg::*;
  import ahb_uvm_pkg::*;
  import tb_pkg::*;

  logic HCLK    /* verilator public_flat_rw */;
  logic HRESETn /* verilator public_flat_rw */;

  initial begin
    HCLK = 1'b0;
    forever #5 HCLK = ~HCLK;
  end

  initial begin
    HRESETn = 1'b0;
    repeat (10) @(posedge HCLK);
    HRESETn = 1'b1;
  end

  localparam int ADDR_W  = 16;
  localparam int DATA_W  = 32;
  localparam int HRESP_W = 2;

  ahb_if #(.ADDR_W(ADDR_W), .DATA_W(DATA_W), .HRESP_W(HRESP_W)) ahb_if0 (.HCLK(HCLK), .HRESETn(HRESETn));
  kvips_cocotb_bridge_if bridge (.clk(HCLK), .rst_n(HRESETn));

  ahb_ram_slave #(.ADDR_W(ADDR_W), .DATA_W(DATA_W), .HRESP_W(HRESP_W), .WAIT_STATES(1)) dut (
    .HCLK(HCLK), .HRESETn(HRESETn),
    .HADDR(ahb_if0.HADDR), .HTRANS(ahb_if0.HTRANS), .HWRITE(ahb_if0.HWRITE), .HSIZE(ahb_if0.HSIZE), .HBURST(ahb_if0.HBURST), .HPROT(ahb_if0.HPROT),
    .HSEL(ahb_if0.HSEL), .HWDATA(ahb_if0.HWDATA), .HREADY(ahb_if0.HREADY), .HREADYOUT(ahb_if0.HREADYOUT), .HRESP(ahb_if0.HRESP), .HRDATA(ahb_if0.HRDATA)
  );

  assign ahb_if0.HREADY = ahb_if0.HREADYOUT;

  initial begin
    uvm_config_db#(virtual interface ahb_if #(.ADDR_W(ADDR_W), .DATA_W(DATA_W), .HRESP_W(HRESP_W)))::set(null, "*", "vif", ahb_if0);
    uvm_config_db#(virtual interface kvips_cocotb_bridge_if)::set(null, "*", "bridge", bridge);
`ifdef VERILATOR
    uvm_root::get().set_finish_on_completion(1'b0);
`endif
    run_test("ahb_cocotb_bridge_test");
  end
endmodule
