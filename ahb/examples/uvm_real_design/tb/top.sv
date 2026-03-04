`timescale 1ns/1ps

module top;
  import uvm_pkg::*;
  import ahb_uvm_pkg::*;
  import tb_pkg::*;

  logic HCLK;
  logic HRESETn;

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

  ahb_ram_slave #(.ADDR_W(ADDR_W), .DATA_W(DATA_W), .HRESP_W(HRESP_W), .WAIT_STATES(1)) dut (
    .HCLK(HCLK), .HRESETn(HRESETn),
    .HADDR(ahb_if0.HADDR), .HTRANS(ahb_if0.HTRANS), .HWRITE(ahb_if0.HWRITE), .HSIZE(ahb_if0.HSIZE), .HBURST(ahb_if0.HBURST), .HPROT(ahb_if0.HPROT),
    .HSEL(ahb_if0.HSEL), .HWDATA(ahb_if0.HWDATA), .HREADY(ahb_if0.HREADY), .HREADYOUT(ahb_if0.HREADYOUT), .HRESP(ahb_if0.HRESP), .HRDATA(ahb_if0.HRDATA)
  );

  assign ahb_if0.HSEL = 1'b1;
`ifdef VERILATOR
  always_ff @(posedge HCLK or negedge HRESETn) begin
    if (!HRESETn) ahb_if0.HREADY <= 1'b1;
    else          ahb_if0.HREADY <= ahb_if0.HREADYOUT;
  end
`else
  assign ahb_if0.HREADY = ahb_if0.HREADYOUT;
`endif

  initial begin
    `include "kvips_wave_dump.svh"
    `KVIPS_MAYBE_ENABLE_WAVES("kvips_ahb_real_design")
  end

`ifdef VERILATOR
  // Keep simulation running long enough under Verilator UVM/no-DPI flow.
  initial begin
    bit en;
    longint unsigned wr_cnt, rd_cnt, err_cnt, mis_cnt;
    longint unsigned log_wr_cnt, log_rd_cnt, log_err_cnt, log_stall_cnt;
    ahb_scoreboard#(.ADDR_W(ADDR_W), .DATA_W(DATA_W), .HRESP_W(HRESP_W)) sb_h;
    ahb_txn_logger#(.ADDR_W(ADDR_W), .DATA_W(DATA_W), .HRESP_W(HRESP_W)) log_h;
    wait (HRESETn === 1'b1);
    repeat (5000) @(posedge HCLK);
    if ($cast(sb_h, uvm_root::get().find("uvm_test_top.env.sb"))) begin
      sb_h.get_summary(en, wr_cnt, rd_cnt, err_cnt, mis_cnt);
      uvm_report_info("AHB_SCB",
        $sformatf("AHB SB summary: enable=%0d wr=%0d rd=%0d err=%0d mismatch=%0d",
          en, wr_cnt, rd_cnt, err_cnt, mis_cnt),
        UVM_NONE);
    end
    if ($cast(log_h, uvm_root::get().find("uvm_test_top.env.logger"))) begin
      log_h.get_summary(log_wr_cnt, log_rd_cnt, log_err_cnt, log_stall_cnt);
      uvm_report_info("AHB_LOG",
        $sformatf("AHB log summary: wr=%0d rd=%0d err=%0d stall_cycles=%0d",
          log_wr_cnt, log_rd_cnt, log_err_cnt, log_stall_cnt),
        UVM_NONE);
    end
    $finish;
  end
`endif

  initial begin
    uvm_config_db#(virtual interface ahb_if #(.ADDR_W(ADDR_W), .DATA_W(DATA_W), .HRESP_W(HRESP_W)))::set(null, "*", "vif", ahb_if0);
`ifdef VERILATOR
    uvm_root::get().set_finish_on_completion(1'b0);
`endif
    run_test();
  end
endmodule
