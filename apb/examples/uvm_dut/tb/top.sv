`timescale 1ns/1ps

module tb_top;
  import uvm_pkg::*;
  import apb_uvm_pkg::*;
  import tb_pkg::*;

  localparam int ADDR_W = 16;
  localparam int DATA_W = 32;
  localparam int NSEL   = 1;

  logic PCLK;
  logic PRESETn;

  apb_if #(ADDR_W, DATA_W, NSEL) apb (.*);

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
    `include "kvips_wave_dump.svh"
    `KVIPS_MAYBE_ENABLE_WAVES("kvips_apb_dut")
  end

`ifdef VERILATOR
  // Keep simulation running long enough under Verilator UVM/no-DPI flow.
  initial begin
    longint unsigned wr_cnt, rd_cnt, err_cnt;
    bit en;
    longint unsigned mis;
    apb_scoreboard#(ADDR_W, DATA_W) sb_h;
    wait (PRESETn === 1'b1);
    repeat (5000) @(posedge PCLK);
    if ($cast(sb_h, uvm_root::get().find("uvm_test_top.sb"))) begin
      sb_h.get_summary(en, wr_cnt, rd_cnt, err_cnt, mis);
      uvm_report_info("APB_SCB",
        $sformatf("APB SB summary: enable=%0d wr=%0d rd=%0d err=%0d mismatch=%0d",
          en, wr_cnt, rd_cnt, err_cnt, mis),
        UVM_NONE);
      if (en && ((wr_cnt + rd_cnt) == 0))
        uvm_report_error("APB_SCB", "APB scoreboard observed zero transactions");
    end
    uvm_report_server::get_server().report_summarize();
    $finish;
  end
`endif

  initial begin
    uvm_config_db#(virtual interface apb_if #(ADDR_W, DATA_W, NSEL))::set(null, "*", "vif", apb);
`ifdef VERILATOR
    uvm_root::get().set_finish_on_completion(1'b0);
`endif
    run_test();
  end
endmodule
