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

  apb_ram_slave #(.ADDR_W(ADDR_W), .DATA_W(DATA_W), .NSEL(NSEL), .WAIT_STATES(1)) dut (
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
`ifdef VERILATOR
    PRESETn = 1'b1;
`else
    PRESETn = 1'b0;
    repeat (5) @(posedge PCLK);
    PRESETn = 1'b1;
`endif
  end

  initial begin
    `include "kvips_wave_dump.svh"
    `KVIPS_MAYBE_ENABLE_WAVES("kvips_apb_real_design")
  end

`ifdef VERILATOR
  // Keep run phase alive long enough under Verilator UVM/no-DPI flow.
  initial begin
    uvm_phase run_phase_h;
    uvm_objection run_obj_h;
    int tries;
    tries = 0;
    run_obj_h = null;
    while ((run_obj_h == null) && (tries < 1000)) begin
      run_phase_h = uvm_run_phase::get();
      run_obj_h = (run_phase_h == null) ? null : run_phase_h.get_objection();
      tries++;
      #1step;
    end
    if (run_obj_h != null) begin
      run_obj_h.raise_objection(uvm_root::get(), "kvips_verilator_runtime_hold");
      wait (PRESETn === 1'b1);
      repeat (2000) @(posedge PCLK);
      run_obj_h.drop_objection(uvm_root::get(), "kvips_verilator_runtime_hold");
    end
  end
`endif

  initial begin
    uvm_config_db#(virtual interface apb_if #(ADDR_W, DATA_W, NSEL))::set(null, "*", "vif", apb);
    run_test();
  end
endmodule
