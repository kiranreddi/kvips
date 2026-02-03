//------------------------------------------------------------------------------
// APB Master Driver
//------------------------------------------------------------------------------
`ifndef KVIPS_APB_MASTER_DRIVER_SVH
`define KVIPS_APB_MASTER_DRIVER_SVH

class apb_master_driver #(
  int ADDR_W = 32,
  int DATA_W = 32,
  int NSEL   = 1
) extends uvm_driver #(apb_item#(ADDR_W, DATA_W));

  localparam int STRB_W = (DATA_W/8);
  localparam string RID = "APB_MDRV";

  typedef virtual interface apb_if #(ADDR_W, DATA_W, NSEL) apb_vif_t;

  apb_cfg#(ADDR_W, DATA_W, NSEL) cfg;
  apb_vif_t vif;

`ifdef VERILATOR
  `define APB_M_CB vif
  `define APB_M_EVT @(posedge vif.PCLK)
`else
  `define APB_M_CB vif.cb_m
  `define APB_M_EVT @(vif.cb_m)
`endif

  `uvm_component_param_utils(apb_master_driver#(ADDR_W, DATA_W, NSEL))

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(apb_cfg#(ADDR_W, DATA_W, NSEL))::get(this, "", "cfg", cfg)) begin
      `uvm_fatal(RID, "Missing cfg in config DB (key: cfg)")
    end
    vif = cfg.vif;
    if (vif == null) `uvm_fatal(RID, "cfg.vif is null")
    cfg.apply_plusargs();
  endfunction

  task automatic drive_idle();
    `APB_M_CB.PSEL    <= '0;
    `APB_M_CB.PENABLE <= 1'b0;
    `APB_M_CB.PWRITE  <= 1'b0;
    `APB_M_CB.PADDR   <= '0;
    `APB_M_CB.PWDATA  <= '0;
    `APB_M_CB.PPROT   <= 3'b000;
    `APB_M_CB.PSTRB   <= '0;
  endtask

  task automatic wait_reset_release();
    drive_idle();
    while (vif.PRESETn !== 1'b1) `APB_M_EVT;
    `APB_M_EVT;
  endtask

  function automatic logic [2:0] choose_pprot(apb_item#(ADDR_W, DATA_W) tr);
    logic [2:0] v;
    if (!cfg.is_apb4()) return 3'b000;
    v = cfg.default_pprot;
    if (cfg.randomize_pprot) v = $urandom_range(0, 7);
    if (tr.prot !== 'x) v = tr.prot;
    return v;
  endfunction

  function automatic logic [STRB_W-1:0] choose_pstrb(apb_item#(ADDR_W, DATA_W) tr);
    logic [STRB_W-1:0] v;
    v = '1;
    if (!cfg.is_apb4()) return v;
    v = cfg.default_pstrb;
    if (cfg.randomize_pstrb) v = $urandom_range(0, (1 << STRB_W) - 1);
    if (tr.strb !== 'x) v = tr.strb;
    return v;
  endfunction

  task automatic do_transfer(apb_item#(ADDR_W, DATA_W) tr);
    int unsigned wait_c;
    logic [NSEL-1:0] sel;
    logic [2:0] pprot_v;
    logic [STRB_W-1:0] pstrb_v;
    sel = '0;
    if (cfg.sel_index < NSEL) sel[cfg.sel_index] = 1'b1;
    else sel[0] = 1'b1;

    pprot_v = choose_pprot(tr);
    pstrb_v = choose_pstrb(tr);
    tr.prot = pprot_v;
    tr.strb = pstrb_v;

    // SETUP phase
    `APB_M_CB.PADDR   <= tr.addr;
    `APB_M_CB.PWRITE  <= tr.write;
    `APB_M_CB.PWDATA  <= tr.wdata;
    `APB_M_CB.PSEL    <= sel;
    `APB_M_CB.PENABLE <= 1'b0;
    `APB_M_CB.PPROT   <= pprot_v;
    `APB_M_CB.PSTRB   <= pstrb_v;
    `APB_M_EVT;

    // ENABLE phase
    `APB_M_CB.PENABLE <= 1'b1;
    // Advance into the first ACCESS cycle. APB completes in an ACCESS cycle,
    // not in the same delta-cycle as PENABLE assertion.
    `APB_M_EVT;

    wait_c = 0;
    tr.start_t = $time;
    while (`APB_M_CB.PREADY !== 1'b1) begin
      wait_c++;
      `APB_M_EVT;
    end

    // COMPLETE
    tr.wait_cycles = wait_c;
    tr.slverr = (`APB_M_CB.PSLVERR === 1'b1);
    tr.resp   = tr.slverr ? APB_RESP_ERR : APB_RESP_OK;
    if (!tr.write) tr.rdata = `APB_M_CB.PRDATA;
    tr.end_t = $time;

    if (cfg.trace_enable) begin
      `uvm_info(RID,
        $sformatf("%s addr=0x%0h wdata=0x%0h rdata=0x%0h pstrb=0x%0h pprot=0x%0h wait=%0d slverr=%0d",
          tr.write ? "WR" : "RD",
          tr.addr, tr.wdata, tr.rdata, pstrb_v, pprot_v, wait_c, tr.slverr),
        UVM_MEDIUM)
    end

    // Return to SETUP/IDLE for next transfer.
    if (cfg.drop_psel_between) begin
      `APB_M_CB.PSEL    <= '0;
      `APB_M_CB.PENABLE <= 1'b0;
      `APB_M_EVT;
    end else begin
      // Continuous mode: drop PENABLE, keep PSEL asserted and update address/data in next setup cycle.
      `APB_M_CB.PENABLE <= 1'b0;
      `APB_M_EVT;
    end
  endtask

  task run_phase(uvm_phase phase);
    apb_item#(ADDR_W, DATA_W) tr;
    wait_reset_release();

    forever begin
      seq_item_port.get_next_item(tr);
      if (tr == null) begin
        seq_item_port.item_done();
        continue;
      end

      // Force APB3 semantics.
      if (!cfg.is_apb4()) begin
        tr.prot = 3'b000;
        tr.strb = '1;
      end

      do_transfer(tr);
      seq_item_port.item_done();
    end
  endtask

endclass

`undef APB_M_CB
`undef APB_M_EVT

`endif // KVIPS_APB_MASTER_DRIVER_SVH
