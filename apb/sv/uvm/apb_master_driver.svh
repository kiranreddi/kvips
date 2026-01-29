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

  typedef virtual apb_if #(ADDR_W, DATA_W, NSEL) apb_vif_t;

  apb_cfg#(ADDR_W, DATA_W, NSEL) cfg;
  apb_vif_t vif;

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
    vif.cb_m.PSEL    <= '0;
    vif.cb_m.PENABLE <= 1'b0;
    vif.cb_m.PWRITE  <= 1'b0;
    vif.cb_m.PADDR   <= '0;
    vif.cb_m.PWDATA  <= '0;
    vif.cb_m.PPROT   <= 3'b000;
    vif.cb_m.PSTRB   <= '0;
  endtask

  task automatic wait_reset_release();
    drive_idle();
    while (vif.PRESETn !== 1'b1) @(vif.cb_m);
    @(vif.cb_m);
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
    if (cfg.randomize_pstrb) v = $urandom();
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
    vif.cb_m.PADDR   <= tr.addr;
    vif.cb_m.PWRITE  <= tr.write;
    vif.cb_m.PWDATA  <= tr.wdata;
    vif.cb_m.PSEL    <= sel;
    vif.cb_m.PENABLE <= 1'b0;
    vif.cb_m.PPROT   <= pprot_v;
    vif.cb_m.PSTRB   <= pstrb_v;
    @(vif.cb_m);

    // ENABLE phase
    vif.cb_m.PENABLE <= 1'b1;
    // Advance into the first ACCESS cycle. APB completes in an ACCESS cycle,
    // not in the same delta-cycle as PENABLE assertion.
    @(vif.cb_m);

    wait_c = 0;
    tr.start_t = $time;
    while (vif.cb_m.PREADY !== 1'b1) begin
      wait_c++;
      @(vif.cb_m);
    end

    // COMPLETE
    tr.wait_cycles = wait_c;
    tr.slverr = (vif.cb_m.PSLVERR === 1'b1);
    tr.resp   = tr.slverr ? APB_RESP_ERR : APB_RESP_OK;
    if (!tr.write) tr.rdata = vif.cb_m.PRDATA;
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
      vif.cb_m.PSEL    <= '0;
      vif.cb_m.PENABLE <= 1'b0;
      @(vif.cb_m);
    end else begin
      // Continuous mode: drop PENABLE, keep PSEL asserted and update address/data in next setup cycle.
      vif.cb_m.PENABLE <= 1'b0;
      @(vif.cb_m);
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

`endif // KVIPS_APB_MASTER_DRIVER_SVH
