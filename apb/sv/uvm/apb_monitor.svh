//------------------------------------------------------------------------------
// APB Monitor
//------------------------------------------------------------------------------
`ifndef KVIPS_APB_MONITOR_SVH
`define KVIPS_APB_MONITOR_SVH

class apb_monitor #(
  int ADDR_W = 32,
  int DATA_W = 32,
  int NSEL   = 1
) extends uvm_component;

  localparam int STRB_W = (DATA_W/8);
  localparam string RID = "APB_MON";

  typedef virtual apb_if #(ADDR_W, DATA_W, NSEL) apb_vif_t;
  typedef apb_item#(ADDR_W, DATA_W) item_t;

  apb_cfg#(ADDR_W, DATA_W, NSEL) cfg;
  apb_vif_t vif;

  uvm_analysis_port #(item_t) ap;

  // Summary counters
  longint unsigned sum_wr;
  longint unsigned sum_rd;
  longint unsigned sum_err;

  // Wait-state tracking
  bit          in_access;
  int unsigned cur_wait;
  item_t       cur_tr;

  covergroup cov with function sample(bit write, int unsigned wait_cycles, bit slverr, logic [STRB_W-1:0] strb, logic [2:0] prot);
    option.per_instance = 1;
    cp_wr: coverpoint write;
    cp_wait: coverpoint wait_cycles {
      bins w0  = {0};
      bins w1  = {1};
      bins w2_3 = {[2:3]};
      bins w4_7 = {[4:7]};
      bins w8p  = {[8:$]};
    }
    cp_err: coverpoint slverr;
    cp_strb_pop: coverpoint $countones(strb) {
      bins none   = {0};
      bins single = {1};
      bins some   = {[2:(STRB_W > 1) ? (STRB_W-1) : 1]};
      bins full   = {STRB_W};
    }
    cp_prot: coverpoint prot;
    cx_wr_err: cross cp_wr, cp_err;
  endgroup

  `uvm_component_param_utils(apb_monitor#(ADDR_W, DATA_W, NSEL))

  function new(string name, uvm_component parent);
    super.new(name, parent);
    ap = new("ap", this);
    cov = new();
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(apb_cfg#(ADDR_W, DATA_W, NSEL))::get(this, "", "cfg", cfg)) begin
      `uvm_fatal(RID, "Missing cfg in config DB (key: cfg)")
    end
    vif = cfg.vif;
    if (vif == null) `uvm_fatal(RID, "cfg.vif is null")
    cfg.apply_plusargs();

    sum_wr = 0;
    sum_rd = 0;
    sum_err = 0;
    in_access = 0;
    cur_wait = 0;
    cur_tr = null;
  endfunction

  function automatic void maybe_record(item_t tr, string label);
    if (!cfg.tr_record_enable) return;
    void'(begin_tr(tr, cfg.tr_stream_name, label));
    tr.record();
    end_tr(tr);
  endfunction

  function automatic void get_summary(
    output longint unsigned wr_cnt,
    output longint unsigned rd_cnt,
    output longint unsigned err_cnt
  );
    wr_cnt = sum_wr;
    rd_cnt = sum_rd;
    err_cnt = sum_err;
  endfunction

  task run_phase(uvm_phase phase);
    if (!cfg.monitor_enable) return;
    while (vif.PRESETn !== 1'b1) @(vif.cb_mon);

    forever begin
      @(vif.cb_mon);

      if (vif.PRESETn !== 1'b1) begin
        in_access = 0;
        cur_wait = 0;
        cur_tr = null;
        continue;
      end

      // Setup phase seen: allocate a new transaction.
      if ((|vif.cb_mon.PSEL) && (vif.cb_mon.PENABLE === 1'b0)) begin
        cur_tr = new("apb_mon_tr");
        cur_tr.addr  = vif.cb_mon.PADDR;
        cur_tr.write = (vif.cb_mon.PWRITE === 1'b1);
        cur_tr.wdata = vif.cb_mon.PWDATA;
        cur_tr.prot  = vif.cb_mon.PPROT;
        cur_tr.strb  = cfg.is_apb4() ? vif.cb_mon.PSTRB : '1;
        cur_tr.start_t = $time;
        cur_wait = 0;
        in_access = 1;
      end

      // Access phase: count wait cycles.
      if ((|vif.cb_mon.PSEL) && (vif.cb_mon.PENABLE === 1'b1) && in_access) begin
        if (vif.cb_mon.PREADY !== 1'b1) begin
          cur_wait++;
        end else begin
          // Completion cycle.
          cur_tr.wait_cycles = cur_wait;
          cur_tr.slverr = (vif.cb_mon.PSLVERR === 1'b1);
          cur_tr.resp   = cur_tr.slverr ? APB_RESP_ERR : APB_RESP_OK;
          if (!cur_tr.write) cur_tr.rdata = vif.cb_mon.PRDATA;
          cur_tr.end_t = $time;

          if (cur_tr.write) sum_wr++; else sum_rd++;
          if (cur_tr.slverr) sum_err++;

          if (cfg.coverage_enable) cov.sample(cur_tr.write, cur_tr.wait_cycles, cur_tr.slverr, cur_tr.strb, cur_tr.prot);
          maybe_record(cur_tr, cur_tr.write ? "apb_write" : "apb_read");
          ap.write(cur_tr);
          if (cfg.trace_enable) `uvm_info(RID, {"MON txn:\n", cur_tr.sprint()}, UVM_LOW)

          in_access = 0;
          cur_wait = 0;
          cur_tr = null;
        end
      end
    end
  endtask

  function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    if (!cfg.monitor_enable) return;
    `uvm_info(RID,
      $sformatf("APB summary: wr=%0d rd=%0d err=%0d", sum_wr, sum_rd, sum_err),
      UVM_LOW)
  endfunction

endclass

`endif // KVIPS_APB_MONITOR_SVH
