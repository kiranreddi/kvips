//------------------------------------------------------------------------------
// AHB Monitor (pipeline reconstruction + optional coverage)
//------------------------------------------------------------------------------
`ifndef KVIPS_AHB_MONITOR_SVH
`define KVIPS_AHB_MONITOR_SVH

class ahb_monitor #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2,
  bit HAS_HMASTLOCK = 1'b0
) extends uvm_component;

  localparam string RID = "AHB_MON";

`ifdef VERILATOR
  ahb_cfg#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK) cfg;
  /* verilator lint_off UNSUPPORTED */
  virtual ahb_if #(
    .ADDR_W(ADDR_W),
    .DATA_W(DATA_W),
    .HAS_HMASTLOCK(HAS_HMASTLOCK),
    .HRESP_W(HRESP_W)
  ) vif;
  /* verilator lint_on UNSUPPORTED */
`else
  typedef virtual ahb_if #(
    .ADDR_W(ADDR_W),
    .DATA_W(DATA_W),
    .HAS_HMASTLOCK(HAS_HMASTLOCK),
    .HRESP_W(HRESP_W)
  ) ahb_vif_t;
  ahb_cfg#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK) cfg;
  ahb_vif_t                           vif;
`endif

  uvm_analysis_port #(ahb_item#(ADDR_W, DATA_W, HRESP_W)) ap;

`ifdef VERILATOR
`define AHB_MON_CB  vif
`define AHB_MON_EVT posedge vif.HCLK
`else
`define AHB_MON_CB  vif.cb_mon
`define AHB_MON_EVT vif.cb_mon
`endif

  typedef struct packed {
    bit                valid;
    bit                write;
    logic [ADDR_W-1:0] addr;
    ahb_size_e         size;
    ahb_burst_e        burst;
    logic [3:0]        prot;
    bit                lock;
  } ctrl_t;

  ctrl_t ctrl_pipe;
  ctrl_t ctrl_data;

  int unsigned stall_cnt;

  // Functional coverage:
  // - Single covergroup to avoid VCS limitations around creating embedded
  //   covergroups outside the class constructor.
  // - Config-driven ignore_bins prevent "disabled feature" bins from dragging
  //   down coverage for a given run.
`ifndef VERILATOR
  covergroup cg with function sample(
    bit          write,
    ahb_size_e   size,
    ahb_burst_e  burst,
    int unsigned stall_cycles,
    ahb_resp_e   resp
  );
    option.per_instance = 1;

    cp_rw: coverpoint write;

    cp_size: coverpoint size {
      bins b8   = {AHB_SIZE_8};
      bins b16  = {AHB_SIZE_16};
      bins b32  = {AHB_SIZE_32};
      bins b64  = {AHB_SIZE_64};
      // Ignore bins that are structurally impossible for a given DATA_W.
      // (This is parameter-driven, so it avoids URG "shape" explosion.)
      ignore_bins dis64 = {AHB_SIZE_64} iff (DATA_W < 64);
      // In AHB-Lite integration (HRESP_W==1) we treat these ports as simple
      // register-style access paths: focus coverage on SIZE_32.
      ignore_bins lite_non32 = {AHB_SIZE_8, AHB_SIZE_16, AHB_SIZE_64} iff (HRESP_W == 1);
    }

    cp_burst: coverpoint burst {
      bins single = {AHB_BURST_SINGLE};
      bins incr   = {AHB_BURST_INCR};
      bins incr4  = {AHB_BURST_INCR4};
      bins incr8  = {AHB_BURST_INCR8};
      bins incr16 = {AHB_BURST_INCR16};
      bins wrap4  = {AHB_BURST_WRAP4};
      bins wrap8  = {AHB_BURST_WRAP8};
      bins wrap16 = {AHB_BURST_WRAP16};
      // Same AHB-Lite integration assumption: only SINGLE transfers expected.
      ignore_bins lite_non_single = {AHB_BURST_INCR, AHB_BURST_INCR4, AHB_BURST_INCR8, AHB_BURST_INCR16,
                                     AHB_BURST_WRAP4, AHB_BURST_WRAP8, AHB_BURST_WRAP16} iff (HRESP_W == 1);
    }

    cp_stall: coverpoint stall_cycles {
      bins s0  = {0};
      bins s1  = {1};
      bins s2  = {[2:3]};
      bins s4  = {[4:7]};
      bins s8  = {[8:$]};
    }

    cp_resp: coverpoint resp {
      bins okay = {AHB_RESP_OKAY};
      bins err  = {AHB_RESP_ERROR};
      // RETRY/SPLIT are AHB Full responses. We don't treat them as a required
      // closure target in the NIC TB integration (and many environments never
      // generate them), so keep the bins defined but don't cross them.
    }

    cr_rw_size: cross cp_rw, cp_size;
    cr_burst_stall: cross cp_burst, cp_stall;
  endgroup
`endif

  `uvm_component_param_utils(ahb_monitor#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK))

  function new(string name, uvm_component parent);
    super.new(name, parent);
    ap = new("ap", this);
`ifndef VERILATOR
    cg = new();
`endif
  endfunction

  function ctrl_t sample_ctrl();
    ctrl_t c;
    c.valid = (`AHB_MON_CB.HSEL && `AHB_MON_CB.HTRANS[1] && `AHB_MON_CB.HREADY);
    c.write = `AHB_MON_CB.HWRITE;
    c.addr  = `AHB_MON_CB.HADDR;
    c.size  = ahb_size_e'(`AHB_MON_CB.HSIZE);
    c.burst = ahb_burst_e'(`AHB_MON_CB.HBURST);
    c.prot  = `AHB_MON_CB.HPROT;
    c.lock  = `AHB_MON_CB.HMASTLOCK;
    return c;
  endfunction

  function automatic ctrl_t clear_ctrl();
    ctrl_t c;
    c.valid = 1'b0;
    c.write = 1'b0;
    c.addr  = '0;
    c.size  = AHB_SIZE_8;
    c.burst = AHB_BURST_SINGLE;
    c.prot  = '0;
    c.lock  = 1'b0;
    return c;
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);

    if (!uvm_config_db#(ahb_cfg#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK))::get(this, "", "cfg", cfg)) begin
      `uvm_fatal(RID, "Missing cfg in config DB (key: cfg)")
    end
    vif = cfg.vif;
    if (vif == null) `uvm_fatal(RID, "cfg.vif is null")

    if (!cfg.monitor_enable) begin
      // Keep component alive but inactive (avoids fork/join ordering surprises
      // in environments that expect the monitor to exist).
      forever @(`AHB_MON_EVT);
    end

    ctrl_pipe = clear_ctrl();
    ctrl_data = clear_ctrl();
    stall_cnt = 0;

    @(posedge vif.HCLK);
    while (!vif.HRESETn) begin
      @(posedge vif.HCLK);
      ctrl_pipe = clear_ctrl();
      ctrl_data = clear_ctrl();
      stall_cnt = 0;
    end

    forever begin
      @(`AHB_MON_EVT);

      if (!vif.HRESETn) begin
        ctrl_pipe = clear_ctrl();
        ctrl_data = clear_ctrl();
        stall_cnt = 0;
        continue;
      end

      if (!`AHB_MON_CB.HREADY) begin
        // Stalling the current data phase.
        if (ctrl_data.valid) stall_cnt++;
        continue;
      end

      // Data phase completion for ctrl_data
      if (ctrl_data.valid) begin
        ahb_item#(ADDR_W, DATA_W, HRESP_W) t;
        t = ahb_item#(ADDR_W, DATA_W, HRESP_W)::type_id::create("t");
        t.write = ctrl_data.write;
        t.addr  = ctrl_data.addr;
        t.size  = ctrl_data.size;
        t.burst = ctrl_data.burst;
        t.prot  = ctrl_data.prot;
        t.lock  = ctrl_data.lock;
        t.len   = 1;
        t.post_randomize();
        t.wait_cycles[0] = stall_cnt;
        t.resp[0]        = `AHB_MON_CB.HRESP;
        if (ctrl_data.write) begin
          t.wdata[0] = `AHB_MON_CB.HWDATA;
        end else begin
          t.rdata[0] = `AHB_MON_CB.HRDATA;
        end
        ap.write(t);

        if (cfg.coverage_enable) begin
`ifndef VERILATOR
          cg.sample(ctrl_data.write, ctrl_data.size, ctrl_data.burst, stall_cnt, ahb_resp_e'(vif.HRESP));
`endif
        end
        if (cfg.trace_enable) begin
          `uvm_info(RID, t.convert2string(), UVM_MEDIUM)
        end
      end

      // Shift pipeline (ready cycle)
      stall_cnt = 0;
      ctrl_data = ctrl_pipe;
      ctrl_pipe = sample_ctrl();
    end
  endtask

endclass

`undef AHB_MON_CB
`undef AHB_MON_EVT

`endif // KVIPS_AHB_MONITOR_SVH
