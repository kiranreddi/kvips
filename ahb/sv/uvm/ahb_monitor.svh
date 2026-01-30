//------------------------------------------------------------------------------
// AHB Monitor (pipeline reconstruction + optional coverage)
//------------------------------------------------------------------------------
`ifndef KVIPS_AHB_MONITOR_SVH
`define KVIPS_AHB_MONITOR_SVH

class ahb_monitor #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2
) extends uvm_component;

  localparam string RID = "AHB_MON";

  typedef virtual ahb_if #(ADDR_W, DATA_W, .HRESP_W(HRESP_W)) ahb_vif_t;

  ahb_cfg#(ADDR_W, DATA_W, HRESP_W) cfg;
  ahb_vif_t                         vif;

  uvm_analysis_port #(ahb_item#(ADDR_W, DATA_W, HRESP_W)) ap;

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

  covergroup cg_ahb;
    option.per_instance = 1;

    cp_rw: coverpoint ctrl_data.write iff (ctrl_data.valid && vif.HREADY);
    cp_size: coverpoint ctrl_data.size iff (ctrl_data.valid && vif.HREADY) {
      bins b8   = {AHB_SIZE_8};
      bins b16  = {AHB_SIZE_16};
      bins b32  = {AHB_SIZE_32};
      bins b64  = {AHB_SIZE_64};
    }
    cp_burst: coverpoint ctrl_data.burst iff (ctrl_data.valid && vif.HREADY);
    cp_stall: coverpoint stall_cnt iff (ctrl_data.valid && vif.HREADY) {
      bins s0  = {0};
      bins s1  = {1};
      bins s2  = {[2:3]};
      bins s4  = {[4:7]};
      bins s8  = {[8:$]};
    }
    cp_resp: coverpoint vif.HRESP iff (ctrl_data.valid && vif.HREADY);

    cr_rw_size: cross cp_rw, cp_size;
    cr_burst_stall: cross cp_burst, cp_stall;
  endgroup

  `uvm_component_param_utils(ahb_monitor#(ADDR_W, DATA_W, HRESP_W))

  function new(string name, uvm_component parent);
    super.new(name, parent);
    ap = new("ap", this);
  endfunction

  function ctrl_t sample_ctrl();
    ctrl_t c;
    c.valid = (vif.cb_mon.HSEL && vif.cb_mon.HTRANS[1] && vif.cb_mon.HREADY);
    c.write = vif.cb_mon.HWRITE;
    c.addr  = vif.cb_mon.HADDR;
    c.size  = ahb_size_e'(vif.cb_mon.HSIZE);
    c.burst = ahb_burst_e'(vif.cb_mon.HBURST);
    c.prot  = vif.cb_mon.HPROT;
    c.lock  = vif.cb_mon.HMASTLOCK;
    return c;
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);

    if (!uvm_config_db#(ahb_cfg#(ADDR_W, DATA_W, HRESP_W))::get(this, "", "cfg", cfg)) begin
      `uvm_fatal(RID, "Missing cfg in config DB (key: cfg)")
    end
    vif = cfg.vif;
    if (vif == null) `uvm_fatal(RID, "cfg.vif is null")

    ctrl_pipe = '{default:'0};
    ctrl_data = '{default:'0};
    stall_cnt = 0;

    if (cfg.coverage_enable) cg_ahb = new();

    @(posedge vif.HCLK);
    while (!vif.HRESETn) begin
      @(posedge vif.HCLK);
      ctrl_pipe = '{default:'0};
      ctrl_data = '{default:'0};
      stall_cnt = 0;
    end

    forever begin
      @(vif.cb_mon);

      if (!vif.HRESETn) begin
        ctrl_pipe = '{default:'0};
        ctrl_data = '{default:'0};
        stall_cnt = 0;
        continue;
      end

      if (!vif.cb_mon.HREADY) begin
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
        t.resp[0]        = vif.cb_mon.HRESP;
        if (ctrl_data.write) begin
          t.wdata[0] = vif.cb_mon.HWDATA;
        end else begin
          t.rdata[0] = vif.cb_mon.HRDATA;
        end
        ap.write(t);

        if (cfg.coverage_enable) cg_ahb.sample();
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

`endif // KVIPS_AHB_MONITOR_SVH
