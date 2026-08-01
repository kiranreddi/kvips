//------------------------------------------------------------------------------
// AHB Slave Driver (single-slave responder + memory model)
//------------------------------------------------------------------------------
`ifndef KVIPS_AHB_SLAVE_DRIVER_SVH
`define KVIPS_AHB_SLAVE_DRIVER_SVH

class ahb_slave_driver #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2,
  bit HAS_HMASTLOCK = 1'b0
) extends uvm_component;

  localparam string RID = "AHB_SDRV";

`ifdef VERILATOR
  ahb_cfg#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK) cfg;
  virtual ahb_if #(
    .ADDR_W(ADDR_W),
    .DATA_W(DATA_W),
    .HAS_HMASTLOCK(HAS_HMASTLOCK),
    .HRESP_W(HRESP_W)
  ) vif;
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

  typedef logic [HRESP_W-1:0] hresp_t;

`ifdef VERILATOR
`define AHB_S_CB  vif
`define AHB_S_EVT posedge vif.HCLK
`else
`define AHB_S_CB  vif.cb_s
`define AHB_S_EVT vif.cb_s
`endif

  // Simple byte-addressed memory model
  byte unsigned mem[longint unsigned];

  // Pipeline tracking for data phase
  typedef struct packed {
    bit                valid;
    bit                write;
    logic [ADDR_W-1:0] addr;
    ahb_size_e         size;
    ahb_burst_e        burst;
    logic [3:0]        prot;
    bit                nonsec;
    bit                lock;
    ahb_resp_e         resp_kind;
  } ctrl_t;

  ctrl_t ctrl_pipe;   // accepted in the previous ready cycle (becomes data phase)
  ctrl_t ctrl_data;   // currently in data phase (when valid)

  int unsigned stall_rem; // remaining wait-state cycles for current data beat
  bit          resp_pending; // second cycle of a two-cycle non-OKAY response

  `uvm_component_param_utils(ahb_slave_driver#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK))

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function int unsigned data_bus_bytes();
    return (DATA_W/8);
  endfunction

  function automatic ctrl_t clear_ctrl();
    ctrl_t c;
    c.valid = 1'b0;
    c.write = 1'b0;
    c.addr  = '0;
    c.size  = AHB_SIZE_8;
    c.burst = AHB_BURST_SINGLE;
    c.prot  = '0;
    c.nonsec = 1'b0;
    c.lock  = 1'b0;
    c.resp_kind = AHB_RESP_OKAY;
    return c;
  endfunction

  function int unsigned size_bytes(ahb_size_e size);
    return (1 << size);
  endfunction

  function int unsigned data_lane(logic [ADDR_W-1:0] addr, int unsigned byte_offset);
    int unsigned lane;
    lane = int'(addr) % data_bus_bytes();
    if (cfg.endian == AHB_ENDIAN_BIG)
      return (data_bus_bytes() - 1) - (lane + byte_offset);
    return lane + byte_offset;
  endfunction

  function void write_bytes(logic [ADDR_W-1:0] addr, ahb_size_e size, logic [DATA_W-1:0] wdata);
    int unsigned sb = size_bytes(size);
    int unsigned lane = int'(addr) % data_bus_bytes();
    for (int unsigned i = 0; i < sb; i++) begin
      int unsigned byte_lane;
      if ((lane + i) < data_bus_bytes()) begin
        byte_lane = data_lane(addr, i);
        mem[longint'(addr) + longint'(i)] = wdata[(8*byte_lane) +: 8];
      end
    end
  endfunction

  function logic [DATA_W-1:0] read_bytes(logic [ADDR_W-1:0] addr, ahb_size_e size);
    logic [DATA_W-1:0] r;
    int unsigned sb = size_bytes(size);
    int unsigned lane = int'(addr) % data_bus_bytes();
    r = '0;
    for (int unsigned i = 0; i < sb; i++) begin
      int unsigned byte_lane;
      if ((lane + i) < data_bus_bytes()) begin
        byte_lane = data_lane(addr, i);
        if (mem.exists(longint'(addr) + longint'(i)))
          r[(8*byte_lane) +: 8] = mem[longint'(addr) + longint'(i)];
        else
          r[(8*byte_lane) +: 8] = 8'h00;
      end
    end
    return r;
  endfunction

  function logic [HRESP_W-1:0] resp_okay();
    if (HRESP_W == 1) return hresp_t'(1'b0);
    return hresp_t'(2'b00);
  endfunction

  function logic [HRESP_W-1:0] resp_error();
    if (HRESP_W == 1) return hresp_t'(1'b1);
    return hresp_t'(2'b01);
  endfunction

  function logic [HRESP_W-1:0] resp_signal(ahb_resp_e r);
    if (HRESP_W == 1) return hresp_t'((r == AHB_RESP_OKAY) ? 1'b0 : 1'b1);
    case (r)
      AHB_RESP_RETRY: return hresp_t'(2'b10);
      AHB_RESP_SPLIT: return hresp_t'(2'b11);
      AHB_RESP_ERROR: return hresp_t'(2'b01);
      default:        return hresp_t'(2'b00);
    endcase
  endfunction

  function ahb_resp_e choose_response(
    logic [ADDR_W-1:0] addr,
    bit                nonsec,
    logic [3:0]        prot,
    bit                write
  );
    int unsigned r;
    if (!cfg.access_allowed(addr, nonsec, prot, write)) return AHB_RESP_ERROR;
    if (cfg.force_resp_enable) begin
      if ((cfg.mode == AHB_MODE_LITE) && (cfg.force_resp inside {AHB_RESP_RETRY, AHB_RESP_SPLIT}))
        return AHB_RESP_ERROR;
      return cfg.force_resp;
    end
    if (cfg.addr_in_error_range(addr)) return AHB_RESP_ERROR;
    if (cfg.mode == AHB_MODE_FULL && cfg.allow_retry_split) begin
      r = $urandom_range(0, 99);
      if (r < cfg.split_pct) return AHB_RESP_SPLIT;
      if (r < (cfg.split_pct + cfg.retry_pct)) return AHB_RESP_RETRY;
    end
    return AHB_RESP_OKAY;
  endfunction

  function ctrl_t sample_ctrl();
    ctrl_t c;
    c.valid = ((`AHB_S_CB.HSEL === 1'b1) && (`AHB_S_CB.HTRANS[1] === 1'b1) && (`AHB_S_CB.HREADY === 1'b1));
    c.write = `AHB_S_CB.HWRITE;
    c.addr  = `AHB_S_CB.HADDR;
    c.size  = ahb_size_e'(`AHB_S_CB.HSIZE);
    c.burst = ahb_burst_e'(`AHB_S_CB.HBURST);
    c.prot  = `AHB_S_CB.HPROT;
    c.nonsec = `AHB_S_CB.HNONSEC;
    c.lock  = `AHB_S_CB.HMASTLOCK;
    c.resp_kind = choose_response(c.addr, c.nonsec, c.prot, c.write);
    return c;
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);

    if (!uvm_config_db#(ahb_cfg#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK))::get(this, "", "cfg", cfg)) begin
      `uvm_fatal(RID, "Missing cfg in config DB (key: cfg)")
    end
    vif = cfg.vif;
`ifndef VERILATOR
    if (vif == null) `uvm_fatal(RID, "cfg.vif is null")
`endif

    // Defaults
    ctrl_pipe = clear_ctrl();
    ctrl_data = clear_ctrl();
    stall_rem = 0;
    resp_pending = 0;

    vif.HREADYOUT <= 1'b1;
    vif.HRESP     <= resp_okay();
    vif.HRDATA    <= '0;

    @(posedge vif.HCLK);
    while (!vif.HRESETn) begin
      @(posedge vif.HCLK);
      vif.HREADYOUT <= 1'b1;
      vif.HRESP     <= resp_okay();
      vif.HRDATA    <= '0;
      ctrl_pipe = clear_ctrl();
      ctrl_data = clear_ctrl();
      stall_rem = 0;
      resp_pending = 0;
    end

    forever begin
      @(`AHB_S_EVT);

      if (!vif.HRESETn) begin
        ctrl_pipe = clear_ctrl();
        ctrl_data = clear_ctrl();
        stall_rem = 0;
        resp_pending = 0;
        vif.HREADYOUT <= 1'b1;
        vif.HRESP     <= resp_okay();
        vif.HRDATA    <= '0;
        continue;
      end

      if (ctrl_data.valid && resp_pending) begin
        // AHB two-cycle non-OKAY response (cycle 2), then shift below.
        vif.HREADYOUT <= 1'b1;
        vif.HRESP     <= resp_signal(ctrl_data.resp_kind);
        resp_pending = 0;
      end else if (ctrl_data.valid && (stall_rem != 0)) begin
        // Stall cycle: keep response/data stable and re-open HREADYOUT for the
        // cycle in which the stalled data phase will complete.
        if (stall_rem > 1) begin
          stall_rem--;
          vif.HREADYOUT <= 1'b0;
        end else begin
          stall_rem = 0;
          vif.HREADYOUT <= 1'b1;
        end
        continue;
      end else if (ctrl_data.valid) begin
        if (ctrl_data.resp_kind != AHB_RESP_OKAY) begin
          // AHB two-cycle non-OKAY response (cycle 1).
          vif.HREADYOUT <= 1'b0;
          vif.HRESP     <= resp_signal(ctrl_data.resp_kind);
          vif.HRDATA    <= '0;
          resp_pending = 1'b1;
          continue;
        end else if (ctrl_data.write) begin
          write_bytes(ctrl_data.addr, ctrl_data.size, `AHB_S_CB.HWDATA);
        end
      end

      // Shift pipeline at end of ready cycle:
      // - ctrl_pipe captures newly accepted control.
      // - ctrl_data becomes previous ctrl_pipe.
      ctrl_data = ctrl_pipe;
      ctrl_pipe = sample_ctrl();

      if (ctrl_data.valid && cfg.allow_wait_states) begin
        stall_rem = (cfg.max_wait >= cfg.min_wait) ? $urandom_range(cfg.min_wait, cfg.max_wait) : cfg.min_wait;
      end else begin
        stall_rem = 0;
      end

      if (ctrl_data.valid) begin
        vif.HRESP <= resp_signal(ctrl_data.resp_kind);
        if (!ctrl_data.write && (ctrl_data.resp_kind == AHB_RESP_OKAY)) begin
          vif.HRDATA <= read_bytes(ctrl_data.addr, ctrl_data.size);
        end else begin
          vif.HRDATA <= '0;
        end
      end else begin
        vif.HRESP  <= resp_okay();
        vif.HRDATA <= '0;
      end

      vif.HREADYOUT <= (ctrl_data.valid && (stall_rem != 0)) ? 1'b0 : 1'b1;
    end
  endtask

endclass

`undef AHB_S_CB
`undef AHB_S_EVT

`endif // KVIPS_AHB_SLAVE_DRIVER_SVH
