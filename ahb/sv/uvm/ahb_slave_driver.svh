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

  typedef virtual ahb_if #(
    .ADDR_W(ADDR_W),
    .DATA_W(DATA_W),
    .HAS_HMASTLOCK(HAS_HMASTLOCK),
    .HRESP_W(HRESP_W)
  ) ahb_vif_t;

  ahb_cfg#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK) cfg;
  ahb_vif_t                         vif;

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
    bit                lock;
  } ctrl_t;

  ctrl_t ctrl_pipe;   // accepted in the previous ready cycle (becomes data phase)
  ctrl_t ctrl_data;   // currently in data phase (when valid)

  int unsigned stall_rem; // remaining wait-state cycles for current data beat
  bit          stall_armed; // selects stall_rem once per data beat

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
    c.lock  = 1'b0;
    return c;
  endfunction

  function int unsigned size_bytes(ahb_size_e size);
    return (1 << size);
  endfunction

  function void write_bytes(logic [ADDR_W-1:0] addr, ahb_size_e size, logic [DATA_W-1:0] wdata);
    int unsigned sb = size_bytes(size);
    int unsigned lane = int'(addr) % data_bus_bytes();
    for (int unsigned i = 0; i < sb; i++) begin
      int unsigned byte_lane = lane + i;
      if (byte_lane < data_bus_bytes()) begin
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
      int unsigned byte_lane = lane + i;
      if (byte_lane < data_bus_bytes()) begin
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

  function ctrl_t sample_ctrl();
    ctrl_t c;
    c.valid = ((`AHB_S_CB.HSEL === 1'b1) && (`AHB_S_CB.HTRANS[1] === 1'b1) && (`AHB_S_CB.HREADY === 1'b1));
    c.write = `AHB_S_CB.HWRITE;
    c.addr  = `AHB_S_CB.HADDR;
    c.size  = ahb_size_e'(`AHB_S_CB.HSIZE);
    c.burst = ahb_burst_e'(`AHB_S_CB.HBURST);
    c.prot  = `AHB_S_CB.HPROT;
    c.lock  = `AHB_S_CB.HMASTLOCK;
    return c;
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);

    if (!uvm_config_db#(ahb_cfg#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK))::get(this, "", "cfg", cfg)) begin
      `uvm_fatal(RID, "Missing cfg in config DB (key: cfg)")
    end
    vif = cfg.vif;
    if (vif == null) `uvm_fatal(RID, "cfg.vif is null")

    // Defaults
    ctrl_pipe = clear_ctrl();
    ctrl_data = clear_ctrl();
    stall_rem = 0;
    stall_armed = 0;

    `AHB_S_CB.HREADYOUT <= 1'b1;
    `AHB_S_CB.HRESP     <= resp_okay();
    `AHB_S_CB.HRDATA    <= '0;

    @(posedge vif.HCLK);
    while (!vif.HRESETn) begin
      @(posedge vif.HCLK);
      `AHB_S_CB.HREADYOUT <= 1'b1;
      `AHB_S_CB.HRESP     <= resp_okay();
      `AHB_S_CB.HRDATA    <= '0;
      ctrl_pipe = clear_ctrl();
      ctrl_data = clear_ctrl();
      stall_rem = 0;
      stall_armed = 0;
    end

    forever begin
      @(`AHB_S_EVT);

      if (!vif.HRESETn) begin
        ctrl_pipe = clear_ctrl();
        ctrl_data = clear_ctrl();
        stall_rem = 0;
        stall_armed = 0;
        `AHB_S_CB.HREADYOUT <= 1'b1;
        `AHB_S_CB.HRESP     <= resp_okay();
        `AHB_S_CB.HRDATA    <= '0;
        continue;
      end

      // Manage wait-state insertion for the current data-phase beat.
      if (ctrl_data.valid && cfg.allow_wait_states && !stall_armed) begin
        stall_rem = (cfg.max_wait >= cfg.min_wait) ? $urandom_range(cfg.min_wait, cfg.max_wait) : cfg.min_wait;
        stall_armed = 1'b1;
      end

      if (ctrl_data.valid && (stall_rem != 0)) begin
        // Stall cycle: keep outputs stable, hold HREADYOUT low, decrement.
        `AHB_S_CB.HREADYOUT <= 1'b0;
        stall_rem--;
        continue;
      end

      // Ready to complete current beat (if any) and accept next control.
      `AHB_S_CB.HREADYOUT <= 1'b1;

      // Complete data phase for ctrl_data (this cycle's handshake completes it).
      if (ctrl_data.valid) begin
        bit err = cfg.addr_in_error_range(ctrl_data.addr);
        `AHB_S_CB.HRESP  <= err ? resp_error() : resp_okay();
        if (!ctrl_data.write) begin
          `AHB_S_CB.HRDATA <= read_bytes(ctrl_data.addr, ctrl_data.size);
        end else begin
          write_bytes(ctrl_data.addr, ctrl_data.size, `AHB_S_CB.HWDATA);
          `AHB_S_CB.HRDATA <= '0;
        end
      end else begin
        `AHB_S_CB.HRESP  <= resp_okay();
        `AHB_S_CB.HRDATA <= '0;
      end

      // Shift pipeline at end of ready cycle:
      // - ctrl_pipe captures newly accepted control.
      // - ctrl_data becomes previous ctrl_pipe.
      ctrl_data = ctrl_pipe;
      ctrl_pipe = sample_ctrl();

      if (!ctrl_data.valid) begin
        stall_rem = 0;
        stall_armed = 0;
      end else begin
        // New data beat started; choose wait-state policy fresh.
        stall_armed = 0;
      end
    end
  endtask

endclass

`undef AHB_S_CB
`undef AHB_S_EVT

`endif // KVIPS_AHB_SLAVE_DRIVER_SVH
