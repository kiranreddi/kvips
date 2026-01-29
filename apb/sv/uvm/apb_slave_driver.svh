//------------------------------------------------------------------------------
// APB Slave Driver (Responder + optional memory model)
//------------------------------------------------------------------------------
`ifndef KVIPS_APB_SLAVE_DRIVER_SVH
`define KVIPS_APB_SLAVE_DRIVER_SVH

class apb_slave_driver #(
  int ADDR_W = 32,
  int DATA_W = 32,
  int NSEL   = 1
) extends uvm_component;

  localparam int STRB_W = (DATA_W/8);
  localparam string RID = "APB_SDRV";

  typedef virtual apb_if #(ADDR_W, DATA_W, NSEL) apb_vif_t;

  apb_cfg#(ADDR_W, DATA_W, NSEL) cfg;
  apb_vif_t vif;

  // Simple word-addressed backing store.
  logic [DATA_W-1:0] mem[longint unsigned];

  typedef struct packed {
    logic [ADDR_W-1:0] addr;
    bit                write;
    logic [DATA_W-1:0] wdata;
    logic [STRB_W-1:0] strb;
    logic [2:0]        prot;
  } req_t;

  req_t pending;
  bit   have_pending;
  int unsigned wait_left;

  `uvm_component_param_utils(apb_slave_driver#(ADDR_W, DATA_W, NSEL))

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

  function automatic longint unsigned word_idx(logic [ADDR_W-1:0] addr);
    return longint'(addr) / STRB_W;
  endfunction

  function automatic logic [DATA_W-1:0] apply_strb(
    logic [DATA_W-1:0] old_d,
    logic [DATA_W-1:0] new_d,
    logic [STRB_W-1:0] strb
  );
    logic [DATA_W-1:0] out;
    out = old_d;
    for (int unsigned b = 0; b < STRB_W; b++) begin
      if (strb[b]) out[8*b +: 8] = new_d[8*b +: 8];
    end
    return out;
  endfunction

  function automatic bit addr_in_err_range(logic [ADDR_W-1:0] a);
    if (!cfg.slverr_enable) return 0;
    if (a < cfg.slverr_start) return 0;
    if (a > cfg.slverr_end)   return 0;
    return 1;
  endfunction

  function automatic bit should_slverr(logic [ADDR_W-1:0] a);
    int unsigned roll;
    if (!addr_in_err_range(a)) return 0;
    if (cfg.slverr_pct == 0) return 0;
    if (cfg.slverr_pct >= 100) return 1;
    roll = $urandom_range(0, 99);
    return (roll < cfg.slverr_pct);
  endfunction

  task automatic drive_idle();
    vif.cb_s.PREADY  <= 1'b1;
    vif.cb_s.PSLVERR <= 1'b0;
    vif.cb_s.PRDATA  <= '0;
  endtask

  task automatic wait_reset_release();
    drive_idle();
    have_pending = 0;
    wait_left = 0;
    while (vif.PRESETn !== 1'b1) @(vif.cb_s);
    @(vif.cb_s);
  endtask

  task automatic capture_setup();
    pending.addr  = vif.cb_s.PADDR;
    pending.write = (vif.cb_s.PWRITE === 1'b1);
    pending.wdata = vif.cb_s.PWDATA;
    pending.prot  = vif.cb_s.PPROT;
    pending.strb  = cfg.is_apb4() ? vif.cb_s.PSTRB : '1;
    have_pending = 1;

    if (cfg.allow_wait_states && (cfg.max_wait_cycles != 0)) begin
      wait_left = cfg.min_wait_cycles;
      if (cfg.max_wait_cycles > cfg.min_wait_cycles) begin
        wait_left = $urandom_range(cfg.min_wait_cycles, cfg.max_wait_cycles);
      end
    end else begin
      wait_left = 0;
    end
  endtask

  task automatic respond_access();
    bit slv_err;
    longint unsigned wi;
    logic [DATA_W-1:0] old_d;
    logic [DATA_W-1:0] new_d;

    slv_err = should_slverr(pending.addr);
    vif.cb_s.PSLVERR <= slv_err;

    wi = word_idx(pending.addr);
    old_d = mem.exists(wi) ? mem[wi] : '0;

    if (pending.write) begin
      if (!slv_err) begin
        if (cfg.is_apb4()) new_d = apply_strb(old_d, pending.wdata, pending.strb);
        else               new_d = pending.wdata;
        mem[wi] = new_d;
      end
      vif.cb_s.PRDATA <= '0;
    end else begin
      vif.cb_s.PRDATA <= old_d;
    end
  endtask

  task run_phase(uvm_phase phase);
    wait_reset_release();

    forever begin
      bit done;
      @(vif.cb_s);
      done = 0;

      if (vif.PRESETn !== 1'b1) begin
        drive_idle();
        have_pending = 0;
        wait_left = 0;
        continue;
      end

      // Setup observed
      if ((|vif.cb_s.PSEL) && (vif.cb_s.PENABLE === 1'b0)) begin
        capture_setup();
        done = (wait_left == 0);
        vif.cb_s.PREADY  <= done;
        vif.cb_s.PSLVERR <= 1'b0;
        if (done) respond_access();
        continue;
      end

      // Access phase
      if ((|vif.cb_s.PSEL) && (vif.cb_s.PENABLE === 1'b1)) begin
        if (!have_pending) begin
          // Defensive: recover by treating current cycle as pending.
          capture_setup();
        end

        if (wait_left != 0) begin
          wait_left--;
          done = (wait_left == 0);
          vif.cb_s.PREADY <= done;
          if (done) respond_access();
        end else begin
          done = 1;
          vif.cb_s.PREADY <= 1'b1;
          respond_access();
        end

        // Transfer completes when PREADY is high in access phase.
        if (done) begin
          have_pending = 0;
          vif.cb_s.PSLVERR <= 1'b0;
        end
      end else begin
        // Idle: keep ready high, error low.
        vif.cb_s.PREADY  <= 1'b1;
        vif.cb_s.PSLVERR <= 1'b0;
      end
    end
  endtask

endclass

`endif // KVIPS_APB_SLAVE_DRIVER_SVH
