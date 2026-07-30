//------------------------------------------------------------------------------
// AXI4 Slave Driver (Reactive, with optional memory model)
//------------------------------------------------------------------------------

`ifndef KVIPS_AXI4_SLAVE_DRIVER_SVH
`define KVIPS_AXI4_SLAVE_DRIVER_SVH

class axi4_slave_mem #(
  int ADDR_W = 32,
  int DATA_W = 64
) extends uvm_object;

  localparam int STRB_W = DATA_W/8;

  byte unsigned mem[];
  bit           valid[];
  int unsigned  mem_bytes;
  longint unsigned mem_base;
  bit             mem_wrap;

  function new(
    string name = "axi4_slave_mem",
    int unsigned bytes = 64*1024,
    longint unsigned base = 0,
    bit wrap = 1'b0
  );
    super.new(name);
    mem_bytes = bytes;
    mem_base  = base;
    mem_wrap  = wrap;
    mem = new[mem_bytes];
    valid = new[mem_bytes];
    foreach (mem[i]) mem[i] = 8'h00;
    foreach (valid[i]) valid[i] = 1'b0;
  endfunction

  function automatic bit map_addr(longint unsigned addr, output int unsigned idx);
    longint unsigned idx_l;
    if ((mem_bytes == 0) || (addr < mem_base)) return 1'b0;
    idx_l = addr - mem_base;
    if (mem_wrap) idx_l = idx_l % longint'(mem_bytes);
    if (idx_l >= longint'(mem_bytes)) return 1'b0;
    idx = int'(idx_l);
    return 1'b1;
  endfunction

  function void clear();
    foreach (mem[i]) mem[i] = 8'h00;
    foreach (valid[i]) valid[i] = 1'b0;
  endfunction

  function void backdoor_write_byte(longint unsigned addr, byte unsigned data);
    int unsigned idx;
    if (map_addr(addr, idx)) begin
      mem[idx] = data;
      valid[idx] = 1'b1;
    end
  endfunction

  function byte unsigned backdoor_read_byte(longint unsigned addr);
    int unsigned idx;
    if (map_addr(addr, idx)) return mem[idx];
    return '0;
  endfunction

  function void write_beat(logic [ADDR_W-1:0] addr, logic [DATA_W-1:0] data, logic [STRB_W-1:0] strb);
    longint unsigned base;
    longint unsigned stride;
    base = longint'(addr);
    stride = longint'(STRB_W);
    base = (base / stride) * stride; // align to data-bus word
    for (int unsigned b = 0; b < STRB_W; b++) begin
      if (strb[b]) begin
        longint unsigned a;
        int unsigned idx;
        a = base + longint'(b);
        if (map_addr(a, idx)) begin
          mem[idx] = data[8*b +: 8];
          valid[idx] = 1'b1;
        end
      end
    end
  endfunction

  function logic [DATA_W-1:0] read_beat(logic [ADDR_W-1:0] addr);
    bit ignored;
    return read_beat_policy(addr, AXI4_UNINIT_ZERO, 8'h00, ignored);
  endfunction

  function logic [DATA_W-1:0] read_beat_policy(
    logic [ADDR_W-1:0] addr,
    axi4_uninit_read_policy_e policy,
    logic [7:0] fill,
    output bit had_uninit
  );
    logic [DATA_W-1:0] data;
    longint unsigned base;
    longint unsigned stride;
    base = longint'(addr);
    stride = longint'(STRB_W);
    base = (base / stride) * stride; // align to data-bus word
    data = '0;
    had_uninit = 1'b0;
    for (int unsigned b = 0; b < STRB_W; b++) begin
      longint unsigned a;
      int unsigned idx;
      a = base + longint'(b);
      if (map_addr(a, idx) && valid[idx]) begin
        data[8*b +: 8] = mem[idx];
      end else begin
        had_uninit = 1'b1;
        case (policy)
          AXI4_UNINIT_FILL:   data[8*b +: 8] = fill;
          AXI4_UNINIT_RANDOM: data[8*b +: 8] = $urandom_range(255, 0);
          AXI4_UNINIT_X:      data[8*b +: 8] = 'x;
          default:             data[8*b +: 8] = '0;
        endcase
      end
    end
    return data;
  endfunction

  `uvm_object_param_utils(axi4_slave_mem#(ADDR_W, DATA_W))

endclass

class axi4_slave_driver #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends uvm_component;

  localparam int STRB_W = DATA_W/8;
  localparam string RID = "AXI4_SDRV";

`ifdef VERILATOR
  axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W) cfg;
  virtual axi4_if #(ADDR_W, DATA_W, ID_W, USER_W) vif;
`else
  typedef virtual axi4_if #(ADDR_W, DATA_W, ID_W, USER_W) axi4_vif_t;
  axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W) cfg;
  axi4_vif_t vif;
`endif
  axi4_slave_mem#(ADDR_W, DATA_W) mem;

  typedef struct packed {
    logic [ID_W-1:0]      id;
    logic [ADDR_W-1:0]    addr;
    logic [7:0]           len;
    logic [2:0]           size;
    axi4_burst_e          burst;
    logic                 lock;
    logic                 err;
    axi4_resp_e           err_resp;
    logic [USER_W-1:0]    user;
  } aw_t;

  typedef struct packed {
    logic [ID_W-1:0]      id;
    logic [ADDR_W-1:0]    addr;
    logic [7:0]           len;
    logic [2:0]           size;
    axi4_burst_e          burst;
    logic                 lock;
    axi4_resp_e           resp;
    logic [USER_W-1:0]    user;
  } ar_t;

  aw_t aw_q[$];
  ar_t ar_q[$];
  int unsigned outstanding_w;
  int unsigned outstanding_r;

  typedef struct {
    bit              valid;
    logic [ADDR_W-1:0] addr;
    logic [7:0]         len;
    logic [2:0]         size;
    axi4_burst_e        burst;
    longint unsigned    start_b;
    longint unsigned    end_b;
  } excl_res_t;

  excl_res_t excl_by_id[logic [ID_W-1:0]];

  `uvm_component_param_utils(axi4_slave_driver#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W))::get(this, "", "cfg", cfg)) begin
      `uvm_fatal(RID, "Missing cfg in config DB (key: cfg)")
    end
    vif = cfg.vif;
`ifndef VERILATOR
    if (vif == null) `uvm_fatal(RID, "cfg.vif is null")
`endif
    if (cfg.slave_mem_enable) mem = new("mem", cfg.slave_mem_bytes, cfg.slave_mem_base, cfg.slave_mem_wrap);
  endfunction

  task automatic drive_idle();
    vif.awready <= 1'b0;
    vif.wready  <= 1'b0;
    vif.bvalid  <= 1'b0;
    vif.bid     <= '0;
    vif.bresp   <= AXI4_RESP_OKAY;
    vif.buser   <= '0;
    vif.arready <= 1'b0;
    vif.rvalid  <= 1'b0;
    vif.rid     <= '0;
    vif.rdata   <= '0;
    vif.rresp   <= AXI4_RESP_OKAY;
    vif.rlast   <= 1'b0;
    vif.ruser   <= '0;
  endtask

  task automatic wait_reset_release();
    drive_idle();
    while (vif.areset_n !== 1'b1) @(posedge vif.aclk);
    @(posedge vif.aclk);
  endtask

  function automatic int unsigned rand_in_range(int unsigned lo, int unsigned hi);
    int unsigned v;
    if (hi <= lo) return lo;
`ifdef VERILATOR
    v = $urandom_range(hi, lo);
`else
    void'(std::randomize(v) with { v inside {[lo:hi]}; });
`endif
    return v;
  endfunction

  task automatic maybe_wait_cycles(int unsigned min_c, int unsigned max_c);
    int unsigned c = rand_in_range(min_c, max_c);
    repeat (c) @(posedge vif.aclk);
  endtask

  task automatic maybe_wait_channel_cycles(
    int unsigned channel_min,
    int unsigned channel_max,
    int unsigned fallback_min,
    int unsigned fallback_max
  );
    if ((channel_min != 0) || (channel_max != 0)) begin
      maybe_wait_cycles(channel_min, channel_max);
    end else begin
      maybe_wait_cycles(fallback_min, fallback_max);
    end
  endtask

  function automatic bit txn_outside_regions(
    logic [ADDR_W-1:0] addr,
    logic [7:0] len,
    logic [2:0] size,
    axi4_burst_e burst
  );
    if (!cfg.slave_region_decode_enable) return 1'b0;
    for (int unsigned i = 0; i <= int'(len); i++) begin
      longint unsigned beat_addr;
      int unsigned bytes_per_beat;
      beat_addr = axi4_beat_addr(longint'(addr), int'(size), int'(len), burst, i);
      bytes_per_beat = axi4_size_to_bytes(int'(size));
      for (int unsigned b = 0; b < bytes_per_beat; b++) begin
        bit mapped;
        mapped = 1'b0;
        for (int unsigned r = 0; r < cfg.slave_region_start.size(); r++) begin
          longint unsigned start_addr;
          longint unsigned end_addr;
          start_addr = longint'(cfg.slave_region_start[r]);
          end_addr = longint'(cfg.slave_region_end[r]);
          if (end_addr < start_addr) begin
            longint unsigned tmp;
            tmp = start_addr;
            start_addr = end_addr;
            end_addr = tmp;
          end
          if (((beat_addr + b) >= start_addr) && ((beat_addr + b) <= end_addr)) mapped = 1'b1;
        end
        if (!mapped) return 1'b1;
      end
    end
    return 1'b0;
  endfunction

  function automatic bit choose_rate_error(bit is_read, output axi4_resp_e resp);
    int unsigned roll;
    int unsigned decerr_rate;
    int unsigned slverr_rate;
    decerr_rate = is_read ? cfg.slave_rd_decerr_rate_pct : cfg.slave_wr_decerr_rate_pct;
    slverr_rate = is_read ? cfg.slave_rd_slverr_rate_pct : cfg.slave_wr_slverr_rate_pct;
    if (decerr_rate > 100) decerr_rate = 100;
    if (slverr_rate > (100 - decerr_rate)) slverr_rate = 100 - decerr_rate;
    roll = $urandom_range(99, 0);
    if (roll < decerr_rate) begin
      resp = AXI4_RESP_DECERR;
      return 1'b1;
    end
    if (roll < (decerr_rate + slverr_rate)) begin
      resp = AXI4_RESP_SLVERR;
      return 1'b1;
    end
    resp = AXI4_RESP_OKAY;
    return 1'b0;
  endfunction

  function automatic logic [DATA_W-1:0] read_mem_beat(logic [ADDR_W-1:0] addr);
    logic [DATA_W-1:0] data;
    bit had_uninit;
    data = mem.read_beat_policy(addr, cfg.slave_uninit_read_policy, cfg.slave_uninit_fill, had_uninit);
    if (had_uninit && cfg.slave_uninit_read_warn) begin
      `uvm_warning(RID, $sformatf("Read from unwritten slave memory at 0x%0h", addr))
    end
    return data;
  endfunction

  function void backdoor_write_byte(longint unsigned addr, byte unsigned data);
    if (mem == null) `uvm_fatal(RID, "backdoor_write_byte requires cfg.slave_mem_enable=1")
    mem.backdoor_write_byte(addr, data);
  endfunction

  function byte unsigned backdoor_read_byte(longint unsigned addr);
    if (mem == null) `uvm_fatal(RID, "backdoor_read_byte requires cfg.slave_mem_enable=1")
    return mem.backdoor_read_byte(addr);
  endfunction

  function automatic bit exclusive_req_legal(logic [ADDR_W-1:0] addr, logic [7:0] len, logic [2:0] size, axi4_burst_e burst);
    longint unsigned bytes_per_beat;
    longint unsigned total_bytes;
    bytes_per_beat = longint'(axi4_size_to_bytes(int'(size)));
    total_bytes    = longint'(axi4_total_bytes(int'(size), int'(len)));
    if (!cfg.slave_exclusive_enable) return 1'b0;
    if (burst != AXI4_BURST_INCR) return 1'b0;
    if (total_bytes == 0) return 1'b0;
    if (total_bytes > longint'(cfg.slave_exclusive_max_bytes)) return 1'b0;
    if ((longint'(addr) % bytes_per_beat) != 0) return 1'b0;
    if (axi4_crosses_4kb(longint'(addr), int'(size), int'(len))) return 1'b0;
    return 1'b1;
  endfunction

  function automatic bit txn_overlaps_err_range(logic [ADDR_W-1:0] addr, logic [7:0] len, logic [2:0] size, axi4_burst_e burst);
    longint unsigned beat_addr;
    longint unsigned cfg_start_b;
    longint unsigned cfg_end_b;
    longint unsigned bytes_per_beat;
    if (!cfg.slave_err_enable) return 1'b0;
    bytes_per_beat = axi4_size_to_bytes(int'(size));
    cfg_start_b = longint'(cfg.slave_err_start);
    cfg_end_b   = longint'(cfg.slave_err_end);
    if (cfg_end_b < cfg_start_b) begin
      longint unsigned t;
      t = cfg_start_b;
      cfg_start_b = cfg_end_b;
      cfg_end_b   = t;
    end
    // A WRAP burst is not a contiguous range from AxADDR.  Check each byte of
    // each actual beat address so error injection matches the memory accesses
    // for INCR, FIXED, and WRAP transfers alike.
    for (int unsigned i = 0; i <= int'(len); i++) begin
      beat_addr = axi4_beat_addr(longint'(addr), int'(size), int'(len), burst, i);
      for (int unsigned b = 0; b < bytes_per_beat; b++) begin
        if (((beat_addr + b) >= cfg_start_b) && ((beat_addr + b) <= cfg_end_b)) return 1'b1;
      end
    end
    return 1'b0;
  endfunction

  function automatic void excl_set_reservation(logic [ID_W-1:0] id, logic [ADDR_W-1:0] addr, logic [7:0] len, logic [2:0] size, axi4_burst_e burst);
    excl_res_t res;
    longint unsigned total_bytes;
    total_bytes = axi4_total_bytes(int'(size), int'(len));
    res.valid  = 1'b1;
    res.addr   = addr;
    res.len    = len;
    res.size   = size;
    res.burst  = burst;
    res.start_b = longint'(addr);
    res.end_b   = longint'(addr) + total_bytes - 1;
    excl_by_id[id] = res;
  endfunction

  function automatic void excl_clear_reservation(logic [ID_W-1:0] id);
    if (excl_by_id.exists(id)) begin
      excl_by_id[id].valid = 1'b0;
    end
  endfunction

  function automatic bit excl_match_and_valid(logic [ID_W-1:0] id, logic [ADDR_W-1:0] addr, logic [7:0] len, logic [2:0] size, axi4_burst_e burst);
    if (!excl_by_id.exists(id)) return 1'b0;
    if (!excl_by_id[id].valid)  return 1'b0;
    if (excl_by_id[id].addr  != addr)  return 1'b0;
    if (excl_by_id[id].len   != len)   return 1'b0;
    if (excl_by_id[id].size  != size)  return 1'b0;
    if (excl_by_id[id].burst != burst) return 1'b0;
    return 1'b1;
  endfunction

  function automatic void excl_invalidate_overlapping(longint unsigned wr_start_b, longint unsigned wr_end_b);
    foreach (excl_by_id[id]) begin
      if (!excl_by_id[id].valid) continue;
      if ((wr_start_b <= excl_by_id[id].end_b) && (wr_end_b >= excl_by_id[id].start_b)) begin
        excl_by_id[id].valid = 1'b0;
      end
    end
  endfunction

  task run_phase(uvm_phase phase);
    forever begin
      drive_idle();
      while (vif.areset_n !== 1'b1) @(posedge vif.aclk);
      fork : slave_active
        aw_accept_loop();
        w_accept_loop();
        b_respond_loop();
        ar_accept_loop();
        r_respond_loop();
        begin
          @(negedge vif.areset_n);
        end
      join_any
      disable slave_active;
      aw_q.delete();
      ar_q.delete();
      b_q.delete();
      excl_by_id.delete();
      outstanding_w = 0;
      outstanding_r = 0;
      if (cfg.slave_clear_mem_on_reset && (mem != null)) mem.clear();
    end
  endtask

  task automatic aw_accept_loop();
    aw_t aw;
    wait_reset_release();
    forever begin
      while ((cfg.slave_max_outstanding_wr != 0) &&
             (outstanding_w >= cfg.slave_max_outstanding_wr)) @(posedge vif.aclk);
      maybe_wait_channel_cycles(cfg.slave_aw_ready_min, cfg.slave_aw_ready_max, cfg.ready_min, cfg.ready_max);
      @(negedge vif.aclk);
      vif.awready <= 1'b1;
      if (cfg.slave_aw_random_ready) begin
        forever begin
          @(posedge vif.aclk);
          if (vif.awvalid && vif.awready) break;
          @(negedge vif.aclk);
          vif.awready <= 1'b0;
          maybe_wait_channel_cycles(cfg.slave_aw_ready_min, cfg.slave_aw_ready_max, cfg.ready_min, cfg.ready_max);
          @(negedge vif.aclk);
          vif.awready <= 1'b1;
        end
      end else begin
        do @(posedge vif.aclk); while (!(vif.awvalid && vif.awready));
      end
      aw.id    = vif.awid;
      aw.addr  = vif.awaddr;
      aw.len   = vif.awlen;
      aw.size  = vif.awsize;
      aw.burst = axi4_burst_e'(vif.awburst);
      aw.lock  = vif.awlock;
      aw.err_resp = cfg.slave_err_resp;
      aw.err = 1'b0;
      if (txn_outside_regions(aw.addr, aw.len, aw.size, aw.burst)) begin
        aw.err = 1'b1;
        aw.err_resp = AXI4_RESP_DECERR;
      end else if (cfg.slave_err_on_write && txn_overlaps_err_range(aw.addr, aw.len, aw.size, aw.burst)) begin
        aw.err = 1'b1;
      end else if (choose_rate_error(1'b0, aw.err_resp)) begin
        aw.err = 1'b1;
      end
      aw.user  = vif.awuser;
      aw_q.push_back(aw);
      outstanding_w++;
      if (cfg.trace_enable) `uvm_info(RID, $sformatf("AW accepted id=0x%0h addr=0x%0h len=%0d", aw.id, aw.addr, aw.len), UVM_MEDIUM)
      @(negedge vif.aclk);
      vif.awready <= 1'b0;
    end
  endtask

  task automatic w_accept_loop();
    aw_t cur_aw;
    bit  have_aw = 0;
    int unsigned beat_idx = 0;
    logic [ADDR_W-1:0] beat_addr;
    logic [DATA_W-1:0] buf_data[];
    logic [STRB_W-1:0] buf_strb[];
    bit                is_excl;
    bit                excl_legal;
    bit                is_err;
    wait_reset_release();
    forever begin
      if (!have_aw) begin
        if (aw_q.size() == 0) begin
          @(posedge vif.aclk);
          continue;
        end
        cur_aw = aw_q.pop_front();
        have_aw = 1;
        beat_idx = 0;
        is_excl = (cur_aw.lock && cfg.slave_exclusive_enable);
        excl_legal = is_excl ? exclusive_req_legal(cur_aw.addr, cur_aw.len, cur_aw.size, cur_aw.burst) : 1'b0;
        is_err = cur_aw.err;
        if (is_excl || is_err) begin
          int unsigned beats;
          beats = int'(cur_aw.len) + 1;
          buf_data = new[beats];
          buf_strb = new[beats];
        end else begin
          buf_data = new[0];
          buf_strb = new[0];
        end
      end

      maybe_wait_channel_cycles(cfg.slave_w_ready_min, cfg.slave_w_ready_max, cfg.ready_min, cfg.ready_max);
      @(negedge vif.aclk);
      vif.wready <= 1'b1;
      if (cfg.slave_w_random_ready) begin
        forever begin
          @(posedge vif.aclk);
          if (vif.wvalid && vif.wready) break;
          @(negedge vif.aclk);
          vif.wready <= 1'b0;
          maybe_wait_channel_cycles(cfg.slave_w_ready_min, cfg.slave_w_ready_max, cfg.ready_min, cfg.ready_max);
          @(negedge vif.aclk);
          vif.wready <= 1'b1;
        end
      end else begin
        do @(posedge vif.aclk); while (!(vif.wvalid && vif.wready));
      end
      if (is_excl || is_err) begin
        if (beat_idx < buf_data.size()) begin
          buf_data[beat_idx] = vif.wdata;
          buf_strb[beat_idx] = vif.wstrb;
        end
      end else if (cfg.slave_mem_enable) begin
        longint unsigned a;
        a = axi4_beat_addr(longint'(cur_aw.addr), int'(cur_aw.size), int'(cur_aw.len), cur_aw.burst, beat_idx);
        beat_addr = a[ADDR_W-1:0];
        mem.write_beat(beat_addr, vif.wdata, vif.wstrb);
      end
      beat_idx++;
      if (vif.wlast) begin
        longint unsigned wr_start_b;
        longint unsigned wr_end_b;
        longint unsigned total_bytes;
        bit excl_success;
        axi4_resp_e bresp;

        total_bytes = axi4_total_bytes(int'(cur_aw.size), int'(cur_aw.len));
        wr_start_b  = longint'(cur_aw.addr);
        wr_end_b    = (total_bytes == 0) ? wr_start_b : (wr_start_b + total_bytes - 1);

        excl_success = 1'b0;
        bresp        = AXI4_RESP_OKAY;
        if (is_err) begin
          bresp = cur_aw.err_resp;
        end else if (is_excl && excl_legal) begin
          excl_success = excl_match_and_valid(cur_aw.id, cur_aw.addr, cur_aw.len, cur_aw.size, cur_aw.burst);
          bresp        = excl_success ? AXI4_RESP_EXOKAY : AXI4_RESP_OKAY;
        end

        // Any write invalidates any outstanding exclusive reservations to overlapping addresses.
        excl_invalidate_overlapping(wr_start_b, wr_end_b);
        // Clear this ID's reservation after an exclusive write attempt.
        if (is_excl) excl_clear_reservation(cur_aw.id);

        // Exclusive write updates memory only if the exclusive access succeeded.
        if (cfg.slave_mem_enable) begin
          if (!is_err) begin
            if (is_excl) begin
              if (excl_success) begin
                for (int unsigned i = 0; i < buf_data.size(); i++) begin
                  longint unsigned a;
                  a = axi4_beat_addr(longint'(cur_aw.addr), int'(cur_aw.size), int'(cur_aw.len), cur_aw.burst, i);
                  beat_addr = a[ADDR_W-1:0];
                  mem.write_beat(beat_addr, buf_data[i], buf_strb[i]);
                end
              end
            end else begin
              // Non-exclusive writes are written beat-by-beat (already committed).
            end
          end
        end

        have_aw = 0;
        beat_idx = 0;
        b_push(cur_aw.id, bresp, cur_aw.user);
      end
      @(negedge vif.aclk);
      vif.wready <= 1'b0;
    end
  endtask

  typedef struct packed {
    logic [ID_W-1:0]   id;
    axi4_resp_e        resp;
    logic [USER_W-1:0] user;
  } b_t;

  b_t b_q[$];

  // AXI4 permits response reordering between IDs, but preserves issue order
  // for transactions that share an ID.  Return a random queue entry that is
  // the oldest pending response for its ID.
  function automatic int find_b_eligible_idx();
    int eligible[$];
    foreach (b_q[i]) begin
      bit older_same_id;
      older_same_id = 1'b0;
      for (int j = 0; j < i; j++) begin
        if (b_q[j].id == b_q[i].id) older_same_id = 1'b1;
      end
      if (!older_same_id) eligible.push_back(i);
    end
    if (eligible.size() == 0) return -1;
    return eligible[$urandom_range(0, eligible.size()-1)];
  endfunction

  function void b_push(logic [ID_W-1:0] id, axi4_resp_e resp, logic [USER_W-1:0] user);
    b_t b;
    b.id   = id;
    b.resp = resp;
    b.user = user;
    b_q.push_back(b);
  endfunction

  function automatic int find_r_eligible_idx();
    int eligible[$];
    foreach (ar_q[i]) begin
      bit older_same_id;
      older_same_id = 1'b0;
      for (int j = 0; j < i; j++) begin
        if (ar_q[j].id == ar_q[i].id) older_same_id = 1'b1;
      end
      if (!older_same_id) eligible.push_back(i);
    end
    if (eligible.size() == 0) return -1;
    return eligible[$urandom_range(0, eligible.size()-1)];
  endfunction

  task automatic maybe_wait_r_beat(int unsigned beat_idx);
    if (beat_idx < cfg.slave_r_beat_delays.size()) begin
      repeat (cfg.slave_r_beat_delays[beat_idx]) @(posedge vif.aclk);
    end else if (beat_idx == 0) begin
      maybe_wait_channel_cycles(cfg.slave_r_resp_min, cfg.slave_r_resp_max, cfg.resp_min, cfg.resp_max);
    end
  endtask

  task automatic b_respond_loop();
    b_t b;
    int unsigned cycles;
    wait_reset_release();
    forever begin
      if (b_q.size() == 0) begin
        @(posedge vif.aclk);
        continue;
      end
      if (cfg.slave_reorder_b && (cfg.slave_b_accum_cycles != 0)) begin
        repeat (cfg.slave_b_accum_cycles) @(posedge vif.aclk);
      end
      maybe_wait_channel_cycles(cfg.slave_b_resp_min, cfg.slave_b_resp_max, cfg.resp_min, cfg.resp_max);
      if (cfg.slave_reorder_b && (b_q.size() > 1)) begin
        int idx;
        idx = find_b_eligible_idx();
        if (idx < 0) begin
          @(posedge vif.aclk);
          continue;
        end
        b = b_q[idx];
        b_q.delete(idx);
      end else begin
        b = b_q.pop_front();
      end
      @(negedge vif.aclk);
      vif.bid    <= b.id;
      vif.bresp  <= b.resp;
      vif.buser  <= b.user;
      vif.bvalid <= 1'b1;

      cycles = 0;
      while (1) begin
        @(posedge vif.aclk);
        if (vif.bvalid && vif.bready) break;
        cycles++;
        if ((cfg.handshake_timeout_cycles != 0) && (cycles > cfg.handshake_timeout_cycles)) begin
          `uvm_fatal(RID, "Timeout waiting for BREADY")
        end
      end
      @(negedge vif.aclk);
      vif.bvalid <= 1'b0;
      if (outstanding_w != 0) outstanding_w--;
    end
  endtask

  task automatic ar_accept_loop();
    ar_t ar;
    wait_reset_release();
    forever begin
      while ((cfg.slave_max_outstanding_rd != 0) &&
             (outstanding_r >= cfg.slave_max_outstanding_rd)) @(posedge vif.aclk);
      maybe_wait_channel_cycles(cfg.slave_ar_ready_min, cfg.slave_ar_ready_max, cfg.ready_min, cfg.ready_max);
      @(negedge vif.aclk);
      vif.arready <= 1'b1;
      if (cfg.slave_ar_random_ready) begin
        forever begin
          @(posedge vif.aclk);
          if (vif.arvalid && vif.arready) break;
          @(negedge vif.aclk);
          vif.arready <= 1'b0;
          maybe_wait_channel_cycles(cfg.slave_ar_ready_min, cfg.slave_ar_ready_max, cfg.ready_min, cfg.ready_max);
          @(negedge vif.aclk);
          vif.arready <= 1'b1;
        end
      end else begin
        do @(posedge vif.aclk); while (!(vif.arvalid && vif.arready));
      end
      ar.id    = vif.arid;
      ar.addr  = vif.araddr;
      ar.len   = vif.arlen;
      ar.size  = vif.arsize;
      ar.burst = axi4_burst_e'(vif.arburst);
      ar.lock  = vif.arlock;
      ar.user  = vif.aruser;
      ar.resp  = AXI4_RESP_OKAY;
      if (txn_outside_regions(ar.addr, ar.len, ar.size, ar.burst)) begin
        ar.resp = AXI4_RESP_DECERR;
        excl_clear_reservation(ar.id);
      end else if (cfg.slave_err_on_read && txn_overlaps_err_range(ar.addr, ar.len, ar.size, ar.burst)) begin
        ar.resp = cfg.slave_err_resp;
        excl_clear_reservation(ar.id);
      end else if (choose_rate_error(1'b1, ar.resp)) begin
        excl_clear_reservation(ar.id);
      end else if (ar.lock && cfg.slave_exclusive_enable) begin
        if (exclusive_req_legal(ar.addr, ar.len, ar.size, ar.burst)) begin
          ar.resp = AXI4_RESP_EXOKAY;
          excl_set_reservation(ar.id, ar.addr, ar.len, ar.size, ar.burst);
        end else begin
          ar.resp = AXI4_RESP_OKAY;
          excl_clear_reservation(ar.id);
        end
      end
      ar_q.push_back(ar);
      outstanding_r++;
      if (cfg.trace_enable) `uvm_info(RID, $sformatf("AR accepted id=0x%0h addr=0x%0h len=%0d", ar.id, ar.addr, ar.len), UVM_MEDIUM)
      @(negedge vif.aclk);
      vif.arready <= 1'b0;
    end
  endtask

  task automatic r_respond_loop_inorder();
    ar_t ar;
    int unsigned beats;
    logic [ADDR_W-1:0] beat_addr;
    int unsigned cycles;
    int idx;
    wait_reset_release();
    forever begin
      if (ar_q.size() == 0) begin
        @(posedge vif.aclk);
        continue;
      end
      if (cfg.slave_reorder_r && (cfg.slave_r_accum_cycles != 0)) begin
        repeat (cfg.slave_r_accum_cycles) @(posedge vif.aclk);
      end
      if (cfg.slave_reorder_r && (ar_q.size() > 1)) begin
        idx = find_r_eligible_idx();
        if (idx < 0) begin
          @(posedge vif.aclk);
          continue;
        end
        ar = ar_q[idx];
        ar_q.delete(idx);
      end else begin
        ar = ar_q.pop_front();
      end
      beats = int'(ar.len) + 1;
      for (int unsigned i = 0; i < beats; i++) begin
        longint unsigned a;
        maybe_wait_r_beat(i);
        a = axi4_beat_addr(longint'(ar.addr), int'(ar.size), int'(ar.len), ar.burst, i);
        beat_addr = a[ADDR_W-1:0];
        @(negedge vif.aclk);
        vif.rid    <= ar.id;
        vif.rdata  <= ((ar.resp == AXI4_RESP_SLVERR) || (ar.resp == AXI4_RESP_DECERR)) ? '0
                       : (cfg.slave_mem_enable ? read_mem_beat(beat_addr) : '0);
        vif.rresp  <= ar.resp;
        vif.rlast  <= (i == (beats-1));
        vif.ruser  <= ar.user;
        vif.rvalid <= 1'b1;

        cycles = 0;
        while (1) begin
          @(posedge vif.aclk);
          if (vif.rvalid && vif.rready) break;
          cycles++;
          if ((cfg.handshake_timeout_cycles != 0) && (cycles > cfg.handshake_timeout_cycles)) begin
            `uvm_fatal(RID, "Timeout waiting for RREADY")
          end
        end
        @(negedge vif.aclk);
        vif.rvalid <= 1'b0;
      end
      if (outstanding_r != 0) outstanding_r--;
    end
  endtask

  task automatic r_respond_loop_interleave();
    // Interleave beats across IDs while maintaining per-ID ordering.
    typedef struct {
      ar_t          ar;
      int unsigned  beat_idx;
      int unsigned  beats;
    } rd_state_t;

    ar_t rd_by_id[logic [ID_W-1:0]][$];
    rd_state_t active[logic [ID_W-1:0]];

    wait_reset_release();
    forever begin
      // Move any newly accepted ARs into per-ID queues.
      while (ar_q.size() != 0) begin
        ar_t tmp;
        tmp = ar_q.pop_front();
        rd_by_id[tmp.id].push_back(tmp);
      end

      // Activate one pending burst per ID.
      foreach (rd_by_id[id]) begin
        if ((!active.exists(id)) && (rd_by_id[id].size() != 0)) begin
          rd_state_t st;
          st.ar = rd_by_id[id].pop_front();
          st.beat_idx = 0;
          st.beats = int'(st.ar.len) + 1;
          active[id] = st;
        end
      end

      if (active.num() == 0) begin
        @(posedge vif.aclk);
        continue;
      end

      if (cfg.slave_r_accum_cycles != 0) begin
        repeat (cfg.slave_r_accum_cycles) @(posedge vif.aclk);
      end

      begin
        logic [ID_W-1:0] ids[$];
        logic [ID_W-1:0] pick_id;
        rd_state_t st;
        logic [ADDR_W-1:0] beat_addr;
        int unsigned cycles;
        longint unsigned a;

        foreach (active[id]) ids.push_back(id);
        pick_id = ids[$urandom_range(0, ids.size()-1)];
        st = active[pick_id];

        maybe_wait_r_beat(st.beat_idx);
        a = axi4_beat_addr(longint'(st.ar.addr), int'(st.ar.size), int'(st.ar.len), st.ar.burst, st.beat_idx);
        beat_addr = a[ADDR_W-1:0];

        @(negedge vif.aclk);
        vif.rid    <= st.ar.id;
        vif.rdata  <= ((st.ar.resp == AXI4_RESP_SLVERR) || (st.ar.resp == AXI4_RESP_DECERR)) ? '0
                       : (cfg.slave_mem_enable ? read_mem_beat(beat_addr) : '0);
        vif.rresp  <= st.ar.resp;
        vif.rlast  <= (st.beat_idx == (st.beats-1));
        vif.ruser  <= st.ar.user;
        vif.rvalid <= 1'b1;

        cycles = 0;
        while (1) begin
          @(posedge vif.aclk);
          if (vif.rvalid && vif.rready) break;
          cycles++;
          if ((cfg.handshake_timeout_cycles != 0) && (cycles > cfg.handshake_timeout_cycles)) begin
            `uvm_fatal(RID, "Timeout waiting for RREADY")
          end
        end
        @(negedge vif.aclk);
        vif.rvalid <= 1'b0;

        st.beat_idx++;
        if (st.beat_idx >= st.beats) begin
          void'(active.delete(pick_id));
          if (outstanding_r != 0) outstanding_r--;
        end else begin
          active[pick_id] = st;
        end
      end
    end
  endtask

  task automatic r_respond_loop();
    if (cfg.slave_interleave_r) r_respond_loop_interleave();
    else                       r_respond_loop_inorder();
  endtask

endclass

`endif // KVIPS_AXI4_SLAVE_DRIVER_SVH
