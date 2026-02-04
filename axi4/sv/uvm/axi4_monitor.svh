//------------------------------------------------------------------------------
// AXI4 Monitor
//------------------------------------------------------------------------------

`ifndef KVIPS_AXI4_MONITOR_SVH
`define KVIPS_AXI4_MONITOR_SVH

class axi4_monitor #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends uvm_component;

  localparam string RID = "AXI4_MON";
  localparam int unsigned STRB_W = (DATA_W/8);

`ifdef VERILATOR
  typedef axi4_if #(ADDR_W, DATA_W, ID_W, USER_W) axi4_vif_t;
`else
  typedef virtual axi4_if #(ADDR_W, DATA_W, ID_W, USER_W) axi4_vif_t;
`endif

  axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W) cfg;
`ifdef VERILATOR
  virtual axi4_vif_t vif;
`else
  axi4_vif_t vif;
`endif

`ifdef VERILATOR
`define AXI4_MON_CB  vif
`define AXI4_MON_EVT posedge vif.aclk
`else
`define AXI4_MON_CB  vif.mon_cb
`define AXI4_MON_EVT vif.mon_cb
`endif

  uvm_analysis_port #(axi4_item#(ADDR_W, DATA_W, ID_W, USER_W)) ap;

  // -------------------------
  // Optional performance statistics (lightweight)
  // -------------------------
  // Always-on summary counters (independent of cfg.stats_enable). These are used
  // for end-of-test reporting even when full stats are disabled.
  longint unsigned sum_aw_hs;
  longint unsigned sum_w_hs;
  longint unsigned sum_b_hs;
  longint unsigned sum_ar_hs;
  longint unsigned sum_r_hs;
  longint unsigned sum_r_last_hs;

  longint unsigned stat_cycles;
  longint unsigned stat_aw_hs;
  longint unsigned stat_w_hs;
  longint unsigned stat_b_hs;
  longint unsigned stat_ar_hs;
  longint unsigned stat_r_hs;
  longint unsigned stat_aw_stall;
  longint unsigned stat_w_stall;
  longint unsigned stat_b_stall;
  longint unsigned stat_ar_stall;
  longint unsigned stat_r_stall;
  int unsigned     stat_out_w;
  int unsigned     stat_out_r;
  int unsigned     stat_out_w_max;
  int unsigned     stat_out_r_max;

  // Latency (in cycles), keyed by ID; assumes per-ID in-order completion.
  longint unsigned wr_start_cycle[logic [ID_W-1:0]][$];
  longint unsigned rd_start_cycle[logic [ID_W-1:0]][$];
  longint unsigned wr_lat_min;
  longint unsigned wr_lat_max;
  longint unsigned wr_lat_sum;
  longint unsigned wr_lat_cnt;
  longint unsigned rd_lat_min;
  longint unsigned rd_lat_max;
  longint unsigned rd_lat_sum;
  longint unsigned rd_lat_cnt;

  typedef struct packed {
    logic [ID_W-1:0]     id;
    logic [ADDR_W-1:0]   addr;
    logic [7:0]          len;
    logic [2:0]          size;
    axi4_burst_e         burst;
    logic                lock;
    logic [3:0]          cache;
    logic [2:0]          prot;
    logic [3:0]          qos;
    logic [3:0]          region;
    logic [USER_W-1:0]   user;
  } a_chan_t;

  a_chan_t aw_q[$];

  typedef axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) item_t;

  // Write transactions waiting for B response, keyed by BID (to allow B reordering).
  item_t wr_wait_b[logic [ID_W-1:0]][$];

  typedef struct {
    item_t        tr;
    int unsigned  beat_idx;
    int unsigned  beats;
  } rd_state_t;

  // Read transactions waiting for R data, keyed by RID (to allow R interleaving across IDs).
  rd_state_t rd_q[logic [ID_W-1:0]][$];

  // -------------------------
  // Optional functional coverage (portable subset)
  // -------------------------
`ifndef VERILATOR
  covergroup cov with function sample(
    bit          is_write,
    axi4_burst_e burst,
    int unsigned size,
    int unsigned len,
    bit          lock,
    axi4_resp_e  resp,
    logic [3:0]  qos,
    logic [2:0]  prot,
    logic [3:0]  cache,
    logic [3:0]  region,
    int unsigned strb_pop,
    bit          narrow
  );
    option.per_instance = 1;
    cp_is_write: coverpoint is_write;
    cp_burst:    coverpoint burst {
      bins fixed = {AXI4_BURST_FIXED};
      bins incr  = {AXI4_BURST_INCR};
      bins wrap  = {AXI4_BURST_WRAP};
    }
    cp_size:     coverpoint size { bins sizes[] = {[0:$clog2(DATA_W/8)]}; }
    cp_len:      coverpoint len  {
      bins len_1    = {0};    // 1 beat (AxLEN is beats-1)
      bins len_2    = {1};
      bins len_4    = {3};
      bins len_8    = {7};
      bins len_16   = {15};
      bins len_256  = {255};
      bins other    = default;
    }
    cp_lock:     coverpoint lock;
    cp_resp:     coverpoint resp {
      bins okay   = {AXI4_RESP_OKAY};
      bins exokay = {AXI4_RESP_EXOKAY};
      bins slverr = {AXI4_RESP_SLVERR};
      bins decerr = {AXI4_RESP_DECERR};
    }
    cp_qos:      coverpoint qos {
      bins qos0   = {0};
      bins qos1_3 = {[1:3]};
      bins qos4_11 = {[4:11]};
      bins qos12_14 = {[12:14]};
      bins qos15  = {15};
    }
    cp_prot:     coverpoint prot { bins vals[] = {[0:7]}; }
    cp_cache:    coverpoint cache {
      bins c0  = {4'h0};
      bins cF  = {4'hF};
      bins c_other = default;
    }
    cp_region:   coverpoint region {
      bins r0  = {0};
      bins r15 = {15};
      bins r_other = default;
    }
    cp_strb_pop: coverpoint strb_pop iff (is_write) {
      bins none   = {0};
      bins single = {1};
      bins full   = {STRB_W};
      bins some   = {[2:(STRB_W-1)]} iff (STRB_W > 2);
    }
    cp_narrow:   coverpoint narrow;

    cx_burst_size: cross cp_burst, cp_size;
    cx_write_resp: cross cp_is_write, cp_resp;
    cx_narrow_strb: cross cp_narrow, cp_strb_pop iff (is_write) {
      // A narrow transfer is defined by AxSIZE < $clog2(DATA_W/8). In that
      // case, asserting all byte-lanes (full strobe) is not meaningful/legal
      // for most AXI environments; ignore that cross bin so it doesn't become
      // an unreachable-hole magnet.
      ignore_bins narrow_full = binsof(cp_narrow) intersect {1} && binsof(cp_strb_pop.full);
    }
  endgroup
`endif

  `uvm_component_param_utils(axi4_monitor#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name, uvm_component parent);
    super.new(name, parent);
    ap = new("ap", this);
`ifndef VERILATOR
    cov = new();
`endif
  endfunction

  function automatic void get_summary_counts(
    output longint unsigned aw_hs,
    output longint unsigned w_hs,
    output longint unsigned b_hs,
    output longint unsigned ar_hs,
    output longint unsigned r_hs,
    output longint unsigned r_last_hs
  );
    aw_hs     = sum_aw_hs;
    w_hs      = sum_w_hs;
    b_hs      = sum_b_hs;
    ar_hs     = sum_ar_hs;
    r_hs      = sum_r_hs;
    r_last_hs = sum_r_last_hs;
  endfunction

  function automatic void maybe_record(axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) tr, string label);
`ifdef VERILATOR
    return;
`endif
    if (!cfg.tr_record_enable) return;
    void'(begin_tr(tr, cfg.tr_stream_name, label));
    tr.record();
    end_tr(tr);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W))::get(this, "", "cfg", cfg)) begin
      `uvm_fatal(RID, "Missing cfg in config DB (key: cfg)")
    end
    vif = cfg.vif;
    if (vif == null) `uvm_fatal(RID, "cfg.vif is null")

    sum_aw_hs = 0;
    sum_w_hs = 0;
    sum_b_hs = 0;
    sum_ar_hs = 0;
    sum_r_hs = 0;
    sum_r_last_hs = 0;

    stat_cycles = 0;
    stat_aw_hs = 0;
    stat_w_hs  = 0;
    stat_b_hs  = 0;
    stat_ar_hs = 0;
    stat_r_hs  = 0;
    stat_aw_stall = 0;
    stat_w_stall  = 0;
    stat_b_stall  = 0;
    stat_ar_stall = 0;
    stat_r_stall  = 0;
    stat_out_w = 0;
    stat_out_r = 0;
    stat_out_w_max = 0;
    stat_out_r_max = 0;
    wr_lat_min = '1;
    wr_lat_max = 0;
    wr_lat_sum = 0;
    wr_lat_cnt = 0;
    rd_lat_min = '1;
    rd_lat_max = 0;
    rd_lat_sum = 0;
    rd_lat_cnt = 0;

  endfunction

  task run_phase(uvm_phase phase);
    if (!cfg.monitor_enable) begin
      // Keep component alive but inactive.
      forever @(`AXI4_MON_EVT);
    end
    fork
      stats_loop();
      monitor_aw_w_b();
      monitor_ar_r();
    join
  endtask

  task automatic stats_loop();
    longint unsigned last_cycles;
    longint unsigned last_aw_hs;
    longint unsigned last_w_hs;
    longint unsigned last_b_hs;
    longint unsigned last_ar_hs;
    longint unsigned last_r_hs;
    longint unsigned last_aw_stall;
    longint unsigned last_w_stall;
    longint unsigned last_b_stall;
    longint unsigned last_ar_stall;
    longint unsigned last_r_stall;

    if (!cfg.stats_enable) begin
      // Keep thread alive but idle to avoid fork/join termination ordering surprises.
      forever @(`AXI4_MON_EVT);
    end
    while (vif.areset_n !== 1'b1) @(`AXI4_MON_EVT);

    last_cycles   = 0;
    last_aw_hs    = 0;
    last_w_hs     = 0;
    last_b_hs     = 0;
    last_ar_hs    = 0;
    last_r_hs     = 0;
    last_aw_stall = 0;
    last_w_stall  = 0;
    last_b_stall  = 0;
    last_ar_stall = 0;
    last_r_stall  = 0;

    forever begin
      @(`AXI4_MON_EVT);
      stat_cycles++;
      if (`AXI4_MON_CB.awvalid && !`AXI4_MON_CB.awready) stat_aw_stall++;
      if (`AXI4_MON_CB.wvalid  && !`AXI4_MON_CB.wready)  stat_w_stall++;
      if (`AXI4_MON_CB.bvalid  && !`AXI4_MON_CB.bready)  stat_b_stall++;
      if (`AXI4_MON_CB.arvalid && !`AXI4_MON_CB.arready) stat_ar_stall++;
      if (`AXI4_MON_CB.rvalid  && !`AXI4_MON_CB.rready)  stat_r_stall++;

      if (cfg.stats_window_cycles != 0) begin
        longint unsigned win_size;
        longint unsigned win_cycles;
        win_size = longint'(cfg.stats_window_cycles);
        if ((stat_cycles % win_size) == 0) begin
        win_cycles = stat_cycles - last_cycles;
        `uvm_info(RID,
          $sformatf("AXI4 STATS WINDOW cycles=%0d AW=%0d W=%0d B=%0d AR=%0d R=%0d | stalls AW=%0d W=%0d B=%0d AR=%0d R=%0d",
            win_cycles,
            (stat_aw_hs - last_aw_hs), (stat_w_hs - last_w_hs), (stat_b_hs - last_b_hs),
            (stat_ar_hs - last_ar_hs), (stat_r_hs - last_r_hs),
            (stat_aw_stall - last_aw_stall), (stat_w_stall - last_w_stall), (stat_b_stall - last_b_stall),
            (stat_ar_stall - last_ar_stall), (stat_r_stall - last_r_stall)),
          UVM_LOW)
        last_cycles   = stat_cycles;
        last_aw_hs    = stat_aw_hs;
        last_w_hs     = stat_w_hs;
        last_b_hs     = stat_b_hs;
        last_ar_hs    = stat_ar_hs;
        last_r_hs     = stat_r_hs;
        last_aw_stall = stat_aw_stall;
        last_w_stall  = stat_w_stall;
        last_b_stall  = stat_b_stall;
        last_ar_stall = stat_ar_stall;
        last_r_stall  = stat_r_stall;
        end
      end
    end
  endtask

  task automatic monitor_aw_w_b();
    a_chan_t aw;
    item_t tr;
    int unsigned beat_idx;
    bit have_aw = 0;

    while (vif.areset_n !== 1'b1) @(`AXI4_MON_EVT);
    forever begin
      @(`AXI4_MON_EVT);

      if (`AXI4_MON_CB.awvalid && `AXI4_MON_CB.awready) begin
        a_chan_t tmp;
        sum_aw_hs++;
        tmp.id    = `AXI4_MON_CB.awid;
        tmp.addr  = `AXI4_MON_CB.awaddr;
        tmp.len   = `AXI4_MON_CB.awlen;
        tmp.size  = `AXI4_MON_CB.awsize;
        tmp.burst = axi4_burst_e'(`AXI4_MON_CB.awburst);
        tmp.lock  = `AXI4_MON_CB.awlock;
        tmp.cache  = `AXI4_MON_CB.awcache;
        tmp.prot   = `AXI4_MON_CB.awprot;
        tmp.qos    = `AXI4_MON_CB.awqos;
        tmp.region = `AXI4_MON_CB.awregion;
        tmp.user  = `AXI4_MON_CB.awuser;
        aw_q.push_back(tmp);
        if (cfg.stats_enable) begin
          stat_aw_hs++;
          wr_start_cycle[tmp.id].push_back(stat_cycles);
          stat_out_w++;
          if (stat_out_w > stat_out_w_max) stat_out_w_max = stat_out_w;
        end
      end

      if (!have_aw && (aw_q.size() != 0)) begin
        aw = aw_q.pop_front();
        have_aw = 1;
        beat_idx = 0;
        tr = new("mon_wr");
        tr.is_write = 1;
        tr.id    = aw.id;
        tr.addr  = aw.addr;
        tr.len   = aw.len;
        tr.size  = aw.size;
        tr.burst = aw.burst;
        tr.lock  = aw.lock;
        tr.cache  = aw.cache;
        tr.prot   = aw.prot;
        tr.qos    = aw.qos;
        tr.region = aw.region;
        tr.user  = aw.user;
        tr.allocate_payload();
      end

      if (have_aw && (tr != null) && (`AXI4_MON_CB.wvalid && `AXI4_MON_CB.wready)) begin
        sum_w_hs++;
        if (cfg.stats_enable) stat_w_hs++;
        if (beat_idx < tr.num_beats()) begin
          tr.data[beat_idx] = `AXI4_MON_CB.wdata;
          if (tr.strb.size() == tr.num_beats()) tr.strb[beat_idx] = `AXI4_MON_CB.wstrb;
        end
        beat_idx++;
        if (`AXI4_MON_CB.wlast) begin
          wr_wait_b[tr.id].push_back(tr);
          tr = null;
          have_aw = 0;
        end
      end

      if (`AXI4_MON_CB.bvalid && `AXI4_MON_CB.bready) begin
        logic [ID_W-1:0] bid;
        item_t trb;
        int unsigned spop;
        bit is_narrow;
        sum_b_hs++;
        bid = `AXI4_MON_CB.bid;
        if (cfg.stats_enable) begin
          longint unsigned start_c;
          longint unsigned lat;
          stat_b_hs++;
          if (stat_out_w != 0) stat_out_w--;
          if (wr_start_cycle.exists(bid) && (wr_start_cycle[bid].size() != 0)) begin
            start_c = wr_start_cycle[bid].pop_front();
            lat = (stat_cycles >= start_c) ? (stat_cycles - start_c) : 0;
            if (lat < wr_lat_min) wr_lat_min = lat;
            if (lat > wr_lat_max) wr_lat_max = lat;
            wr_lat_sum += lat;
            wr_lat_cnt++;
          end
        end
        if (wr_wait_b.exists(bid) && (wr_wait_b[bid].size() != 0)) begin
          trb = wr_wait_b[bid].pop_front();
          trb.bresp = axi4_resp_e'(`AXI4_MON_CB.bresp);
`ifndef VERILATOR
          if (cfg.coverage_enable) begin
            spop = (trb.strb.size() != 0) ? $countones(trb.strb[0]) : STRB_W;
            is_narrow = (int'(trb.size) < $clog2(DATA_W/8));
            cov.sample(1'b1, trb.burst, int'(trb.size), int'(trb.len), trb.lock, trb.bresp,
              trb.qos, trb.prot, trb.cache, trb.region, spop, is_narrow);
          end
`endif
          maybe_record(trb, "axi4_write");
          ap.write(trb);
          if (cfg.trace_enable) `uvm_info(RID, {"MON write:\n", trb.sprint()}, UVM_LOW)
        end else begin
          `uvm_warning(RID, $sformatf("Observed B (bid=0x%0h) with no matching outstanding write", bid))
        end
      end
    end
  endtask

  task automatic monitor_ar_r();
    while (vif.areset_n !== 1'b1) @(`AXI4_MON_EVT);
    forever begin
      @(`AXI4_MON_EVT);

      if (`AXI4_MON_CB.arvalid && `AXI4_MON_CB.arready) begin
        rd_state_t st;
        sum_ar_hs++;
        st.tr = new("mon_rd");
        st.tr.is_write = 0;
        st.tr.id    = `AXI4_MON_CB.arid;
        st.tr.addr  = `AXI4_MON_CB.araddr;
        st.tr.len   = `AXI4_MON_CB.arlen;
        st.tr.size  = `AXI4_MON_CB.arsize;
        st.tr.burst = axi4_burst_e'(`AXI4_MON_CB.arburst);
        st.tr.lock  = `AXI4_MON_CB.arlock;
        st.tr.cache  = `AXI4_MON_CB.arcache;
        st.tr.prot   = `AXI4_MON_CB.arprot;
        st.tr.qos    = `AXI4_MON_CB.arqos;
        st.tr.region = `AXI4_MON_CB.arregion;
        st.tr.user  = `AXI4_MON_CB.aruser;
        st.tr.allocate_payload();
        st.beat_idx = 0;
        st.beats    = st.tr.num_beats();
        rd_q[st.tr.id].push_back(st);
        if (cfg.stats_enable) begin
          stat_ar_hs++;
          rd_start_cycle[st.tr.id].push_back(stat_cycles);
          stat_out_r++;
          if (stat_out_r > stat_out_r_max) stat_out_r_max = stat_out_r;
        end
      end

      if (`AXI4_MON_CB.rvalid && `AXI4_MON_CB.rready) begin
        logic [ID_W-1:0] rid;
        sum_r_hs++;
        rid = `AXI4_MON_CB.rid;
        if (cfg.stats_enable) stat_r_hs++;
        if (!(rd_q.exists(rid)) || (rd_q[rid].size() == 0)) begin
          `uvm_warning(RID, $sformatf("Observed R (rid=0x%0h) with no matching outstanding read", rid))
        end else begin
          rd_state_t st;
          st = rd_q[rid][0];
          if (st.beat_idx >= st.beats) begin
            `uvm_error(RID, $sformatf("Read beat overflow rid=0x%0h beat_idx=%0d beats=%0d", rid, st.beat_idx, st.beats))
          end else begin
            st.tr.data[st.beat_idx]  = `AXI4_MON_CB.rdata;
            st.tr.rresp[st.beat_idx] = axi4_resp_e'(`AXI4_MON_CB.rresp);
          end
          st.beat_idx++;
          rd_q[rid][0] = st;

          if (`AXI4_MON_CB.rlast) begin
            sum_r_last_hs++;
            st = rd_q[rid].pop_front();
            if (cfg.stats_enable) begin
              longint unsigned start_c;
              longint unsigned lat;
              if (stat_out_r != 0) stat_out_r--;
              if (rd_start_cycle.exists(rid) && (rd_start_cycle[rid].size() != 0)) begin
                start_c = rd_start_cycle[rid].pop_front();
                lat = (stat_cycles >= start_c) ? (stat_cycles - start_c) : 0;
                if (lat < rd_lat_min) rd_lat_min = lat;
                if (lat > rd_lat_max) rd_lat_max = lat;
                rd_lat_sum += lat;
                rd_lat_cnt++;
              end
            end
            maybe_record(st.tr, "axi4_read");
`ifndef VERILATOR
          if (cfg.coverage_enable) begin
            axi4_resp_e resp0;
            int unsigned spop;
            bit is_narrow;
            resp0 = (st.tr.rresp.size() != 0) ? st.tr.rresp[0] : AXI4_RESP_OKAY;
            spop = STRB_W;
            is_narrow = (int'(st.tr.size) < $clog2(DATA_W/8));
            cov.sample(1'b0, st.tr.burst, int'(st.tr.size), int'(st.tr.len), st.tr.lock, resp0,
              st.tr.qos, st.tr.prot, st.tr.cache, st.tr.region, spop, is_narrow);
          end
`endif
          ap.write(st.tr);
          if (cfg.trace_enable) `uvm_info(RID, {"MON read:\n", st.tr.sprint()}, UVM_LOW)
        end
      end
      end
    end
  endtask

  function automatic longint unsigned safe_mean(longint unsigned sum, longint unsigned cnt);
    if (cnt == 0) return 0;
    return (sum / cnt);
  endfunction

  function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    if (!cfg.stats_enable) return;
    `uvm_info(RID,
      $sformatf("AXI4 STATS cycles=%0d AW=%0d W=%0d B=%0d AR=%0d R=%0d | stalls AW=%0d W=%0d B=%0d AR=%0d R=%0d | out_max W=%0d R=%0d | lat_w(min/mean/max)=%0d/%0d/%0d (n=%0d) lat_r(min/mean/max)=%0d/%0d/%0d (n=%0d)",
        stat_cycles, stat_aw_hs, stat_w_hs, stat_b_hs, stat_ar_hs, stat_r_hs,
        stat_aw_stall, stat_w_stall, stat_b_stall, stat_ar_stall, stat_r_stall,
        stat_out_w_max, stat_out_r_max,
        (wr_lat_cnt==0)?0:wr_lat_min, safe_mean(wr_lat_sum, wr_lat_cnt), wr_lat_max, wr_lat_cnt,
        (rd_lat_cnt==0)?0:rd_lat_min, safe_mean(rd_lat_sum, rd_lat_cnt), rd_lat_max, rd_lat_cnt),
      UVM_LOW)
  endfunction

endclass

`undef AXI4_MON_CB
`undef AXI4_MON_EVT

`endif // KVIPS_AXI4_MONITOR_SVH
