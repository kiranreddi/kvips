//------------------------------------------------------------------------------
// AHB Master Driver (pipelined, beat-oriented)
//------------------------------------------------------------------------------
`ifndef KVIPS_AHB_MASTER_DRIVER_SVH
`define KVIPS_AHB_MASTER_DRIVER_SVH

class ahb_master_driver #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2,
  bit HAS_HMASTLOCK = 1'b0
) extends uvm_driver #(ahb_item#(ADDR_W, DATA_W, HRESP_W));

  localparam string RID = "AHB_MDRV";

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

  typedef logic [ADDR_W-1:0] addr_t;

`ifdef VERILATOR
`define AHB_M_CB  vif
`define AHB_M_EVT posedge vif.HCLK
`else
`define AHB_M_CB  vif.cb_m
`define AHB_M_EVT vif.cb_m
`endif

  // State for pipelining
  bit          data_valid;
  bit          data_write;
  int unsigned data_beat;
  ahb_item#(ADDR_W, DATA_W, HRESP_W) cur_item;

  int unsigned cur_beat;
  int unsigned cur_beats;
  int unsigned incr_len_eff;

  `uvm_component_param_utils(ahb_master_driver#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK))

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function int unsigned bytes_per_beat(ahb_size_e size);
    return (1 << size);
  endfunction

  function automatic void ensure_item_payload(ref ahb_item#(ADDR_W, DATA_W, HRESP_W) t);
    int unsigned beats;
    logic [DATA_W-1:0] old_wdata[];

    beats = t.beats;
    if (beats == 0) begin
      beats = (t.burst == AHB_BURST_INCR) ? ((t.len == 0) ? 1 : t.len) : t.burst_len(t.burst, t.len);
      if (beats == 0) beats = 1;
      t.beats = beats;
    end

    if (t.write) begin
      if (t.wdata.size() != beats) begin
        old_wdata = t.wdata;
        t.wdata = new[beats];
        for (int unsigned i = 0; i < beats; i++) begin
          if (i < old_wdata.size()) t.wdata[i] = old_wdata[i];
          else t.wdata[i] = '0;
        end
      end
    end else begin
      if (t.wdata.size() != 0) t.wdata = new[0];
    end
    if (t.rdata.size() != beats) t.rdata = new[beats];
    if (t.wait_cycles.size() != beats) t.wait_cycles = new[beats];
    if (t.resp.size() != beats) t.resp = new[beats];
  endfunction

  function logic [ADDR_W-1:0] next_addr(logic [ADDR_W-1:0] base, int unsigned beat, ahb_size_e size, ahb_burst_e burst);
    int unsigned bpb;
    int unsigned blen;
    int unsigned boundary;
    int unsigned base_i;
    logic [ADDR_W-1:0] region_base;
    logic [ADDR_W-1:0] offset;
    logic [ADDR_W-1:0] a;
    bpb = bytes_per_beat(size);
    base_i = int'(base);
    a = addr_t'(base_i + beat * bpb);

    case (burst)
      AHB_BURST_WRAP4, AHB_BURST_WRAP8, AHB_BURST_WRAP16: begin
        case (burst)
          AHB_BURST_WRAP4:  blen = 4;
          AHB_BURST_WRAP8:  blen = 8;
          default:          blen = 16;
        endcase
        boundary = blen * bpb;
        region_base = addr_t'(base_i & ~(boundary-1));
        offset = addr_t'((base_i + beat * bpb) & (boundary-1));
        a = region_base | offset;
      end
      default: begin end
    endcase
    return a;
  endfunction

  task check_item_legality(ahb_item#(ADDR_W, DATA_W, HRESP_W) t);
    if (!cfg.strict_legality_enable) return;
    if (!cfg.legal_transfer(t.addr, t.size, t.burst, t.beats)) begin
      `uvm_fatal(RID, $sformatf(
        "Illegal AHB transfer addr=0x%0h size=%0d burst=%0d beats=%0d (alignment/width/1KB rule)",
        t.addr, t.size, t.burst, t.beats))
    end
  endtask

  task drive_idle();
    vif.HSEL          <= 1'b1;
    vif.HTRANS        <= AHB_TRANS_IDLE;
    vif.HADDR         <= '0;
    vif.HWRITE        <= 1'b0;
    vif.HSIZE         <= AHB_SIZE_32;
    vif.HBURST        <= AHB_BURST_SINGLE;
    vif.HPROT         <= 4'h0;
    vif.HNONSEC       <= 1'b0;
    vif.HMASTER       <= '0;
    vif.HWDATA        <= '0;
    // Optional signals default inside the interface when disabled.
    if (HAS_HMASTLOCK) vif.HMASTLOCK <= 1'b0;
  endtask

  task apply_optional_idles();
    int unsigned gap;
    if (!cfg.insert_idles) return;
    gap = (cfg.idle_gap_max >= cfg.idle_gap_min) ? $urandom_range(cfg.idle_gap_min, cfg.idle_gap_max) : cfg.idle_gap_min;
    repeat (gap) begin
      @(`AHB_M_EVT);
      if (!vif.HRESETn) return;
      if (`AHB_M_CB.HREADY === 1'b1) drive_idle();
    end
  endtask

  task run_phase(uvm_phase phase);
    bit          next_data_valid;
    bit          next_data_write;
    int unsigned next_data_beat;
    logic [ADDR_W-1:0] next_a;
    bit          last_data_valid;
    bit          last_data_write;
    int unsigned last_data_beat;

    super.run_phase(phase);

    if (!uvm_config_db#(ahb_cfg#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK))::get(this, "", "cfg", cfg)) begin
      `uvm_fatal(RID, "Missing cfg in config DB (key: cfg)")
    end
    vif = cfg.vif;
`ifndef VERILATOR
    if (vif == null) `uvm_fatal(RID, "cfg.vif is null")
`endif

    data_valid = 0;
    drive_idle();

    // Wait for reset release
    @(posedge vif.HCLK);
    while (!vif.HRESETn) begin
      @(posedge vif.HCLK);
      drive_idle();
      data_valid = 0;
    end

    forever begin
      seq_item_port.get_next_item(cur_item);

      // Apply config defaults / legality
      cfg.apply_plusargs();
      if (!cfg.allow_bursts) cur_item.burst = AHB_BURST_SINGLE;
      if (!cfg.allow_wrap && (cur_item.burst inside {AHB_BURST_WRAP4,AHB_BURST_WRAP8,AHB_BURST_WRAP16})) cur_item.burst = AHB_BURST_INCR;

      incr_len_eff = cur_item.len;
      if (cur_item.burst == AHB_BURST_INCR) begin
        if (cfg.max_incr_len != 0) incr_len_eff = $urandom_range(1, cfg.max_incr_len);
        cur_item.len = incr_len_eff;
      end

      ensure_item_payload(cur_item);
      check_item_legality(cur_item);
      cur_beats = cur_item.beats;
      cur_beat  = 0;
      cur_item.start_t = $time;
      last_data_valid = 1'b0;
      last_data_write = 1'b0;
      last_data_beat  = 0;

      // Prime bus: we only change signals when HREADY==1
      apply_optional_idles();

      while (cur_beat < cur_beats || data_valid) begin
        @(`AHB_M_EVT);
        // The reference slave updates HREADY/HRESP/HRDATA with nonblocking
        // assignments at the same edge.  Sample after that NBA update so the
        // item captures the completed response/data phase rather than the
        // previous cycle's default value.
        #1step;

        if (!vif.HRESETn) begin
          drive_idle();
          data_valid = 0;
          break;
        end

        // Stall: hold signals stable (clocking block does this if we don't drive)
        begin
          int unsigned stall_cycles;
          stall_cycles = 0;
          while (`AHB_M_CB.HREADY !== 1'b1) begin
            stall_cycles++;
            if ((cfg.handshake_timeout_cycles != 0) && (stall_cycles > cfg.handshake_timeout_cycles)) begin
              `uvm_fatal(RID,
                $sformatf("Timeout waiting for HREADY (HREADY=%b HREADYOUT=%b HRESETn=%b HSEL=%b HTRANS=%b)",
                  `AHB_M_CB.HREADY, `AHB_M_CB.HREADYOUT, vif.HRESETn, vif.HSEL, vif.HTRANS))
            end
            @(`AHB_M_EVT);
            if (!vif.HRESETn) break;
          end
          if (!vif.HRESETn) continue;
        end

        // The responder is a clocked reference model.  In AHB Full mode its
        // RETRY/SPLIT response is intentionally generated one cycle after the
        // control pipeline observes the transfer.  Give that response one
        // settling edge before completing a forced-response transfer.
        if (cfg.mode == AHB_MODE_FULL && cfg.force_resp_enable && data_valid) begin
          @(`AHB_M_EVT);
          #1step;
          while (vif.HREADY !== 1'b1) begin
            @(`AHB_M_EVT);
            #1step;
          end
          // The clocking-block inputs used below sample at the next edge.
          @(`AHB_M_EVT);
        end

        // Compute the next-cycle data-phase beat (based on the control we accept now).
        next_data_valid = 0;
        next_data_write = 0;
        next_data_beat  = 0;

        // Drive HWDATA for the beat in the data phase now (accepted previously).
        if (data_valid && data_write && (data_beat < cur_item.wdata.size())) begin
          vif.HWDATA <= cur_item.wdata[data_beat];
        end

        // Complete previous beat (data phase) if one is pending.
        if (data_valid) begin
          last_data_valid = 1'b1;
          last_data_write = data_write;
          last_data_beat  = data_beat;
          if (data_beat < cur_item.resp.size()) begin
            cur_item.resp[data_beat] = `AHB_M_CB.HRESP;
          end
          if (!data_write) begin
            if (data_beat < cur_item.rdata.size()) begin
              cur_item.rdata[data_beat] = `AHB_M_CB.HRDATA;
            end
          end
        end

        // Issue next control beat (address/control phase) if any. BUSY is a
        // legal non-transfer control phase between burst beats; it preserves
        // the previous address/control and does not advance the beat index.
        if (cur_beat < cur_beats) begin
          bit insert_busy_now;
          insert_busy_now = (cur_beat > 0) && cfg.insert_busy &&
                            ($urandom_range(0, 99) < cfg.busy_pct);
          if (insert_busy_now) begin
            vif.HTRANS <= AHB_TRANS_BUSY;
          end else begin
            next_a = next_addr(cur_item.addr, cur_beat, cur_item.size, cur_item.burst);
            vif.HSEL         <= 1'b1;
            vif.HADDR        <= next_a;
            vif.HWRITE       <= cur_item.write;
            vif.HSIZE        <= cur_item.size;
            vif.HBURST       <= cur_item.burst;
            vif.HPROT        <= cur_item.prot;
            vif.HNONSEC      <= cur_item.nonsec;
            vif.HMASTER      <= cur_item.master_id;
            if (HAS_HMASTLOCK) vif.HMASTLOCK <= cur_item.lock;
            vif.HTRANS       <= (cur_beat == 0) ? AHB_TRANS_NONSEQ : AHB_TRANS_SEQ;
            if (cur_item.write && (cur_beat < cur_item.wdata.size())) begin
              vif.HWDATA <= cur_item.wdata[cur_beat];
            end

            // This beat becomes the data-phase beat in the next cycle.
            next_data_valid = 1;
            next_data_write = cur_item.write;
            next_data_beat  = cur_beat;
            cur_beat++;
          end
        end else begin
          // Keep write data stable through the responder's data phase.  The
          // control phase can return to IDLE immediately, but clearing
          // HWDATA here would make a one-beat write appear as zero to a
          // clocked slave that samples it one pipeline stage later.
          if (!(data_valid && data_write)) drive_idle();
        end

        data_valid = next_data_valid;
        data_write = next_data_write;
        data_beat  = next_data_beat;
      end

      // The reference slave reconstructs the address/data pipeline with a
      // separate control and data-phase register.  Allow two settling edges
      // after the final control phase so the last response/data beat is
      // retired before item_done() releases the next sequence item.  Keep the
      // final write data stable until the first of those edges.
      if (last_data_valid && last_data_write) begin
        vif.HSEL   <= 1'b1;
        vif.HTRANS <= AHB_TRANS_IDLE;
      end else begin
        drive_idle();
      end
      repeat (2) begin
        @(`AHB_M_EVT);
        #1step;
      end
      if (last_data_valid && (last_data_beat < cur_item.resp.size())) begin
        cur_item.resp[last_data_beat] = `AHB_M_CB.HRESP;
        if (!last_data_write && (last_data_beat < cur_item.rdata.size()))
          cur_item.rdata[last_data_beat] = `AHB_M_CB.HRDATA;
      end
      drive_idle();

      cur_item.end_t = $time;
      seq_item_port.item_done();
    end
  endtask

endclass

`undef AHB_M_CB
`undef AHB_M_EVT

`endif // KVIPS_AHB_MASTER_DRIVER_SVH
