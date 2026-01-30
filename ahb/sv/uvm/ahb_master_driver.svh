//------------------------------------------------------------------------------
// AHB Master Driver (pipelined, beat-oriented)
//------------------------------------------------------------------------------
`ifndef KVIPS_AHB_MASTER_DRIVER_SVH
`define KVIPS_AHB_MASTER_DRIVER_SVH

class ahb_master_driver #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2
) extends uvm_driver #(ahb_item#(ADDR_W, DATA_W, HRESP_W));

  localparam string RID = "AHB_MDRV";

  typedef virtual ahb_if #(
    .ADDR_W(ADDR_W),
    .DATA_W(DATA_W),
    .HRESP_W(HRESP_W)
  ) ahb_vif_t;

  ahb_cfg#(ADDR_W, DATA_W, HRESP_W) cfg;
  ahb_vif_t                         vif;

  // State for pipelining
  bit          data_valid;
  bit          data_write;
  int unsigned data_beat;
  ahb_item#(ADDR_W, DATA_W, HRESP_W) cur_item;

  int unsigned cur_beat;
  int unsigned cur_beats;
  int unsigned incr_len_eff;

  `uvm_component_param_utils(ahb_master_driver#(ADDR_W, DATA_W, HRESP_W))

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function int unsigned bytes_per_beat(ahb_size_e size);
    return (1 << size);
  endfunction

  function logic [ADDR_W-1:0] next_addr(logic [ADDR_W-1:0] base, int unsigned beat, ahb_size_e size, ahb_burst_e burst);
    int unsigned bpb;
    int unsigned blen;
    int unsigned boundary;
    logic [ADDR_W-1:0] region_base;
    logic [ADDR_W-1:0] offset;
    logic [ADDR_W-1:0] a;
    bpb = bytes_per_beat(size);
    a = base + beat * bpb;

    case (burst)
      AHB_BURST_WRAP4, AHB_BURST_WRAP8, AHB_BURST_WRAP16: begin
        case (burst)
          AHB_BURST_WRAP4:  blen = 4;
          AHB_BURST_WRAP8:  blen = 8;
          default:          blen = 16;
        endcase
        boundary = blen * bpb;
        region_base = base & ~(boundary-1);
        offset = (base + beat * bpb) & (boundary-1);
        a = region_base | offset;
      end
      default: begin end
    endcase
    return a;
  endfunction

  task drive_idle();
    vif.cb_m.HSEL    <= 1'b1;
    vif.cb_m.HTRANS  <= AHB_TRANS_IDLE;
    vif.cb_m.HADDR   <= '0;
    vif.cb_m.HWRITE  <= 1'b0;
    vif.cb_m.HSIZE   <= AHB_SIZE_32;
    vif.cb_m.HBURST  <= AHB_BURST_SINGLE;
    vif.cb_m.HPROT   <= 4'h0;
    vif.cb_m.HWDATA  <= '0;
    vif.cb_m.HMASTLOCK <= 1'b0;
    vif.cb_m.HMASTER <= '0;
  endtask

  task apply_optional_idles();
    int unsigned gap;
    if (!cfg.insert_idles) return;
    gap = (cfg.idle_gap_max >= cfg.idle_gap_min) ? $urandom_range(cfg.idle_gap_min, cfg.idle_gap_max) : cfg.idle_gap_min;
    repeat (gap) begin
      @(vif.cb_m);
      if (!vif.HRESETn) return;
      if (vif.cb_m.HREADY) drive_idle();
    end
  endtask

  task run_phase(uvm_phase phase);
    bit          next_data_valid;
    bit          next_data_write;
    int unsigned next_data_beat;
    logic [ADDR_W-1:0] next_a;

    super.run_phase(phase);

    if (!uvm_config_db#(ahb_cfg#(ADDR_W, DATA_W, HRESP_W))::get(this, "", "cfg", cfg)) begin
      `uvm_fatal(RID, "Missing cfg in config DB (key: cfg)")
    end
    vif = cfg.vif;
    if (vif == null) `uvm_fatal(RID, "cfg.vif is null")

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

      cur_beats = cur_item.beats;
      cur_beat  = 0;
      cur_item.start_t = $time;

      // Prime bus: we only change signals when HREADY==1
      apply_optional_idles();

      while (cur_beat < cur_beats || data_valid) begin
        @(vif.cb_m);

        if (!vif.HRESETn) begin
          drive_idle();
          data_valid = 0;
          break;
        end

        if (!vif.cb_m.HREADY) begin
          // Stall: hold signals stable (clocking block does this if we don't drive)
          continue;
        end

        // Compute the next-cycle data-phase beat (based on the control we accept now).
        next_data_valid = 0;
        next_data_write = 0;
        next_data_beat  = 0;

        // Drive HWDATA for the beat in the data phase now (accepted previously).
        if (data_valid && data_write && (data_beat < cur_item.wdata.size())) begin
          vif.cb_m.HWDATA <= cur_item.wdata[data_beat];
        end

        // Complete previous beat (data phase) if one is pending.
        if (data_valid) begin
          if (data_beat < cur_item.resp.size()) begin
            cur_item.resp[data_beat] = vif.cb_m.HRESP;
          end
          if (!data_write) begin
            if (data_beat < cur_item.rdata.size()) begin
              cur_item.rdata[data_beat] = vif.cb_m.HRDATA;
            end
          end
        end

        // Issue next control beat (address/control phase) if any.
        if (cur_beat < cur_beats) begin
          next_a = next_addr(cur_item.addr, cur_beat, cur_item.size, cur_item.burst);
          vif.cb_m.HSEL   <= 1'b1;
          vif.cb_m.HADDR  <= next_a;
          vif.cb_m.HWRITE <= cur_item.write;
          vif.cb_m.HSIZE  <= cur_item.size;
          vif.cb_m.HBURST <= cur_item.burst;
          vif.cb_m.HPROT  <= cur_item.prot;
          vif.cb_m.HMASTLOCK <= cur_item.lock;
          vif.cb_m.HTRANS <= (cur_beat == 0) ? AHB_TRANS_NONSEQ : AHB_TRANS_SEQ;

          // This beat becomes the data-phase beat in the next cycle.
          next_data_valid = 1;
          next_data_write = cur_item.write;
          next_data_beat  = cur_beat;
          cur_beat++;
        end else begin
          drive_idle();
        end

        data_valid = next_data_valid;
        data_write = next_data_write;
        data_beat  = next_data_beat;
      end

      cur_item.end_t = $time;
      seq_item_port.item_done();
    end
  endtask

endclass

`endif // KVIPS_AHB_MASTER_DRIVER_SVH
