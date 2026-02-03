//------------------------------------------------------------------------------
// AXI4 Sequences
//------------------------------------------------------------------------------

`ifndef KVIPS_AXI4_SEQUENCES_SVH
`define KVIPS_AXI4_SEQUENCES_SVH

`ifdef VERILATOR
  /* verilator lint_off WIDTHEXPAND */
  /* verilator lint_off WIDTHTRUNC */
`endif

class axi4_base_seq #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends uvm_sequence #(axi4_item#(ADDR_W, DATA_W, ID_W, USER_W));

  `uvm_object_param_utils(axi4_base_seq#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name = "axi4_base_seq");
    super.new(name);
  endfunction

endclass

// Sequence wrapper to send a pre-constructed item on a sequencer.
class axi4_item_seq #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends axi4_base_seq#(ADDR_W, DATA_W, ID_W, USER_W);

  axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) item;

  `uvm_object_param_utils(axi4_item_seq#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name = "axi4_item_seq");
    super.new(name);
  endfunction

  task body();
    if (item == null) `uvm_fatal(get_type_name(), "item is null")
    req = item;
    start_item(req);
    finish_item(req);
  endtask

endclass

class axi4_write_readback_seq #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends axi4_base_seq#(ADDR_W, DATA_W, ID_W, USER_W);

  rand int unsigned num_txns = 50;
  rand int unsigned max_len  = 7; // AXI len is beats-1
  rand bit          enable_wrap  = 1'b1;
  rand bit          enable_fixed = 1'b1;
  rand bit          enable_incr  = 1'b1;
  rand bit          enable_narrow = 1'b1;
  rand bit          enable_random_id = 1'b0;
  // When using the KVIPS pipelined master driver, the driver completes items
  // immediately and returns results via the sequencer response queue.
  // Set this to 1 to drain expected responses at the end of the sequence.
  bit               collect_responses = 1'b0;

  rand logic [ADDR_W-1:0] base_addr = 32'h1000;

  `uvm_object_param_utils(axi4_write_readback_seq#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name = "axi4_write_readback_seq");
    super.new(name);
  endfunction

  function automatic axi4_burst_e pick_burst();
    axi4_burst_e choices[$];
    if (enable_incr)  choices.push_back(AXI4_BURST_INCR);
    if (enable_fixed) choices.push_back(AXI4_BURST_FIXED);
    if (enable_wrap)  choices.push_back(AXI4_BURST_WRAP);
    if (choices.size() == 0) return AXI4_BURST_INCR;
    return choices[$urandom_range(0, choices.size()-1)];
  endfunction

  function automatic int unsigned pick_len(axi4_burst_e burst, int unsigned max_len);
    int unsigned cap;
    int unsigned choices[$];
    cap = max_len;
    if (cap > 255) cap = 255;
    if ((burst == AXI4_BURST_FIXED) || (burst == AXI4_BURST_WRAP)) begin
      if (cap > 15) cap = 15;
    end
    if (burst == AXI4_BURST_WRAP) begin
      if (1 <= cap)  choices.push_back(1);
      if (3 <= cap)  choices.push_back(3);
      if (7 <= cap)  choices.push_back(7);
      if (15 <= cap) choices.push_back(15);
      if (choices.size() == 0) return 1;
      return choices[$urandom_range(0, choices.size()-1)];
    end
    if (cap == 0) return 0;
    return $urandom_range(0, cap);
  endfunction

  function automatic int unsigned pick_size();
    int unsigned max_size = $clog2(DATA_W/8);
    if (!enable_narrow) return max_size;
    return $urandom_range(0, max_size);
  endfunction

  task body();
    for (int unsigned t = 0; t < num_txns; t++) begin
      axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) wr;
      axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) rd;
      int unsigned size;
      axi4_burst_e burst;
      int unsigned len;

      size  = pick_size();
      burst = pick_burst();
      len   = pick_len(burst, max_len);

      // Write
      wr = new($sformatf("wr_%0d", t));
      wr.is_write = 1;
      wr.id       = enable_random_id ? $urandom() : '0;
      wr.len      = len[7:0];
      wr.size     = size[2:0];
      wr.burst    = burst;
      wr.user     = '0;
      // Pick an address that stays within a 4KB window for this burst.
      begin
        longint unsigned bus_bytes;
        longint unsigned bytes_per_beat;
        longint unsigned total_bytes;
        longint unsigned base4k;
        longint unsigned max_off;
        longint unsigned off;
        longint unsigned a;
        bus_bytes      = (DATA_W/8);
        bytes_per_beat = longint'(1) << size;
        total_bytes    = (longint'(len) + 1) * bytes_per_beat;
        base4k         = (longint'(base_addr) & ~longint'(12'hFFF));
        max_off        = (total_bytes >= 4096) ? 0 : (4096 - total_bytes);
        off            = (max_off == 0) ? 0 : $urandom_range(0, int'(max_off));
        // Align to transfer size
        off            = (off / bytes_per_beat) * bytes_per_beat;
        a              = base4k + off + longint'(t) * bus_bytes;
        // Re-align into 4KB window if t term pushed us over the max offset
        off            = (a & 12'hFFF);
        if ((off + total_bytes) > 4096) begin
          off = (max_off / bytes_per_beat) * bytes_per_beat;
          a   = base4k + off;
        end
        // Additional WRAP alignment to the wrap container
        if (burst == AXI4_BURST_WRAP) begin
          longint unsigned container;
          container = total_bytes;
          if (container != 0) a = (a / container) * container;
        end
        wr.addr = a[ADDR_W-1:0];
      end
      wr.allocate_payload();
      for (int unsigned i = 0; i < wr.num_beats(); i++) begin
        wr.data[i] = {$urandom(), $urandom()};
        if (DATA_W <= 32) wr.data[i] = $urandom();
        // Generate legal WSTRB for the transfer size and address lane.
        begin
          int unsigned bus_bytes;
          int unsigned bytes_per_beat;
          longint unsigned beat_a;
          int unsigned lane;
          bus_bytes      = (DATA_W/8);
          bytes_per_beat = (1 << size);
          if (bytes_per_beat >= bus_bytes) begin
            wr.strb[i] = '1;
          end else begin
            beat_a = axi4_beat_addr(longint'(wr.addr), size, len, burst, i);
            lane   = int'(beat_a % bus_bytes);
            wr.strb[i] = (((1 << bytes_per_beat) - 1) << lane);
          end
        end
      end

      start_item(wr);
      finish_item(wr);

      // Read back (same burst shape)
      rd = new($sformatf("rd_%0d", t));
      rd.is_write = 0;
      rd.id       = wr.id;
      rd.addr     = wr.addr;
      rd.len      = wr.len;
      rd.size     = wr.size;
      rd.burst    = wr.burst;
      rd.user     = wr.user;
      rd.allocate_payload();

      start_item(rd);
      finish_item(rd);
    end

    if (collect_responses) begin
      axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) rsp;
      for (int unsigned i = 0; i < (2 * num_txns); i++) begin
        get_response(rsp);
      end
    end
  endtask

endclass

class axi4_write_burst_seq #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends axi4_base_seq#(ADDR_W, DATA_W, ID_W, USER_W);

  rand logic [ADDR_W-1:0] start_addr = '0;
  rand int unsigned       num_txns   = 10;
  rand int unsigned       max_len    = 7; // len is beats-1
  rand logic [ID_W-1:0]   id         = '0;

  `uvm_object_param_utils(axi4_write_burst_seq#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name = "axi4_write_burst_seq");
    super.new(name);
  endfunction

  task body();
    for (int unsigned t = 0; t < num_txns; t++) begin
      axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) tr;
      tr = axi4_item#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create($sformatf("wr_%0d", t));
      start_item(tr);
      tr.is_write = 1;
      tr.id       = id;
      tr.addr     = start_addr + t*(DATA_W/8);
      tr.len      = (max_len == 0) ? 0 : $urandom_range(0, max_len);
      tr.size     = $clog2(DATA_W/8);
      tr.burst    = AXI4_BURST_INCR;
      tr.user     = '0;
      tr.allocate_payload();
      for (int unsigned i = 0; i < tr.num_beats(); i++) begin
        tr.data[i] = {$urandom(), $urandom()};
        if (DATA_W <= 32) tr.data[i] = $urandom();
        tr.strb[i] = '1;
      end
      finish_item(tr);
    end
  endtask

endclass

class axi4_read_burst_seq #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends axi4_base_seq#(ADDR_W, DATA_W, ID_W, USER_W);

  rand logic [ADDR_W-1:0] start_addr = '0;
  rand int unsigned       num_txns   = 10;
  rand int unsigned       max_len    = 7;
  rand logic [ID_W-1:0]   id         = '0;

  `uvm_object_param_utils(axi4_read_burst_seq#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name = "axi4_read_burst_seq");
    super.new(name);
  endfunction

  task body();
    for (int unsigned t = 0; t < num_txns; t++) begin
      axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) tr;
      tr = axi4_item#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create($sformatf("rd_%0d", t));
      start_item(tr);
      tr.is_write = 0;
      tr.id       = id;
      tr.addr     = start_addr + t*(DATA_W/8);
      tr.len      = (max_len == 0) ? 0 : $urandom_range(0, max_len);
      tr.size     = $clog2(DATA_W/8);
      tr.burst    = AXI4_BURST_INCR;
      tr.user     = '0;
      tr.allocate_payload();
      finish_item(tr);
    end
  endtask

endclass

// Pipelined stress: dispatch many transactions without waiting for completion,
// then drain responses from the sequencer response queue.
class axi4_pipelined_stress_seq #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends axi4_base_seq#(ADDR_W, DATA_W, ID_W, USER_W);

  localparam int STRB_W = DATA_W/8;

  rand int unsigned num_pairs = 50;
  rand int unsigned max_len   = 31;
  rand logic [ADDR_W-1:0] base_addr = 32'h1000;
  rand bit enable_wrap  = 1'b1;
  rand bit enable_fixed = 1'b1;
  rand bit enable_incr  = 1'b1;
  rand bit enable_narrow = 1'b1;

  `uvm_object_param_utils(axi4_pipelined_stress_seq#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name = "axi4_pipelined_stress_seq");
    super.new(name);
  endfunction

  function automatic axi4_burst_e pick_burst();
    axi4_burst_e choices[$];
    if (enable_incr)  choices.push_back(AXI4_BURST_INCR);
    if (enable_fixed) choices.push_back(AXI4_BURST_FIXED);
    if (enable_wrap)  choices.push_back(AXI4_BURST_WRAP);
    if (choices.size() == 0) return AXI4_BURST_INCR;
    return choices[$urandom_range(0, choices.size()-1)];
  endfunction

  function automatic int unsigned pick_len(axi4_burst_e burst, int unsigned max_len_in);
    int unsigned cap;
    int unsigned choices[$];
    cap = max_len_in;
    if (cap > 255) cap = 255;
    if ((burst == AXI4_BURST_FIXED) || (burst == AXI4_BURST_WRAP)) begin
      if (cap > 15) cap = 15;
    end
    if (burst == AXI4_BURST_WRAP) begin
      if (1 <= cap)  choices.push_back(1);
      if (3 <= cap)  choices.push_back(3);
      if (7 <= cap)  choices.push_back(7);
      if (15 <= cap) choices.push_back(15);
      if (choices.size() == 0) return 1;
      return choices[$urandom_range(0, choices.size()-1)];
    end
    if (cap == 0) return 0;
    return $urandom_range(0, cap);
  endfunction

  function automatic int unsigned pick_size();
    int unsigned max_size = $clog2(DATA_W/8);
    if (!enable_narrow) return max_size;
    return $urandom_range(0, max_size);
  endfunction

  task body();
    int unsigned num_writes;
    int unsigned num_reads;
    int unsigned wr_rsp_seen;
    int unsigned rd_rsp_seen;
    bit stop_rsp_drain;
    bit rsp_drain_done;
    axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) wrs[$];
    axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) rsp;

    num_writes = num_pairs;
    num_reads  = num_pairs;
    wr_rsp_seen = 0;
    rd_rsp_seen = 0;
    stop_rsp_drain = 0;
    rsp_drain_done = 0;

    // Background drain of responses to avoid sequencer response queue overflow.
    fork
      begin : rsp_drain
        int unsigned total_needed;
        total_needed = num_writes + num_reads;
        while (!stop_rsp_drain && ((wr_rsp_seen + rd_rsp_seen) < total_needed)) begin
          get_response(rsp);
          if (rsp == null) continue;
          if (rsp.is_write) wr_rsp_seen++;
          else              rd_rsp_seen++;
        end
        rsp_drain_done = 1'b1;
      end
    join_none

    // Phase 1: issue many writes (multi-outstanding), drain write responses.
    for (int unsigned t = 0; t < num_writes; t++) begin
      axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) wr;
      int unsigned size;
      axi4_burst_e burst;
      int unsigned len;
      logic [ID_W-1:0] id;

      size  = pick_size();
      burst = pick_burst();
      len   = pick_len(burst, max_len);
      id    = $urandom();

      wr = new($sformatf("wr_%0d", t));
      wr.is_write = 1;
      wr.id       = id;
      wr.len      = len[7:0];
      wr.size     = size[2:0];
      wr.burst    = burst;
      wr.user     = '0;
      wr.addr     = base_addr + t*(DATA_W/8);
      // Reuse the same legality shaping as axi4_write_readback_seq.
      begin
        longint unsigned bytes_per_beat;
        longint unsigned total_bytes;
        longint unsigned base4k;
        longint unsigned max_off;
        longint unsigned off;
        longint unsigned a;
        bytes_per_beat = longint'(1) << size;
        total_bytes    = (longint'(len) + 1) * bytes_per_beat;
        base4k         = (longint'(wr.addr) & ~longint'(12'hFFF));
        max_off        = (total_bytes >= 4096) ? 0 : (4096 - total_bytes);
        off            = (max_off == 0) ? 0 : $urandom_range(0, int'(max_off));
        off            = (off / bytes_per_beat) * bytes_per_beat;
        a              = base4k + off;
        if (burst == AXI4_BURST_WRAP) begin
          longint unsigned container;
          container = total_bytes;
          if (container != 0) a = (a / container) * container;
        end
        wr.addr = a[ADDR_W-1:0];
      end
      wr.allocate_payload();
      for (int unsigned i = 0; i < wr.num_beats(); i++) begin
        wr.data[i] = {$urandom(), $urandom()};
        if (DATA_W <= 32) wr.data[i] = $urandom();
        begin
          int unsigned bus_bytes;
          int unsigned bytes_per;
          longint unsigned beat_a;
          int unsigned lane;
          bus_bytes = (DATA_W/8);
          bytes_per = (1 << size);
          if (bytes_per >= bus_bytes) begin
            wr.strb[i] = '1;
          end else begin
            beat_a = axi4_beat_addr(longint'(wr.addr), size, len, burst, i);
            lane   = int'(beat_a % bus_bytes);
            wr.strb[i] = (((1 << bytes_per) - 1) << lane);
          end
        end
      end

      start_item(wr);
      finish_item(wr);

      wrs.push_back(wr);
    end

    wait (wr_rsp_seen >= num_writes);

    // Phase 2: issue reads after all writes completed (readback correctness),
    // drain read responses.
    for (int unsigned t = 0; t < num_reads; t++) begin
      axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) rd;
      logic [ID_W-1:0] id;

      id    = $urandom();

      rd = new($sformatf("rd_%0d", t));
      rd.is_write = 0;
      rd.id       = id;
      rd.user     = '0;
      rd.addr     = wrs[t].addr;
      rd.len      = wrs[t].len;
      rd.size     = wrs[t].size;
      rd.burst    = wrs[t].burst;
      rd.allocate_payload();

      start_item(rd);
      finish_item(rd);
    end

    wait (rd_rsp_seen >= num_reads);
    stop_rsp_drain = 1'b1;
    wait (rsp_drain_done);
  endtask

endclass

// Directed sequence: sweep legal SIZE values and byte lanes, write then readback.
class axi4_lane_sweep_seq #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends axi4_base_seq#(ADDR_W, DATA_W, ID_W, USER_W);

  localparam int STRB_W = DATA_W/8;

  rand logic [ADDR_W-1:0] base_addr = 32'h2000;
  rand logic [ID_W-1:0]   id        = '0;

  `uvm_object_param_utils(axi4_lane_sweep_seq#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name = "axi4_lane_sweep_seq");
    super.new(name);
  endfunction

  task body();
    int unsigned max_size = $clog2(STRB_W);
    for (int unsigned s = 0; s <= max_size; s++) begin
      int unsigned bytes_per = (1 << s);
      int unsigned lanes = (bytes_per >= STRB_W) ? 1 : (STRB_W / bytes_per);
      for (int unsigned lane = 0; lane < lanes; lane++) begin
        axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) wr;
        axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) rd;
        logic [STRB_W-1:0] strb_mask;
        logic [DATA_W-1:0] data_word;
        logic [ADDR_W-1:0] addr;

        addr = (base_addr / STRB_W) * STRB_W;
        addr = addr + (lane * bytes_per);
        strb_mask = (bytes_per >= STRB_W)
          ? '1
          : ((((1 << bytes_per) - 1) << (lane * bytes_per)));

        data_word = '0;
        for (int unsigned b = 0; b < STRB_W; b++) begin
          if (strb_mask[b]) data_word[8*b +: 8] = (8'hA0 + b[7:0]);
        end

        wr = new($sformatf("wr_s%0d_lane%0d", s, lane));
        wr.is_write = 1'b1;
        wr.id       = id;
        wr.addr     = addr;
        wr.len      = 8'd0;
        wr.size     = s[2:0];
        wr.burst    = AXI4_BURST_INCR;
        wr.user     = '0;
        wr.allocate_payload();
        wr.data[0] = data_word;
        wr.strb[0] = strb_mask;
        start_item(wr);
        finish_item(wr);

        rd = new($sformatf("rd_s%0d_lane%0d", s, lane));
        rd.is_write = 1'b0;
        rd.id       = id;
        rd.addr     = addr;
        rd.len      = 8'd0;
        rd.size     = s[2:0];
        rd.burst    = AXI4_BURST_INCR;
        rd.user     = '0;
        rd.allocate_payload();
        start_item(rd);
        finish_item(rd);
      end
    end
  endtask

endclass

// Directed sequence: corner cases around burst length extremes and 4KB boundaries.
class axi4_corner_case_seq #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends axi4_base_seq#(ADDR_W, DATA_W, ID_W, USER_W);

  rand logic [ADDR_W-1:0] base_addr = 32'h10000;

  `uvm_object_param_utils(axi4_corner_case_seq#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name = "axi4_corner_case_seq");
    super.new(name);
  endfunction

  function automatic logic [ADDR_W-1:0] pick_edge_addr(
    input logic [ADDR_W-1:0] base4k,
    input int unsigned       size,
    input int unsigned       len,
    input axi4_burst_e       burst
  );
    longint unsigned bytes_per_beat;
    longint unsigned total_bytes;
    longint unsigned max_off;
    longint unsigned off;
    longint unsigned a;

    bytes_per_beat = longint'(1) << size;
    total_bytes    = axi4_total_bytes(size, len);
    // Park the burst at the end of the 4KB window without crossing.
    max_off = (total_bytes >= 4096) ? 0 : (4096 - total_bytes);
    off     = (max_off / bytes_per_beat) * bytes_per_beat;
    a       = longint'(base4k) + off;

    if (burst == AXI4_BURST_WRAP) begin
      longint unsigned container;
      container = total_bytes;
      if (container != 0) a = (a / container) * container;
    end

    return a[ADDR_W-1:0];
  endfunction

  task body();
    logic [ADDR_W-1:0] base4k;
    base4k = logic'(longint'(base_addr) & ~longint'(12'hFFF));

    // 1) Max INCR length (256 beats) at smallest size, aligned at 4KB base.
    begin
      axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) wr;
      axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) rd;
      wr = new("wr_incr_256beat");
      wr.is_write = 1;
      wr.id       = '0;
      wr.addr     = base4k;
      wr.len      = 8'd255;
      wr.size     = 3'd0; // 1 byte
      wr.burst    = AXI4_BURST_INCR;
      wr.lock     = 1'b0;
      wr.user     = '0;
      wr.allocate_payload();
      for (int unsigned i = 0; i < wr.num_beats(); i++) begin
        wr.data[i] = {$urandom(), $urandom()};
        if (DATA_W <= 32) wr.data[i] = $urandom();
        wr.strb[i] = '1;
      end
      start_item(wr);
      finish_item(wr);

      rd = new("rd_incr_256beat");
      rd.is_write = 0;
      rd.id       = wr.id;
      rd.addr     = wr.addr;
      rd.len      = wr.len;
      rd.size     = wr.size;
      rd.burst    = wr.burst;
      rd.lock     = wr.lock;
      rd.user     = wr.user;
      rd.allocate_payload();
      start_item(rd);
      finish_item(rd);
    end

    // 2) Edge-of-4KB addressing for different burst types/sizes.
    begin
      axi4_burst_e bursts[$];
      bursts.push_back(AXI4_BURST_INCR);
      bursts.push_back(AXI4_BURST_FIXED);
      bursts.push_back(AXI4_BURST_WRAP);
      foreach (bursts[i]) begin
        axi4_burst_e burst;
        int unsigned size;
        int unsigned len;
        axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) wr;
        axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) rd;
        burst = bursts[i];
        size  = $urandom_range(0, $clog2(DATA_W/8));
        len   = (burst == AXI4_BURST_INCR) ? 15 : 7;
        if (burst == AXI4_BURST_WRAP) len = 15;

        wr = new($sformatf("wr_edge_%0d", i));
        wr.is_write = 1;
        wr.id       = logic'(i[ID_W-1:0]);
        wr.len      = len[7:0];
        wr.size     = size[2:0];
        wr.burst    = burst;
        wr.addr     = pick_edge_addr(base4k, size, len, burst);
        wr.lock     = 1'b0;
        wr.user     = '0;
        wr.allocate_payload();
        for (int unsigned b = 0; b < wr.num_beats(); b++) begin
          wr.data[b] = {$urandom(), $urandom()};
          if (DATA_W <= 32) wr.data[b] = $urandom();
          wr.strb[b] = '1;
        end
        start_item(wr);
        finish_item(wr);

        rd = new($sformatf("rd_edge_%0d", i));
        rd.is_write = 0;
        rd.id       = wr.id;
        rd.addr     = wr.addr;
        rd.len      = wr.len;
        rd.size     = wr.size;
        rd.burst    = wr.burst;
        rd.lock     = wr.lock;
        rd.user     = wr.user;
        rd.allocate_payload();
        start_item(rd);
        finish_item(rd);
      end
    end
  endtask

endclass

class axi4_exclusive_basic_seq #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends axi4_base_seq#(ADDR_W, DATA_W, ID_W, USER_W);

  rand logic [ADDR_W-1:0] addr = 32'h2000;
  rand logic [ID_W-1:0]   id   = '0;

  `uvm_object_param_utils(axi4_exclusive_basic_seq#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name = "axi4_exclusive_basic_seq");
    super.new(name);
  endfunction

  task body();
    axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) wr0;
    axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) exrd;
    axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) exwr;
    axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) rd;

    // Seed memory at addr.
    wr0 = new("wr0");
    wr0.is_write = 1'b1;
    wr0.lock     = 1'b0;
    wr0.id       = id;
    wr0.addr     = addr;
    wr0.len      = 8'd0;
    wr0.size     = $clog2(DATA_W/8);
    wr0.burst    = AXI4_BURST_INCR;
    wr0.user     = '0;
    wr0.allocate_payload();
    wr0.data[0] = {$urandom(), $urandom()};
    if (DATA_W <= 32) wr0.data[0] = $urandom();
    wr0.strb[0] = '1;
    start_item(wr0);
    finish_item(wr0);

    // Exclusive read establishes reservation; expect EXOKAY.
    exrd = new("exrd");
    exrd.is_write = 1'b0;
    exrd.lock     = 1'b1;
    exrd.id       = id;
    exrd.addr     = addr;
    exrd.len      = 8'd0;
    exrd.size     = $clog2(DATA_W/8);
    exrd.burst    = AXI4_BURST_INCR;
    exrd.user     = '0;
    exrd.allocate_payload();
    start_item(exrd);
    finish_item(exrd);
    if (exrd.rresp.size() != 1) `uvm_fatal(get_type_name(), "Exclusive read unexpected rresp size")
    if (exrd.rresp[0] != AXI4_RESP_EXOKAY) begin
      `uvm_fatal(get_type_name(), $sformatf("Exclusive read expected EXOKAY, got %0d", exrd.rresp[0]))
    end

    // Exclusive write should succeed and return EXOKAY.
    exwr = new("exwr");
    exwr.is_write = 1'b1;
    exwr.lock     = 1'b1;
    exwr.id       = id;
    exwr.addr     = addr;
    exwr.len      = 8'd0;
    exwr.size     = $clog2(DATA_W/8);
    exwr.burst    = AXI4_BURST_INCR;
    exwr.user     = '0;
    exwr.allocate_payload();
    exwr.data[0] = ~wr0.data[0];
    exwr.strb[0] = '1;
    start_item(exwr);
    finish_item(exwr);
    if (exwr.bresp != AXI4_RESP_EXOKAY) begin
      `uvm_fatal(get_type_name(), $sformatf("Exclusive write expected EXOKAY, got %0d", exwr.bresp))
    end

    // Read back and check the new value landed.
    rd = new("rd");
    rd.is_write = 1'b0;
    rd.lock     = 1'b0;
    rd.id       = id;
    rd.addr     = addr;
    rd.len      = 8'd0;
    rd.size     = $clog2(DATA_W/8);
    rd.burst    = AXI4_BURST_INCR;
    rd.user     = '0;
    rd.allocate_payload();
    start_item(rd);
    finish_item(rd);
    if (rd.data.size() != 1) `uvm_fatal(get_type_name(), "Readback unexpected data size")
    if (rd.data[0] != exwr.data[0]) begin
      `uvm_fatal(get_type_name(), $sformatf("Readback mismatch exp=0x%0h got=0x%0h", exwr.data[0], rd.data[0]))
    end
  endtask

endclass

class axi4_exclusive_fail_seq #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends axi4_base_seq#(ADDR_W, DATA_W, ID_W, USER_W);

  rand logic [ADDR_W-1:0] addr = 32'h3000;
  rand logic [ID_W-1:0]   id   = '0;

  `uvm_object_param_utils(axi4_exclusive_fail_seq#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name = "axi4_exclusive_fail_seq");
    super.new(name);
  endfunction

  task body();
    axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) wr0;
    axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) exrd;
    axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) wr1;
    axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) exwr;
    axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) rd;

    // Seed.
    wr0 = new("wr0");
    wr0.is_write = 1'b1;
    wr0.lock     = 1'b0;
    wr0.id       = id;
    wr0.addr     = addr;
    wr0.len      = 8'd0;
    wr0.size     = $clog2(DATA_W/8);
    wr0.burst    = AXI4_BURST_INCR;
    wr0.user     = '0;
    wr0.allocate_payload();
    wr0.data[0] = {$urandom(), $urandom()};
    if (DATA_W <= 32) wr0.data[0] = $urandom();
    wr0.strb[0] = '1;
    start_item(wr0);
    finish_item(wr0);

    // Exclusive read reservation.
    exrd = new("exrd");
    exrd.is_write = 1'b0;
    exrd.lock     = 1'b1;
    exrd.id       = id;
    exrd.addr     = addr;
    exrd.len      = 8'd0;
    exrd.size     = $clog2(DATA_W/8);
    exrd.burst    = AXI4_BURST_INCR;
    exrd.user     = '0;
    exrd.allocate_payload();
    start_item(exrd);
    finish_item(exrd);
    if (exrd.rresp.size() != 1) `uvm_fatal(get_type_name(), "Exclusive read unexpected rresp size")
    if (exrd.rresp[0] != AXI4_RESP_EXOKAY) begin
      `uvm_fatal(get_type_name(), $sformatf("Exclusive read expected EXOKAY, got %0d", exrd.rresp[0]))
    end

    // Intervening normal write to the same location invalidates the reservation.
    wr1 = new("wr1");
    wr1.is_write = 1'b1;
    wr1.lock     = 1'b0;
    wr1.id       = id;
    wr1.addr     = addr;
    wr1.len      = 8'd0;
    wr1.size     = $clog2(DATA_W/8);
    wr1.burst    = AXI4_BURST_INCR;
    wr1.user     = '0;
    wr1.allocate_payload();
    wr1.data[0] = ~wr0.data[0];
    wr1.strb[0] = '1;
    start_item(wr1);
    finish_item(wr1);

    // Exclusive write should fail (OKAY) and must not update memory.
    exwr = new("exwr");
    exwr.is_write = 1'b1;
    exwr.lock     = 1'b1;
    exwr.id       = id;
    exwr.addr     = addr;
    exwr.len      = 8'd0;
    exwr.size     = $clog2(DATA_W/8);
    exwr.burst    = AXI4_BURST_INCR;
    exwr.user     = '0;
    exwr.allocate_payload();
    exwr.data[0] = 64'hDEADBEEF_DEADBEEF;
    if (DATA_W <= 32) exwr.data[0] = 32'hDEADBEEF;
    exwr.strb[0] = '1;
    start_item(exwr);
    finish_item(exwr);
    if (exwr.bresp != AXI4_RESP_OKAY) begin
      `uvm_fatal(get_type_name(), $sformatf("Exclusive write expected OKAY (fail), got %0d", exwr.bresp))
    end

    // Read back should still be wr1's value.
    rd = new("rd");
    rd.is_write = 1'b0;
    rd.lock     = 1'b0;
    rd.id       = id;
    rd.addr     = addr;
    rd.len      = 8'd0;
    rd.size     = $clog2(DATA_W/8);
    rd.burst    = AXI4_BURST_INCR;
    rd.user     = '0;
    rd.allocate_payload();
    start_item(rd);
    finish_item(rd);
    if (rd.data.size() != 1) `uvm_fatal(get_type_name(), "Readback unexpected data size")
    if (rd.data[0] != wr1.data[0]) begin
      `uvm_fatal(get_type_name(), $sformatf("Readback mismatch exp=0x%0h got=0x%0h", wr1.data[0], rd.data[0]))
    end
  endtask

endclass

class axi4_error_write_seq #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends axi4_base_seq#(ADDR_W, DATA_W, ID_W, USER_W);

  rand logic [ADDR_W-1:0] addr = 32'h4000;
  rand logic [ID_W-1:0]   id   = '0;
  rand axi4_resp_e        expected_bresp = AXI4_RESP_DECERR;

  `uvm_object_param_utils(axi4_error_write_seq#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name = "axi4_error_write_seq");
    super.new(name);
  endfunction

  task body();
    axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) rd0;
    axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) wr_err;
    axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) rd;
    logic [DATA_W-1:0] baseline;

    // Capture baseline value (read path must not be error-injected for this test).
    rd0 = new("rd0");
    rd0.is_write = 1'b0;
    rd0.lock     = 1'b0;
    rd0.id       = id;
    rd0.addr     = addr;
    rd0.len      = 8'd0;
    rd0.size     = $clog2(DATA_W/8);
    rd0.burst    = AXI4_BURST_INCR;
    rd0.user     = '0;
    rd0.allocate_payload();
    start_item(rd0);
    finish_item(rd0);
    if (rd0.data.size() != 1) `uvm_fatal(get_type_name(), "Baseline read unexpected data size")
    baseline = rd0.data[0];

    // Error-injected write must not update memory.
    wr_err = new("wr_err");
    wr_err.is_write = 1'b1;
    wr_err.lock     = 1'b0;
    wr_err.id       = id;
    wr_err.addr     = addr;
    wr_err.len      = 8'd0;
    wr_err.size     = $clog2(DATA_W/8);
    wr_err.burst    = AXI4_BURST_INCR;
    wr_err.user     = '0;
    wr_err.allocate_payload();
    wr_err.data[0] = {$urandom(), $urandom()};
    if (DATA_W <= 32) wr_err.data[0] = $urandom();
    wr_err.strb[0] = '1;
    start_item(wr_err);
    finish_item(wr_err);
    if (wr_err.bresp != expected_bresp) begin
      `uvm_fatal(get_type_name(), $sformatf("Expected BRESP=%0d for error write, got %0d", expected_bresp, wr_err.bresp))
    end

    rd = new("rd");
    rd.is_write = 1'b0;
    rd.lock     = 1'b0;
    rd.id       = id;
    rd.addr     = addr;
    rd.len      = 8'd0;
    rd.size     = $clog2(DATA_W/8);
    rd.burst    = AXI4_BURST_INCR;
    rd.user     = '0;
    rd.allocate_payload();
    start_item(rd);
    finish_item(rd);
    if (rd.data.size() != 1) `uvm_fatal(get_type_name(), "Readback unexpected data size")
    if (rd.data[0] != baseline) begin
      `uvm_fatal(get_type_name(), $sformatf("Error-write readback mismatch exp=0x%0h got=0x%0h", baseline, rd.data[0]))
    end
  endtask

endclass

class axi4_error_read_seq #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends axi4_base_seq#(ADDR_W, DATA_W, ID_W, USER_W);

  rand logic [ADDR_W-1:0] addr = 32'h5000;
  rand logic [ID_W-1:0]   id   = '0;
  rand axi4_resp_e        expected_rresp = AXI4_RESP_DECERR;

  `uvm_object_param_utils(axi4_error_read_seq#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name = "axi4_error_read_seq");
    super.new(name);
  endfunction

  task body();
    axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) wr0;
    axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) rd_err;

    // Seed memory (writes should be non-error for this test).
    wr0 = new("wr0");
    wr0.is_write = 1'b1;
    wr0.lock     = 1'b0;
    wr0.id       = id;
    wr0.addr     = addr;
    wr0.len      = 8'd0;
    wr0.size     = $clog2(DATA_W/8);
    wr0.burst    = AXI4_BURST_INCR;
    wr0.user     = '0;
    wr0.allocate_payload();
    wr0.data[0] = {$urandom(), $urandom()};
    if (DATA_W <= 32) wr0.data[0] = $urandom();
    wr0.strb[0] = '1;
    start_item(wr0);
    finish_item(wr0);

    // Read should return injected error response.
    rd_err = new("rd_err");
    rd_err.is_write = 1'b0;
    rd_err.lock     = 1'b0;
    rd_err.id       = id;
    rd_err.addr     = addr;
    rd_err.len      = 8'd0;
    rd_err.size     = $clog2(DATA_W/8);
    rd_err.burst    = AXI4_BURST_INCR;
    rd_err.user     = '0;
    rd_err.allocate_payload();
    start_item(rd_err);
    finish_item(rd_err);
    if (rd_err.rresp.size() != 1) `uvm_fatal(get_type_name(), "Error read unexpected rresp size")
    if (rd_err.rresp[0] != expected_rresp) begin
      `uvm_fatal(get_type_name(), $sformatf("Expected RRESP=%0d for error read, got %0d", expected_rresp, rd_err.rresp[0]))
    end
  endtask

endclass

class axi4_incr_256b_seq #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends axi4_base_seq#(ADDR_W, DATA_W, ID_W, USER_W);

  rand int unsigned num_txns = 6;
  rand logic [ADDR_W-1:0] base_addr = 32'h6000;

  `uvm_object_param_utils(axi4_incr_256b_seq#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name = "axi4_incr_256b_seq");
    super.new(name);
  endfunction

  task body();
    for (int unsigned t = 0; t < num_txns; t++) begin
      axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) wr;
      axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) rd;
      int unsigned len;
      int unsigned size;

      size = $clog2(DATA_W/8);
      len  = $urandom_range(0, 255);

      wr = new($sformatf("wr_%0d", t));
      wr.is_write = 1'b1;
      wr.lock     = 1'b0;
      wr.id       = t[ID_W-1:0];
      wr.len      = len[7:0];
      wr.size     = size[2:0];
      wr.burst    = AXI4_BURST_INCR;
      wr.user     = '0;
      // Keep within a 4KB region
      begin
        longint unsigned bytes_per_beat;
        longint unsigned total_bytes;
        longint unsigned base4k;
        longint unsigned max_off;
        longint unsigned off;
        longint unsigned a;
        bytes_per_beat = longint'(1) << size;
        total_bytes    = (longint'(len) + 1) * bytes_per_beat;
        base4k         = (longint'(base_addr) & ~longint'(12'hFFF));
        max_off        = (total_bytes >= 4096) ? 0 : (4096 - total_bytes);
        off            = (max_off == 0) ? 0 : $urandom_range(0, int'(max_off));
        off            = (off / bytes_per_beat) * bytes_per_beat;
        a              = base4k + off;
        wr.addr        = a[ADDR_W-1:0];
      end
      wr.allocate_payload();
      for (int unsigned i = 0; i < wr.num_beats(); i++) begin
        wr.data[i] = {$urandom(), $urandom()};
        if (DATA_W <= 32) wr.data[i] = $urandom();
        wr.strb[i] = '1;
      end
      start_item(wr);
      finish_item(wr);

      rd = new($sformatf("rd_%0d", t));
      rd.is_write = 1'b0;
      rd.lock     = 1'b0;
      rd.id       = wr.id;
      rd.addr     = wr.addr;
      rd.len      = wr.len;
      rd.size     = wr.size;
      rd.burst    = wr.burst;
      rd.user     = wr.user;
      rd.allocate_payload();
      start_item(rd);
      finish_item(rd);
    end
  endtask

endclass

class axi4_exclusive_illegal_seq #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends axi4_base_seq#(ADDR_W, DATA_W, ID_W, USER_W);

  rand logic [ADDR_W-1:0] addr = 32'h7000;
  rand logic [ID_W-1:0]   id   = '0;

  `uvm_object_param_utils(axi4_exclusive_illegal_seq#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name = "axi4_exclusive_illegal_seq");
    super.new(name);
  endfunction

  task body();
    axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) exrd;
    axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) exwr;
    axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) rd;

    // Exclusive read with parameters exceeding the configured slave max-bytes
    // should return OKAY (i.e. treated as non-exclusive by the slave model).
    exrd = new("exrd");
    exrd.is_write = 1'b0;
    exrd.lock     = 1'b1;
    exrd.id       = id;
    exrd.addr     = addr;
    exrd.len      = 8'd15;
    exrd.size     = $clog2(DATA_W/8);
    exrd.burst    = AXI4_BURST_INCR;
    exrd.user     = '0;
    exrd.allocate_payload();
    start_item(exrd);
    finish_item(exrd);
    if (exrd.rresp.size() == 0) `uvm_fatal(get_type_name(), "Exclusive read illegal: missing rresp")
    if (exrd.rresp[0] != AXI4_RESP_OKAY) begin
      `uvm_fatal(get_type_name(), $sformatf("Exclusive read illegal expected OKAY, got %0d", exrd.rresp[0]))
    end

    // Exclusive write should return OKAY and must not update memory.
    exwr = new("exwr");
    exwr.is_write = 1'b1;
    exwr.lock     = 1'b1;
    exwr.id       = id;
    exwr.addr     = addr;
    exwr.len      = 8'd15;
    exwr.size     = $clog2(DATA_W/8);
    exwr.burst    = AXI4_BURST_INCR;
    exwr.user     = '0;
    exwr.allocate_payload();
    for (int unsigned i = 0; i < exwr.num_beats(); i++) begin
      exwr.data[i] = {$urandom(), $urandom()};
      if (DATA_W <= 32) exwr.data[i] = $urandom();
      exwr.strb[i] = '1;
    end
    start_item(exwr);
    finish_item(exwr);
    if (exwr.bresp != AXI4_RESP_OKAY) begin
      `uvm_fatal(get_type_name(), $sformatf("Exclusive write illegal expected OKAY, got %0d", exwr.bresp))
    end

    // Readback should be zeros (default slave init) as exclusive write should not commit.
    rd = new("rd");
    rd.is_write = 1'b0;
    rd.lock     = 1'b0;
    rd.id       = id;
    rd.addr     = addr;
    rd.len      = 8'd0;
    rd.size     = $clog2(DATA_W/8);
    rd.burst    = AXI4_BURST_INCR;
    rd.user     = '0;
    rd.allocate_payload();
    start_item(rd);
    finish_item(rd);
    if (rd.data.size() != 1) `uvm_fatal(get_type_name(), "Readback unexpected data size")
    if (rd.data[0] !== '0) begin
      `uvm_fatal(get_type_name(), $sformatf("Exclusive illegal write committed unexpectedly got=0x%0h", rd.data[0]))
    end
  endtask

endclass

class axi4_concurrent_rw_seq #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends axi4_base_seq#(ADDR_W, DATA_W, ID_W, USER_W);

  localparam int STRB_W = DATA_W/8;

  rand int unsigned num_prefill = 32;
  rand int unsigned num_mixed   = 200;
  rand int unsigned num_b_writes = 40;

  rand logic [ADDR_W-1:0] base_a = 32'hA000; // read-only region after prefill
  rand logic [ADDR_W-1:0] base_b = 32'hB000; // write-only during mixed; readback at end

  `uvm_object_param_utils(axi4_concurrent_rw_seq#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name = "axi4_concurrent_rw_seq");
    super.new(name);
  endfunction

  task body();
    axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) wrs_b[$];
    axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) rsp;
    int unsigned issued_total;
    int unsigned rsp_seen;
    bit send_done;
    bit rsp_drain_done;

    issued_total = 0;
    rsp_seen = 0;
    send_done = 0;
    rsp_drain_done = 0;

    fork
      begin : rsp_drain
        forever begin
          if (send_done && (rsp_seen >= issued_total)) break;
          get_response(rsp);
          if (rsp != null) rsp_seen++;
        end
        rsp_drain_done = 1'b1;
      end
    join_none

    // Prefill region A with deterministic single-beat writes.
    for (int unsigned i = 0; i < num_prefill; i++) begin
      axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) wr;
      wr = new($sformatf("prefill_wr_%0d", i));
      wr.is_write = 1'b1;
      wr.lock     = 1'b0;
      wr.id       = i[ID_W-1:0];
      wr.addr     = base_a + i*STRB_W;
      wr.len      = 8'd0;
      wr.size     = $clog2(STRB_W);
      wr.burst    = AXI4_BURST_INCR;
      wr.user     = '0;
      wr.allocate_payload();
      wr.data[0] = '0;
      wr.data[0][31:0] = 32'hA5A50000 + i;
      wr.strb[0] = '1;
      start_item(wr);
      finish_item(wr);
      issued_total++;
    end

    // Ensure prefill writes completed before issuing dependent reads.
    wait (rsp_seen >= issued_total);

    // Mixed traffic: reads from A and writes to B.
    for (int unsigned k = 0; k < num_mixed; k++) begin
      bit do_read;
      do_read = ($urandom_range(0, 1) == 0);
      if (do_read) begin
        axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) rd;
        int unsigned idx;
        idx = $urandom_range(0, (num_prefill == 0) ? 0 : (num_prefill-1));
        rd = new($sformatf("mix_rd_%0d", k));
        rd.is_write = 1'b0;
        rd.lock     = 1'b0;
        rd.id       = $urandom();
        rd.addr     = base_a + idx*STRB_W;
        rd.len      = 8'd0;
        rd.size     = $clog2(STRB_W);
        rd.burst    = AXI4_BURST_INCR;
        rd.user     = '0;
        rd.allocate_payload();
        start_item(rd);
        finish_item(rd);
        issued_total++;
      end else if (wrs_b.size() < num_b_writes) begin
        axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) wr;
        int unsigned len;
        len = $urandom_range(0, 15);
        wr = new($sformatf("mix_wr_%0d", k));
        wr.is_write = 1'b1;
        wr.lock     = 1'b0;
        wr.id       = $urandom();
        wr.len      = len[7:0];
        wr.size     = $clog2(STRB_W);
        wr.burst    = AXI4_BURST_INCR;
        wr.user     = '0;
        // Stay within 4KB window; spaced to reduce overlap.
        wr.addr     = base_b + (wrs_b.size() * 256);
        wr.allocate_payload();
        for (int unsigned i = 0; i < wr.num_beats(); i++) begin
          wr.data[i] = {$urandom(), $urandom()};
          if (DATA_W <= 32) wr.data[i] = $urandom();
          wr.strb[i] = '1;
        end
        start_item(wr);
        finish_item(wr);
        issued_total++;
        wrs_b.push_back(wr);
      end
    end

    // Ensure all writes to B have completed before readback.
    wait (rsp_seen >= issued_total);

    // Readback all B writes (same shapes/addresses).
    for (int unsigned t = 0; t < wrs_b.size(); t++) begin
      axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) rd;
      rd = new($sformatf("b_rd_%0d", t));
      rd.is_write = 1'b0;
      rd.lock     = 1'b0;
      rd.id       = $urandom();
      rd.addr     = wrs_b[t].addr;
      rd.len      = wrs_b[t].len;
      rd.size     = wrs_b[t].size;
      rd.burst    = wrs_b[t].burst;
      rd.user     = wrs_b[t].user;
      rd.allocate_payload();
      start_item(rd);
      finish_item(rd);
      issued_total++;
    end

    send_done = 1'b1;
    wait (rsp_seen >= issued_total);
    wait (rsp_drain_done);
  endtask

endclass

`ifdef VERILATOR
  /* verilator lint_on WIDTHTRUNC */
  /* verilator lint_on WIDTHEXPAND */
`endif

`endif // KVIPS_AXI4_SEQUENCES_SVH
