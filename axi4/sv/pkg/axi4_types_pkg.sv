//------------------------------------------------------------------------------
// AXI4 Types Package
//------------------------------------------------------------------------------
// Common, simulator-agnostic types/enums for AXI4 (full).
//------------------------------------------------------------------------------

`ifndef KVIPS_AXI4_TYPES_PKG_SV
`define KVIPS_AXI4_TYPES_PKG_SV

package axi4_types_pkg;

  typedef enum logic [1:0] {
    AXI4_BURST_FIXED = 2'b00,
    AXI4_BURST_INCR  = 2'b01,
    AXI4_BURST_WRAP  = 2'b10
  } axi4_burst_e;

  typedef enum logic [1:0] {
    AXI4_RESP_OKAY   = 2'b00,
    AXI4_RESP_EXOKAY = 2'b01,
    AXI4_RESP_SLVERR = 2'b10,
    AXI4_RESP_DECERR = 2'b11
  } axi4_resp_e;

  // Utility helpers (protocol-level)
  function automatic int unsigned axi4_size_to_bytes(input int unsigned size);
    return (1 << size);
  endfunction

  function automatic longint unsigned axi4_len_to_beats(input int unsigned len);
    return longint'(len) + 1;
  endfunction

  function automatic longint unsigned axi4_total_bytes(input int unsigned size, input int unsigned len);
    return axi4_len_to_beats(len) * longint'(axi4_size_to_bytes(size));
  endfunction

  function automatic bit axi4_wrap_len_legal(input int unsigned len);
    // AXI4: WRAP burst length must be 2,4,8,16 beats => LEN = 1,3,7,15.
    return (len == 1) || (len == 3) || (len == 7) || (len == 15);
  endfunction

  function automatic bit axi4_wrap_addr_aligned(
    input longint unsigned start_addr,
    input int unsigned     size,
    input int unsigned     len
  );
    longint unsigned container;
    container = axi4_total_bytes(size, len);
    if (container == 0) return 1'b0;
    return ((start_addr % container) == 0);
  endfunction

  function automatic bit axi4_crosses_4kb(
    input longint unsigned start_addr,
    input int unsigned     size,
    input int unsigned     len
  );
    longint unsigned offset;
    longint unsigned total;
    offset = start_addr & 12'hFFF;
    total  = axi4_total_bytes(size, len);
    return ((offset + total) > 4096);
  endfunction

  function automatic int unsigned axi4_bytes_per_beat(input int unsigned data_w);
    return (data_w / 8);
  endfunction

  // Beat address calculation for AXI bursts (FIXED/INCR/WRAP).
  // - start_addr: byte address
  // - size:       AXI size encoding (bytes/beat = 2**size)
  // - len:        AXI len encoding (beats-1)
  // - beat:       0..len
  function automatic longint unsigned axi4_beat_addr(
    input longint unsigned start_addr,
    input int unsigned     size,
    input int unsigned     len,
    input axi4_burst_e     burst,
    input int unsigned     beat
  );
    longint unsigned bytes_per_beat;
    longint unsigned burst_bytes;
    longint unsigned base;
    longint unsigned offset;
    bytes_per_beat = longint'(1) << size;
    burst_bytes    = bytes_per_beat * (longint'(len) + 1);

    case (burst)
      AXI4_BURST_FIXED: axi4_beat_addr = start_addr;
      AXI4_BURST_INCR:  axi4_beat_addr = start_addr + longint'(beat) * bytes_per_beat;
      AXI4_BURST_WRAP: begin
        if (burst_bytes == 0) begin
          axi4_beat_addr = start_addr;
        end else begin
          base   = (start_addr / burst_bytes) * burst_bytes;
          offset = (start_addr - base) + longint'(beat) * bytes_per_beat;
          offset = offset % burst_bytes;
          axi4_beat_addr = base + offset;
        end
      end
      default: axi4_beat_addr = start_addr + longint'(beat) * bytes_per_beat;
    endcase
  endfunction

endpackage

`endif // KVIPS_AXI4_TYPES_PKG_SV
