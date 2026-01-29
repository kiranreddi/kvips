//------------------------------------------------------------------------------
// APB Scoreboard (optional)
//------------------------------------------------------------------------------
`ifndef KVIPS_APB_SCOREBOARD_SVH
`define KVIPS_APB_SCOREBOARD_SVH

class apb_scoreboard #(
  int ADDR_W = 32,
  int DATA_W = 32
) extends uvm_subscriber #(apb_item#(ADDR_W, DATA_W));

  localparam int STRB_W = (DATA_W/8);
  localparam string RID = "APB_SCB";

  bit enable = 1'b1;
  bit warn_uninit = 1'b0;

  // Word-addressed expected model.
  logic [DATA_W-1:0] exp_mem[longint unsigned];
  bit                exp_valid[longint unsigned];

  longint unsigned sum_wr;
  longint unsigned sum_rd;
  longint unsigned sum_err;
  longint unsigned sum_mismatch;

  `uvm_component_param_utils(apb_scoreboard#(ADDR_W, DATA_W))

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if ($test$plusargs("KVIPS_APB_SB_OFF")) enable = 1'b0;
    if ($test$plusargs("KVIPS_APB_SB_WARN_UNINIT")) warn_uninit = 1'b1;
    void'(uvm_config_db#(bit)::get(this, "", "enable", enable));
    void'(uvm_config_db#(bit)::get(this, "", "warn_uninit", warn_uninit));
    sum_wr = 0;
    sum_rd = 0;
    sum_err = 0;
    sum_mismatch = 0;
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

  function automatic void get_summary(
    output bit enabled,
    output longint unsigned wr_cnt,
    output longint unsigned rd_cnt,
    output longint unsigned err_cnt,
    output longint unsigned mismatch_cnt
  );
    enabled = enable;
    wr_cnt = sum_wr;
    rd_cnt = sum_rd;
    err_cnt = sum_err;
    mismatch_cnt = sum_mismatch;
  endfunction

  virtual function void write(apb_item#(ADDR_W, DATA_W) t);
    longint unsigned wi;
    logic [DATA_W-1:0] old_d;
    logic [DATA_W-1:0] exp_d;
    if (t == null) return;

    if (t.slverr) sum_err++;
    if (t.write) sum_wr++; else sum_rd++;
    if (!enable) return;

    wi = word_idx(t.addr);
    old_d = exp_mem.exists(wi) ? exp_mem[wi] : '0;

    if (t.write) begin
      if (t.slverr) return;
      exp_d = apply_strb(old_d, t.wdata, t.strb);
      exp_mem[wi] = exp_d;
      exp_valid[wi] = 1'b1;
    end else begin
      if (t.slverr) return;
      if (!(exp_valid.exists(wi)) || !exp_valid[wi]) begin
        if (warn_uninit) `uvm_warning(RID, $sformatf("Read from unwritten addr=0x%0h (treated as 0)", t.addr))
        exp_d = '0;
      end else begin
        exp_d = exp_mem[wi];
      end
      if (t.rdata !== exp_d) begin
        sum_mismatch++;
        `uvm_error(RID, $sformatf("READ MISMATCH addr=0x%0h exp=0x%0h got=0x%0h", t.addr, exp_d, t.rdata))
      end
    end
  endfunction

  function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info(RID,
      $sformatf("APB SB summary: enable=%0d wr=%0d rd=%0d err=%0d mismatch=%0d",
        enable, sum_wr, sum_rd, sum_err, sum_mismatch),
      UVM_LOW)
  endfunction

endclass

`endif // KVIPS_APB_SCOREBOARD_SVH

