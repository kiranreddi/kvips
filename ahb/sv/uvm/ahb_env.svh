//------------------------------------------------------------------------------
// AHB Environment
//------------------------------------------------------------------------------
`ifndef KVIPS_AHB_ENV_SVH
`define KVIPS_AHB_ENV_SVH

class ahb_env #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2,
  bit HAS_HMASTLOCK = 1'b0
) extends uvm_env;

  localparam string RID = "AHB_ENV";

  ahb_env_cfg#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK) cfg;

  ahb_agent#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK) agents[$];
  uvm_analysis_port #(ahb_item#(ADDR_W, DATA_W, HRESP_W)) ap;

  ahb_txn_logger#(ADDR_W, DATA_W, HRESP_W) logger;
  ahb_scoreboard#(ADDR_W, DATA_W, HRESP_W) sb;

  `uvm_component_param_utils(ahb_env#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK))

  function new(string name, uvm_component parent);
    super.new(name, parent);
    ap = new("ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(ahb_env_cfg#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK))::get(this, "", "cfg", cfg)) begin
      `uvm_fatal(RID, "Missing env cfg in config DB (key: cfg)")
    end

    for (int i = 0; i < cfg.agent_cfgs.size(); i++) begin
      string an = $sformatf("agent_%0d", i);
      ahb_agent#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK) a;
      a = ahb_agent#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK)::type_id::create(an, this);
      uvm_config_db#(ahb_agent_cfg#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK))::set(this, an, "cfg", cfg.agent_cfgs[i]);
      agents.push_back(a);
    end

    logger = ahb_txn_logger#(ADDR_W, DATA_W, HRESP_W)::type_id::create("logger", this);
    sb     = ahb_scoreboard#(ADDR_W, DATA_W, HRESP_W)::type_id::create("sb", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    foreach (agents[i]) begin
      agents[i].monitor.ap.connect(ap);
    end
    ap.connect(logger.analysis_export);
    ap.connect(sb.analysis_export);
  endfunction

  function ahb_sequencer#(ADDR_W, DATA_W, HRESP_W) get_master_sequencer(int idx);
    if (idx >= agents.size()) return null;
    return agents[idx].sequencer;
  endfunction

endclass

`endif // KVIPS_AHB_ENV_SVH
