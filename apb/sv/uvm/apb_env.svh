//------------------------------------------------------------------------------
// APB Environment
//------------------------------------------------------------------------------
`ifndef KVIPS_APB_ENV_SVH
`define KVIPS_APB_ENV_SVH

class apb_env #(
  int ADDR_W = 32,
  int DATA_W = 32,
  int NSEL   = 1
) extends uvm_env;

  localparam string RID = "APB_ENV";

  apb_env_cfg#(ADDR_W, DATA_W, NSEL) cfg;

  apb_agent#(ADDR_W, DATA_W, NSEL) agents[$];
  uvm_analysis_port #(apb_item#(ADDR_W, DATA_W)) ap;

  `uvm_component_param_utils(apb_env#(ADDR_W, DATA_W, NSEL))

  function new(string name, uvm_component parent);
    super.new(name, parent);
    ap = new("ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(apb_env_cfg#(ADDR_W, DATA_W, NSEL))::get(this, "", "cfg", cfg)) begin
      `uvm_fatal(RID, "Missing env cfg in config DB (key: cfg)")
    end

    for (int i = 0; i < cfg.agent_cfgs.size(); i++) begin
      string an = $sformatf("agent_%0d", i);
      apb_agent#(ADDR_W, DATA_W, NSEL) a;
      a = apb_agent#(ADDR_W, DATA_W, NSEL)::type_id::create(an, this);
      uvm_config_db#(apb_agent_cfg#(ADDR_W, DATA_W, NSEL))::set(this, an, "cfg", cfg.agent_cfgs[i]);
      agents.push_back(a);
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    foreach (agents[i]) begin
      agents[i].monitor.ap.connect(ap);
    end
  endfunction

  function apb_sequencer#(ADDR_W, DATA_W) get_master_sequencer(int idx);
    if (idx >= agents.size()) return null;
    return agents[idx].sequencer;
  endfunction

endclass

`endif // KVIPS_APB_ENV_SVH

