//------------------------------------------------------------------------------
// AXI4 Environment
//------------------------------------------------------------------------------

`ifndef KVIPS_AXI4_ENV_SVH
`define KVIPS_AXI4_ENV_SVH

class axi4_env #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends uvm_env;

  localparam string RID = "AXI4_ENV";

  axi4_env_cfg#(ADDR_W, DATA_W, ID_W, USER_W) cfg;

  axi4_agent#(ADDR_W, DATA_W, ID_W, USER_W) agents[$];
  uvm_analysis_port #(axi4_item#(ADDR_W, DATA_W, ID_W, USER_W)) ap;

  `uvm_component_param_utils(axi4_env#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name, uvm_component parent);
    super.new(name, parent);
    ap = new("ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(axi4_env_cfg#(ADDR_W, DATA_W, ID_W, USER_W))::get(this, "", "cfg", cfg)) begin
      `uvm_fatal(RID, "Missing env cfg in config DB (key: cfg)")
    end

    for (int i = 0; i < cfg.agent_cfgs.size(); i++) begin
      string an = $sformatf("agent_%0d", i);
      axi4_agent#(ADDR_W, DATA_W, ID_W, USER_W) a;
      a = axi4_agent#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create(an, this);
      uvm_config_db#(axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W))::set(this, an, "cfg", cfg.agent_cfgs[i]);
      agents.push_back(a);
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    foreach (agents[i]) begin
      if (agents[i].monitor != null) begin
        agents[i].monitor.ap.connect(ap);
      end
    end
  endfunction

  function axi4_sequencer#(ADDR_W, DATA_W, ID_W, USER_W) get_master_sequencer(int idx);
    if (idx >= agents.size()) return null;
    return agents[idx].sequencer;
  endfunction

endclass

`endif // KVIPS_AXI4_ENV_SVH
