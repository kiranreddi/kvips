//------------------------------------------------------------------------------
// Demo TB Package
//------------------------------------------------------------------------------

package tb_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import pcie_types_pkg::*;
  import pcie_uvm_pkg::*;

  //============================================================================
  // PCIe B2B Base Test
  //============================================================================
  class pcie_b2b_base_test extends uvm_test;
    `uvm_component_utils(pcie_b2b_base_test)

    localparam int NUM_LANES   = 16;
    localparam int MAX_GEN     = 5;
    localparam int DATA_WIDTH  = 32;

    typedef virtual pcie_pipe_if #(NUM_LANES, MAX_GEN, DATA_WIDTH) pcie_vif_t;

    pcie_vif_t vif;

    pcie_cfg  cfg;
    pcie_agent rc_agent;
    pcie_agent ep_agent;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void post_build_cfg();
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      if (!uvm_config_db#(pcie_vif_t)::get(this, "", "vif", vif)) begin
        `uvm_fatal(get_type_name(), "Missing vif in config DB (key: vif)")
      end

      // Create configuration
      cfg = pcie_cfg::type_id::create("cfg");
      cfg.agent_mode = PCIE_RC;
      cfg.if_mode = PCIE_PIPE_MODE;
      cfg.target_gen = PCIE_GEN4;
      cfg.target_width = PCIE_X4;

      post_build_cfg();

      // Create RC agent
      uvm_config_db#(pcie_cfg)::set(this, "rc_agent*", "cfg", cfg);
      rc_agent = pcie_agent::type_id::create("rc_agent", this);

      // Create EP agent with different config
      begin
        pcie_cfg ep_cfg = pcie_cfg::type_id::create("ep_cfg");
        // In this example we keep a single active driver to avoid multi-driving
        // a single PIPE interface instance. The "EP" side is modeled as a
        // passive monitor-only agent.
        ep_cfg.agent_mode = PCIE_MONITOR;
        ep_cfg.if_mode = PCIE_PIPE_MODE;
        ep_cfg.target_gen = PCIE_GEN4;
        ep_cfg.target_width = PCIE_X4;
        uvm_config_db#(pcie_cfg)::set(this, "ep_agent*", "cfg", ep_cfg);
        ep_agent = pcie_agent::type_id::create("ep_agent", this);
      end
    endfunction

    function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
    endfunction
  endclass

  //============================================================================
  // PCIe B2B Smoke Test
  //============================================================================
  class pcie_b2b_smoke_test extends pcie_b2b_base_test;
    `uvm_component_utils(pcie_b2b_smoke_test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
      phase.raise_objection(this);

      `uvm_info("TEST", "Starting PCIe B2B smoke test", UVM_LOW)
      
      // Wait for reset
      #100ns;
      
      `uvm_info("TEST", "PCIe B2B smoke test completed", UVM_LOW)

      phase.drop_objection(this);
    endtask
  endclass

  //============================================================================
  // PCIe B2B Memory Test
  //============================================================================
  class pcie_b2b_mem_test extends pcie_b2b_base_test;
    `uvm_component_utils(pcie_b2b_mem_test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
      pcie_transaction req;
      phase.raise_objection(this);

      `uvm_info("TEST", "Starting PCIe B2B memory test", UVM_LOW)

      // Wait for reset
      #100ns;

      // Create a memory write transaction
      req = pcie_transaction::type_id::create("req");
      assert(req.randomize() with {
        trans_type == PCIE_TLP;
        tlp_type == TLP_MWR32;
        address == 64'h1000;
        length == 1;
      });

      `uvm_info("TEST", $sformatf("Created MWR32 transaction: addr=0x%h", req.address), UVM_LOW)

      // Drain time
      #1000ns;

      `uvm_info("TEST", "PCIe B2B memory test completed", UVM_LOW)

      phase.drop_objection(this);
    endtask
  endclass

endpackage
