//-----------------------------------------------------------------------------
// File: pcie_agent.sv
// Description: PCIe Agent - Combines Driver, Monitor, Sequencer
//
// Copyright (c) KVIPS Project
// SPDX-License-Identifier: Apache-2.0
//-----------------------------------------------------------------------------

class pcie_agent extends uvm_agent;
    `uvm_component_utils(pcie_agent)
    
    //-------------------------------------------------------------------------
    // Configuration
    //-------------------------------------------------------------------------
    
    pcie_cfg cfg;
    
    //-------------------------------------------------------------------------
    // Components
    //-------------------------------------------------------------------------
    
    pcie_driver    drv;
    pcie_monitor   mon;
    pcie_sequencer sqr;
    pcie_coverage  cov;
    
    //-------------------------------------------------------------------------
    // Analysis Ports (passthrough from monitor)
    //-------------------------------------------------------------------------
    
    uvm_analysis_port #(pcie_transaction) tlp_ap;
    uvm_analysis_port #(pcie_transaction) dllp_ap;
    uvm_analysis_port #(pcie_transaction) os_ap;
    uvm_analysis_port #(pcie_transaction) all_ap;
    
    //-------------------------------------------------------------------------
    // Methods
    //-------------------------------------------------------------------------
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db #(pcie_cfg)::get(this, "", "cfg", cfg))
            `uvm_fatal("CFG", "Failed to get pcie_cfg")
        
        // Create analysis ports
        tlp_ap = new("tlp_ap", this);
        dllp_ap = new("dllp_ap", this);
        os_ap = new("os_ap", this);
        all_ap = new("all_ap", this);
        
        // Always create monitor
        mon = pcie_monitor::type_id::create("mon", this);
        
        // Create coverage collector
        if (cfg.enable_coverage)
            cov = pcie_coverage::type_id::create("cov", this);
        
        // Create driver and sequencer for active agents
        if (is_active == UVM_ACTIVE && cfg.agent_mode != PCIE_MONITOR) begin
            drv = pcie_driver::type_id::create("drv", this);
            sqr = pcie_sequencer::type_id::create("sqr", this);
        end
        
        `uvm_info("AGENT", $sformatf("PCIe Agent built: mode=%s, active=%s",
                                     cfg.agent_mode.name(), 
                                     is_active == UVM_ACTIVE ? "yes" : "no"), UVM_LOW)
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect monitor analysis ports
        mon.tlp_ap.connect(tlp_ap);
        mon.dllp_ap.connect(dllp_ap);
        mon.os_ap.connect(os_ap);
        mon.all_ap.connect(all_ap);
        
        // Connect coverage
        if (cfg.enable_coverage && cov != null)
            mon.tlp_ap.connect(cov.analysis_export);
        
        // Connect driver to sequencer for active agents
        if (is_active == UVM_ACTIVE && drv != null && sqr != null) begin
            drv.seq_item_port.connect(sqr.seq_item_export);
        end
    endfunction
    
    // Helper: Get sequencer for starting sequences
    function pcie_sequencer get_sequencer();
        return sqr;
    endfunction
    
    // Helper: Check if link is up
    function bit is_link_up();
        if (drv != null)
            return drv.link_up;
        else if (mon != null)
            return mon.link_up;
        return 0;
    endfunction
    
    // Helper: Get current generation
    function pcie_gen_e get_current_gen();
        if (drv != null)
            return drv.current_gen;
        else if (mon != null)
            return mon.observed_gen;
        return PCIE_GEN1;
    endfunction
    
endclass

//-----------------------------------------------------------------------------
// PCIe Environment
//-----------------------------------------------------------------------------

typedef class pcie_virtual_sequencer;

class pcie_env extends uvm_env;
    `uvm_component_utils(pcie_env)
    
    //-------------------------------------------------------------------------
    // Configuration
    //-------------------------------------------------------------------------
    
    pcie_cfg rc_cfg;
    pcie_cfg ep_cfg;
    bit has_ep;              // Whether EP agent exists
    bit back_to_back_mode;   // B2B mode (no DUT)
    
    //-------------------------------------------------------------------------
    // Agents
    //-------------------------------------------------------------------------
    
    pcie_agent rc_agent;
    pcie_agent ep_agent;
    
    //-------------------------------------------------------------------------
    // Scoreboard
    //-------------------------------------------------------------------------
    
    pcie_scoreboard scb;
    
    //-------------------------------------------------------------------------
    // Virtual Sequencer
    //-------------------------------------------------------------------------
    
    pcie_virtual_sequencer vsqr;
    
    //-------------------------------------------------------------------------
    // Methods
    //-------------------------------------------------------------------------
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configurations
        if (!uvm_config_db #(pcie_cfg)::get(this, "", "rc_cfg", rc_cfg))
            `uvm_fatal("CFG", "Failed to get rc_cfg")
        
        // Check for EP configuration
        has_ep = uvm_config_db #(pcie_cfg)::get(this, "", "ep_cfg", ep_cfg);
        
        // Check mode
        void'(uvm_config_db #(bit)::get(this, "", "back_to_back_mode", back_to_back_mode));
        
        // Create RC agent
        uvm_config_db #(pcie_cfg)::set(this, "rc_agent*", "cfg", rc_cfg);
        rc_agent = pcie_agent::type_id::create("rc_agent", this);
        rc_agent.is_active = UVM_ACTIVE;
        
        // Create EP agent if configured
        if (has_ep) begin
            uvm_config_db #(pcie_cfg)::set(this, "ep_agent*", "cfg", ep_cfg);
            ep_agent = pcie_agent::type_id::create("ep_agent", this);
            ep_agent.is_active = UVM_ACTIVE;
        end
        
        // Create scoreboard
        if (rc_cfg.enable_scoreboard) begin
            uvm_config_db #(pcie_cfg)::set(this, "scb", "cfg", rc_cfg);
            scb = pcie_scoreboard::type_id::create("scb", this);
        end
        
        // Create virtual sequencer
        vsqr = pcie_virtual_sequencer::type_id::create("vsqr", this);
        
        `uvm_info("ENV", $sformatf("PCIe Environment built: has_ep=%0d, b2b=%0d",
                                   has_ep, back_to_back_mode), UVM_LOW)
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect virtual sequencer
        vsqr.rc_sqr = rc_agent.sqr;
        if (has_ep)
            vsqr.ep_sqr = ep_agent.sqr;
        
        // Connect agents to scoreboard
        if (scb != null) begin
            rc_agent.tlp_ap.connect(scb.rc_export);
            
            if (has_ep)
                ep_agent.tlp_ap.connect(scb.ep_export);
        end
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        // Wait for link up
        fork
            wait_for_link_up();
        join_none
    endtask
    
    virtual task wait_for_link_up();
        `uvm_info("ENV", "Waiting for link up...", UVM_LOW)
        
        fork
            wait(rc_agent.is_link_up());
            begin
                #100us;
                `uvm_error("ENV", "Link up timeout")
            end
        join_any
        disable fork;
        
        if (rc_agent.is_link_up())
            `uvm_info("ENV", $sformatf("Link is up! Gen%0d", rc_agent.get_current_gen() + 1), UVM_LOW)
    endtask
    
endclass

//-----------------------------------------------------------------------------
// Virtual Sequencer
//-----------------------------------------------------------------------------

class pcie_virtual_sequencer extends uvm_sequencer;
    `uvm_component_utils(pcie_virtual_sequencer)
    
    // Handles to actual sequencers
    pcie_sequencer rc_sqr;
    pcie_sequencer ep_sqr;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
endclass

//-----------------------------------------------------------------------------
// Virtual Sequence Base
//-----------------------------------------------------------------------------

class pcie_virtual_seq_base extends uvm_sequence;
    `uvm_object_utils(pcie_virtual_seq_base)
    `uvm_declare_p_sequencer(pcie_virtual_sequencer)
    
    function new(string name = "pcie_virtual_seq_base");
        super.new(name);
    endfunction
    
    // Start sequence on RC
    task start_rc_sequence(uvm_sequence_base seq);
        seq.start(p_sequencer.rc_sqr);
    endtask
    
    // Start sequence on EP
    task start_ep_sequence(uvm_sequence_base seq);
        if (p_sequencer.ep_sqr != null)
            seq.start(p_sequencer.ep_sqr);
        else
            `uvm_error("VSEQ", "No EP sequencer available")
    endtask
    
endclass

//-----------------------------------------------------------------------------
// Back-to-Back Virtual Sequence
//-----------------------------------------------------------------------------

class pcie_b2b_virtual_seq extends pcie_virtual_seq_base;
    `uvm_object_utils(pcie_b2b_virtual_seq)
    
    rand int unsigned num_rc_transactions;
    rand int unsigned num_ep_transactions;
    
    constraint c_defaults {
        num_rc_transactions inside {[10:100]};
        num_ep_transactions inside {[10:100]};
    }
    
    function new(string name = "pcie_b2b_virtual_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        pcie_mem_seq rc_mem_seq;
        pcie_mem_seq ep_mem_seq;
        
        `uvm_info("VSEQ", "Starting B2B virtual sequence", UVM_LOW)
        
        // Run RC and EP sequences in parallel
        fork
            begin : rc_thread
                rc_mem_seq = pcie_mem_seq::type_id::create("rc_mem_seq");
                rc_mem_seq.num_transactions = num_rc_transactions;
                rc_mem_seq.base_address = 64'h0000_0000_1000_0000;
                start_rc_sequence(rc_mem_seq);
            end
            
            begin : ep_thread
                if (p_sequencer.ep_sqr != null) begin
                    ep_mem_seq = pcie_mem_seq::type_id::create("ep_mem_seq");
                    ep_mem_seq.num_transactions = num_ep_transactions;
                    ep_mem_seq.base_address = 64'h0000_0000_2000_0000;
                    start_ep_sequence(ep_mem_seq);
                end
            end
        join
        
        `uvm_info("VSEQ", "B2B virtual sequence complete", UVM_LOW)
    endtask
    
endclass
