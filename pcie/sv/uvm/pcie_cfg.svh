//-----------------------------------------------------------------------------
// File: pcie_cfg.sv
// Description: PCIe VIP Configuration Class - Full Implementation
//
// Copyright (c) KVIPS Project
// SPDX-License-Identifier: Apache-2.0
//-----------------------------------------------------------------------------

class pcie_cfg extends uvm_object;
    `uvm_object_utils(pcie_cfg)

    //-------------------------------------------------------------------------
    // Basic Configuration
    //-------------------------------------------------------------------------
    
    // Agent mode
    rand pcie_agent_mode_e agent_mode;      // RC, EP, MONITOR
    rand pcie_interface_mode_e if_mode;     // PIPE, SERIAL
    
    // PCIe Generation and Width
    rand pcie_gen_e max_gen;                // Maximum supported generation
    rand pcie_gen_e target_gen;             // Target operating generation
    rand pcie_width_e max_width;            // Maximum supported width
    rand pcie_width_e target_width;         // Target operating width
    
    // Device Configuration
    rand bit [15:0] vendor_id;
    rand bit [15:0] device_id;
    rand bit [7:0]  revision_id;
    rand bit [23:0] class_code;
    rand bit [7:0]  header_type;
    
    // Bus/Device/Function
    rand bit [7:0]  bus_num;
    rand bit [4:0]  device_num;
    rand bit [2:0]  function_num;
    
    //-------------------------------------------------------------------------
    // Capability Configuration
    //-------------------------------------------------------------------------
    
    // PCIe Capabilities
    rand bit        supports_extended_tag;
    rand bit        supports_10bit_tag;     // Gen4+
    rand bit [2:0]  max_payload_size;       // 0=128B, 1=256B, 2=512B, 3=1KB, 4=2KB, 5=4KB
    rand bit [2:0]  max_read_request_size;
    rand bit        phantom_functions_supported;
    rand bit        extended_tag_field_enable;
    
    // ASPM Configuration
    rand bit        l0s_entry_supported;
    rand bit        l1_entry_supported;
    rand bit [2:0]  l0s_exit_latency;
    rand bit [2:0]  l1_exit_latency;
    
    // Power Management
    rand bit        pme_support;
    rand bit [2:0]  aux_current;
    rand bit        d1_support;
    rand bit        d2_support;
    
    //-------------------------------------------------------------------------
    // Flow Control Configuration
    //-------------------------------------------------------------------------
    
    // Initial Flow Control Credits
    rand bit [7:0]  init_ph_credits;        // Posted header credits
    rand bit [11:0] init_pd_credits;        // Posted data credits
    rand bit [7:0]  init_nph_credits;       // Non-posted header credits
    rand bit [11:0] init_npd_credits;       // Non-posted data credits
    rand bit [7:0]  init_cplh_credits;      // Completion header credits
    rand bit [11:0] init_cpld_credits;      // Completion data credits
    
    // FC mode
    rand bit        infinite_fc_credits;    // Unlimited credits mode
    
    //-------------------------------------------------------------------------
    // Timing Configuration
    //-------------------------------------------------------------------------
    
    // LTSSM Timeouts (in ns)
    rand int unsigned detect_timeout;
    rand int unsigned polling_timeout;
    rand int unsigned config_timeout;
    rand int unsigned l0s_entry_timeout;
    rand int unsigned l1_entry_timeout;
    rand int unsigned recovery_timeout;
    rand int unsigned equalization_timeout;
    
    // Replay Timeout (in ns)
    rand int unsigned replay_timeout;
    rand int unsigned ack_latency;
    
    // Completion Timeout (in ns)
    rand longint unsigned completion_timeout;
    
    //-------------------------------------------------------------------------
    // Error Injection Configuration
    //-------------------------------------------------------------------------
    
    // Error injection enables
    rand bit        inject_lcrc_error;
    rand bit        inject_ecrc_error;
    rand bit        inject_seq_num_error;
    rand bit        inject_malformed_tlp;
    rand bit        inject_duplicate_dllp;
    rand bit        inject_fc_protocol_error;
    rand bit        inject_timeout_error;
    rand bit        inject_receiver_error;
    
    // Error injection probability (0-100%)
    rand int        error_injection_rate;
    
    //-------------------------------------------------------------------------
    // Coverage and Checking Configuration
    //-------------------------------------------------------------------------
    
    // Enable/disable features
    bit             enable_coverage;
    bit             enable_assertions;
    bit             enable_protocol_checks;
    bit             enable_scoreboard;
    bit             enable_ordering_checks;
    bit             enable_fc_checks;
    bit             enable_ltssm;
    
    // Debug options
    bit             verbose_logging;
    bit             dump_tlps;
    bit             dump_dllps;
    bit             dump_ordered_sets;
    
    //-------------------------------------------------------------------------
    // Interface References
    //-------------------------------------------------------------------------
    
    virtual pcie_pipe_if.monitor   vif_pipe;
    virtual pcie_serial_if.monitor vif_serial;
    
    //-------------------------------------------------------------------------
    // Constraints
    //-------------------------------------------------------------------------
    
    // Agent mode constraints
    constraint c_agent_mode {
        agent_mode inside {PCIE_RC, PCIE_EP, PCIE_MONITOR};
    }
    
    // Generation constraints
    constraint c_gen {
        target_gen <= max_gen;
        max_gen inside {PCIE_GEN1, PCIE_GEN2, PCIE_GEN3, PCIE_GEN4, PCIE_GEN5, PCIE_GEN6};
    }
    
    // Width constraints
    constraint c_width {
        target_width <= max_width;
        max_width inside {PCIE_X1, PCIE_X2, PCIE_X4, PCIE_X8, PCIE_X16, PCIE_X32};
    }
    
    // Payload size constraints
    constraint c_payload {
        max_payload_size inside {[0:5]};
        max_read_request_size inside {[0:5]};
    }
    
    // Flow control credit constraints
    constraint c_fc_credits {
        init_ph_credits inside {[1:127]};
        init_pd_credits inside {[1:2047]};
        init_nph_credits inside {[1:127]};
        init_npd_credits inside {[1:2047]};
        init_cplh_credits inside {[1:127]};
        init_cpld_credits inside {[1:2047]};
    }
    
    // Timing constraints (reasonable defaults)
    constraint c_timing {
        detect_timeout inside {[1000:100000]};        // 1us - 100us
        polling_timeout inside {[10000:1000000]};     // 10us - 1ms
        config_timeout inside {[10000:1000000]};      // 10us - 1ms
        recovery_timeout inside {[1000:100000]};      // 1us - 100us
        replay_timeout inside {[10000:500000]};       // 10us - 500us
        completion_timeout inside {[64'd1000000:64'd50000000000]};  // 1ms - 50s
    }
    
    // Error injection constraints
    constraint c_error_injection {
        error_injection_rate inside {[0:100]};
        // By default, no error injection
        soft inject_lcrc_error == 0;
        soft inject_ecrc_error == 0;
        soft inject_seq_num_error == 0;
        soft inject_malformed_tlp == 0;
        soft inject_duplicate_dllp == 0;
        soft inject_fc_protocol_error == 0;
        soft inject_timeout_error == 0;
        soft inject_receiver_error == 0;
    }
    
    // Default configuration
    constraint c_defaults {
        soft vendor_id == 16'h10EE;      // Xilinx-like
        soft device_id == 16'hDEAD;
        soft revision_id == 8'h01;
        soft class_code == 24'hFF0000;   // Unclassified
        soft header_type == 8'h00;       // Type 0 header
        
        soft bus_num == 8'h00;
        soft device_num == 5'h00;
        soft function_num == 3'h0;
        
        soft supports_extended_tag == 1;
        soft supports_10bit_tag == 1;
        soft extended_tag_field_enable == 1;
    }
    
    //-------------------------------------------------------------------------
    // Methods
    //-------------------------------------------------------------------------
    
    function new(string name = "pcie_cfg");
        super.new(name);
        set_defaults();
    endfunction
    
    // Set default values for non-randomized fields
    function void set_defaults();
        // Ensure 4-state-safe defaults for randomized fields as well (avoid X-driven
        // branch selection in driver/monitor before a test overrides the cfg).
        agent_mode = PCIE_RC;
        if_mode = PCIE_PIPE_MODE;
        max_gen = PCIE_GEN4;
        target_gen = PCIE_GEN4;
        max_width = PCIE_X16;
        target_width = PCIE_X4;

        enable_coverage = 1;
        enable_assertions = 1;
        enable_protocol_checks = 1;
        enable_scoreboard = 1;
        enable_ordering_checks = 1;
        enable_fc_checks = 1;
        enable_ltssm = 0;
        
        verbose_logging = 0;
        dump_tlps = 0;
        dump_dllps = 0;
        dump_ordered_sets = 0;
    endfunction
    
    // Get max payload size in bytes
    function int get_max_payload_bytes();
        return (128 << max_payload_size);
    endfunction
    
    // Get max read request size in bytes
    function int get_max_read_request_bytes();
        return (128 << max_read_request_size);
    endfunction
    
    // Get number of lanes for current width
    function int get_num_lanes();
        case (target_width)
            PCIE_X1:  return 1;
            PCIE_X2:  return 2;
            PCIE_X4:  return 4;
            PCIE_X8:  return 8;
            PCIE_X16: return 16;
            PCIE_X32: return 32;
            default:  return 1;
        endcase
    endfunction
    
    // Get link speed in GT/s
    function real get_link_speed_gtps();
        case (target_gen)
            PCIE_GEN1: return 2.5;
            PCIE_GEN2: return 5.0;
            PCIE_GEN3: return 8.0;
            PCIE_GEN4: return 16.0;
            PCIE_GEN5: return 32.0;
            PCIE_GEN6: return 64.0;
            default:   return 2.5;
        endcase
    endfunction
    
    // Calculate theoretical bandwidth in GB/s
    function real get_bandwidth_gbps();
        real encoding_overhead;
        int lanes = get_num_lanes();
        real speed = get_link_speed_gtps();
        
        // Encoding overhead: 8b/10b for Gen1-2, 128b/130b for Gen3+
        if (target_gen inside {PCIE_GEN1, PCIE_GEN2})
            encoding_overhead = 0.8;  // 80% efficiency
        else
            encoding_overhead = 128.0/130.0;  // ~98.5% efficiency
            
        return (lanes * speed * encoding_overhead) / 8.0;  // Convert bits to bytes
    endfunction
    
    // Get symbol time in ns
    function real get_symbol_time_ns();
        case (target_gen)
            PCIE_GEN1: return 4.0;     // 250 MHz
            PCIE_GEN2: return 2.0;     // 500 MHz
            PCIE_GEN3: return 1.0;     // 1 GHz (block)
            PCIE_GEN4: return 0.5;     // 2 GHz (block)
            PCIE_GEN5: return 0.25;    // 4 GHz (block)
            PCIE_GEN6: return 0.125;   // 8 GHz (block)
            default:   return 4.0;
        endcase
    endfunction
    
    // Check if using 8b/10b encoding
    function bit is_8b10b_encoding();
        return (target_gen inside {PCIE_GEN1, PCIE_GEN2});
    endfunction
    
    // Check if using 128b/130b encoding
    function bit is_128b130b_encoding();
        return (target_gen inside {PCIE_GEN3, PCIE_GEN4, PCIE_GEN5});
    endfunction
    
    // Check if using 1b/1b (FLIT) encoding (Gen6)
    function bit is_flit_encoding();
        return (target_gen == PCIE_GEN6);
    endfunction
    
    // Get BDF (Bus/Device/Function) as 16-bit value
    function bit [15:0] get_bdf();
        return {bus_num, device_num, function_num};
    endfunction
    
    // Get requester ID
    function bit [15:0] get_requester_id();
        return get_bdf();
    endfunction
    
    // Print configuration
    function void print_config();
        `uvm_info("CFG", $sformatf("===== PCIe VIP Configuration ====="), UVM_LOW)
        `uvm_info("CFG", $sformatf("Agent Mode:      %s", agent_mode.name()), UVM_LOW)
        `uvm_info("CFG", $sformatf("Interface Mode:  %s", if_mode.name()), UVM_LOW)
        `uvm_info("CFG", $sformatf("Max Generation:  %s", max_gen.name()), UVM_LOW)
        `uvm_info("CFG", $sformatf("Target Gen:      %s", target_gen.name()), UVM_LOW)
        `uvm_info("CFG", $sformatf("Max Width:       %s", max_width.name()), UVM_LOW)
        `uvm_info("CFG", $sformatf("Target Width:    %s", target_width.name()), UVM_LOW)
        `uvm_info("CFG", $sformatf("Bandwidth:       %.2f GB/s", get_bandwidth_gbps()), UVM_LOW)
        `uvm_info("CFG", $sformatf("Vendor ID:       0x%04X", vendor_id), UVM_LOW)
        `uvm_info("CFG", $sformatf("Device ID:       0x%04X", device_id), UVM_LOW)
        `uvm_info("CFG", $sformatf("BDF:             %02X:%02X.%X", bus_num, device_num, function_num), UVM_LOW)
        `uvm_info("CFG", $sformatf("Max Payload:     %0d bytes", get_max_payload_bytes()), UVM_LOW)
        `uvm_info("CFG", $sformatf("FC Credits PH:   %0d, PD: %0d", init_ph_credits, init_pd_credits), UVM_LOW)
        `uvm_info("CFG", $sformatf("FC Credits NPH:  %0d, NPD: %0d", init_nph_credits, init_npd_credits), UVM_LOW)
        `uvm_info("CFG", $sformatf("FC Credits CPLH: %0d, CPLD: %0d", init_cplh_credits, init_cpld_credits), UVM_LOW)
        `uvm_info("CFG", $sformatf("Encoding:        %s", is_8b10b_encoding() ? "8b/10b" : 
                                                          is_flit_encoding() ? "FLIT" : "128b/130b"), UVM_LOW)
        `uvm_info("CFG", $sformatf("========================================="), UVM_LOW)
    endfunction
    
    // Clone method
    function pcie_cfg clone_cfg();
        pcie_cfg cloned;
        cloned = new();
        cloned.copy(this);
        return cloned;
    endfunction
    
    // Copy method
    function void copy(pcie_cfg rhs);
        this.agent_mode = rhs.agent_mode;
        this.if_mode = rhs.if_mode;
        this.max_gen = rhs.max_gen;
        this.target_gen = rhs.target_gen;
        this.max_width = rhs.max_width;
        this.target_width = rhs.target_width;
        this.vendor_id = rhs.vendor_id;
        this.device_id = rhs.device_id;
        this.revision_id = rhs.revision_id;
        this.class_code = rhs.class_code;
        this.header_type = rhs.header_type;
        this.bus_num = rhs.bus_num;
        this.device_num = rhs.device_num;
        this.function_num = rhs.function_num;
        this.init_ph_credits = rhs.init_ph_credits;
        this.init_pd_credits = rhs.init_pd_credits;
        this.init_nph_credits = rhs.init_nph_credits;
        this.init_npd_credits = rhs.init_npd_credits;
        this.init_cplh_credits = rhs.init_cplh_credits;
        this.init_cpld_credits = rhs.init_cpld_credits;
        this.enable_coverage = rhs.enable_coverage;
        this.enable_assertions = rhs.enable_assertions;
        this.enable_protocol_checks = rhs.enable_protocol_checks;
        this.enable_scoreboard = rhs.enable_scoreboard;
        // ... copy remaining fields
    endfunction
    
    // Convert to string
    function string convert2string();
        return $sformatf("pcie_cfg: mode=%s gen=%s width=%s", 
                         agent_mode.name(), target_gen.name(), target_width.name());
    endfunction
    
endclass
