//-----------------------------------------------------------------------------
// File: pcie_monitor.sv
// Description: PCIe Monitor - Full Implementation
//
// Copyright (c) KVIPS Project
// SPDX-License-Identifier: Apache-2.0
//-----------------------------------------------------------------------------

class pcie_monitor extends uvm_monitor;
    `uvm_component_utils(pcie_monitor)
    
    //-------------------------------------------------------------------------
    // Configuration and Interfaces
    //-------------------------------------------------------------------------
    
    pcie_cfg cfg;
    virtual pcie_pipe_if.monitor vif_pipe;
    virtual pcie_serial_if.monitor vif_serial;
    
    //-------------------------------------------------------------------------
    // Analysis Ports
    //-------------------------------------------------------------------------
    
    uvm_analysis_port #(pcie_transaction) tlp_ap;
    uvm_analysis_port #(pcie_transaction) dllp_ap;
    uvm_analysis_port #(pcie_transaction) os_ap;
    uvm_analysis_port #(pcie_transaction) all_ap;  // All transactions
    
    //-------------------------------------------------------------------------
    // State Variables
    //-------------------------------------------------------------------------
    
    // LTSSM tracking
    ltssm_state_e observed_ltssm_state;
    bit link_up;
    pcie_gen_e observed_gen;
    pcie_width_e observed_width;
    
    // Sequence number tracking
    bit [11:0] expected_tx_seq_num;
    bit [11:0] expected_rx_seq_num;
    
    // Statistics
    int unsigned tlp_count;
    int unsigned dllp_count;
    int unsigned os_count;
    int unsigned error_count;
    
    // Error tracking
    bit [31:0] lcrc_errors;
    bit [31:0] seq_num_errors;
    bit [31:0] malformed_tlp_errors;
    
    //-------------------------------------------------------------------------
    // Observed values for coverage
    //-------------------------------------------------------------------------
    tlp_type_e observed_tlp_type;
    dllp_type_e observed_dllp_type;
    bit [2:0] observed_tc;
    bit [9:0] observed_length;
    bit observed_td;

    //-------------------------------------------------------------------------
    // Coverage Groups
    //-------------------------------------------------------------------------
    
    covergroup cg_tlp_types;
        option.per_instance = 1;
        
        cp_tlp_type: coverpoint observed_tlp_type {
            bins mem_read32  = {TLP_MRD32};
            bins mem_read64  = {TLP_MRD64};
            bins mem_write32 = {TLP_MWR32};
            bins mem_write64 = {TLP_MWR64};
            bins cfg_read0   = {TLP_CFGRD0};
            bins cfg_read1   = {TLP_CFGRD1};
            bins cfg_write0  = {TLP_CFGWR0};
            bins cfg_write1  = {TLP_CFGWR1};
            bins io_read     = {TLP_IORD};
            bins io_write    = {TLP_IOWR};
            bins cpl         = {TLP_CPL};
            bins cpld        = {TLP_CPLD};
            bins msg         = {TLP_MSG};
            bins msgd        = {TLP_MSGD};
        }
        
        cp_traffic_class: coverpoint observed_tc {
            bins tc[] = {[0:7]};
        }
        
        cp_length: coverpoint observed_length {
            bins len_1   = {1};
            bins len_2_4 = {[2:4]};
            bins len_5_16 = {[5:16]};
            bins len_17_64 = {[17:64]};
            bins len_65_256 = {[65:256]};
            bins len_257_1024 = {[257:1023], [0:0]};  // 0 means 1024
        }
        
        cp_has_ecrc: coverpoint observed_td {
            bins no_ecrc = {0};
            bins has_ecrc = {1};
        }
        
        cross_type_tc: cross cp_tlp_type, cp_traffic_class;
        cross_type_len: cross cp_tlp_type, cp_length;
    endgroup
    
    covergroup cg_dllp_types;
        option.per_instance = 1;
        
        cp_dllp_type: coverpoint observed_dllp_type {
            bins ack = {DLLP_ACK};
            bins nak = {DLLP_NAK};
            bins initfc1_p = {DLLP_INITFC1_P};
            bins initfc1_np = {DLLP_INITFC1_NP};
            bins initfc1_cpl = {DLLP_INITFC1_CPL};
            bins initfc2_p = {DLLP_INITFC2_P};
            bins initfc2_np = {DLLP_INITFC2_NP};
            bins initfc2_cpl = {DLLP_INITFC2_CPL};
            bins updatefc_p = {DLLP_UPDATEFC_P};
            bins updatefc_np = {DLLP_UPDATEFC_NP};
            bins updatefc_cpl = {DLLP_UPDATEFC_CPL};
            bins pm_l1 = {DLLP_PM_ENTER_L1};
            bins pm_l23 = {DLLP_PM_ENTER_L23};
        }
    endgroup
    
    covergroup cg_ltssm_states;
        option.per_instance = 1;
        
        cp_ltssm_state: coverpoint observed_ltssm_state {
            bins detect_quiet = {LTSSM_DETECT_QUIET};
            bins detect_active = {LTSSM_DETECT_ACTIVE};
            bins polling_active = {LTSSM_POLLING_ACTIVE};
            bins polling_config = {LTSSM_POLLING_CONFIGURATION};
            bins config_states[] = {LTSSM_CONFIG_LINKWIDTH_START, LTSSM_CONFIG_COMPLETE};
            bins l0 = {LTSSM_L0};
            bins l0s[] = {LTSSM_L0S_ENTRY, LTSSM_L0S_IDLE, LTSSM_L0S_FTS};
            bins l1[] = {LTSSM_L1_ENTRY, LTSSM_L1_IDLE};
            bins l2[] = {LTSSM_L2_IDLE, LTSSM_L2_TRANSMIT_WAKE};
            bins recovery = {LTSSM_RECOVERY_RCVRLOCK, LTSSM_RECOVERY_SPEED};
            bins hot_reset = {LTSSM_HOT_RESET};
            bins disabled = {LTSSM_DISABLED};
            bins loopback[] = {LTSSM_LOOPBACK_ENTRY, LTSSM_LOOPBACK_ACTIVE, LTSSM_LOOPBACK_EXIT};
        }
        
        cp_link_width: coverpoint observed_width {
            bins x1 = {PCIE_X1};
            bins x2 = {PCIE_X2};
            bins x4 = {PCIE_X4};
            bins x8 = {PCIE_X8};
            bins x16 = {PCIE_X16};
            bins x32 = {PCIE_X32};
        }
        
        cp_link_gen: coverpoint observed_gen {
            bins gen1 = {PCIE_GEN1};
            bins gen2 = {PCIE_GEN2};
            bins gen3 = {PCIE_GEN3};
            bins gen4 = {PCIE_GEN4};
            bins gen5 = {PCIE_GEN5};
            bins gen6 = {PCIE_GEN6};
        }
        
        cross_gen_width: cross cp_link_gen, cp_link_width;
    endgroup
    
    //-------------------------------------------------------------------------
    // Methods
    //-------------------------------------------------------------------------
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        
        // Create coverage groups
        cg_tlp_types = new();
        cg_dllp_types = new();
        cg_ltssm_states = new();
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create analysis ports
        tlp_ap = new("tlp_ap", this);
        dllp_ap = new("dllp_ap", this);
        os_ap = new("os_ap", this);
        all_ap = new("all_ap", this);
        
        // Get configuration
        if (!uvm_config_db #(pcie_cfg)::get(this, "", "cfg", cfg))
            `uvm_fatal("CFG", "Failed to get pcie_cfg")
        
        // Get virtual interface
        if (cfg.if_mode == PCIE_PIPE_MODE) begin
            if (!uvm_config_db #(virtual pcie_pipe_if.monitor)::get(this, "", "vif_pipe", vif_pipe))
                `uvm_fatal("VIF", "Failed to get pcie_pipe_if")
        end else begin
            if (!uvm_config_db #(virtual pcie_serial_if.monitor)::get(this, "", "vif_serial", vif_serial))
                `uvm_fatal("VIF", "Failed to get pcie_serial_if")
        end
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        // Initialize state
        reset_monitor();
        
        // Wait for reset
        wait_for_reset_done();
        
        // Fork monitoring processes
        fork
            monitor_tlps();
            monitor_dllps();
            monitor_ordered_sets();
            monitor_ltssm();
            monitor_errors();
        join
    endtask
    
    virtual function void report_phase(uvm_phase phase);
        `uvm_info("MON", "===== Monitor Statistics =====", UVM_LOW)
        `uvm_info("MON", $sformatf("TLPs observed:  %0d", tlp_count), UVM_LOW)
        `uvm_info("MON", $sformatf("DLLPs observed: %0d", dllp_count), UVM_LOW)
        `uvm_info("MON", $sformatf("Ordered sets:   %0d", os_count), UVM_LOW)
        `uvm_info("MON", $sformatf("Errors:         %0d", error_count), UVM_LOW)
        `uvm_info("MON", $sformatf("  LCRC errors:      %0d", lcrc_errors), UVM_LOW)
        `uvm_info("MON", $sformatf("  Seq num errors:   %0d", seq_num_errors), UVM_LOW)
        `uvm_info("MON", $sformatf("  Malformed TLPs:   %0d", malformed_tlp_errors), UVM_LOW)
        `uvm_info("MON", "================================", UVM_LOW)
    endfunction
    
    //-------------------------------------------------------------------------
    // Reset Handling
    //-------------------------------------------------------------------------
    
    virtual task reset_monitor();
        observed_ltssm_state = LTSSM_DETECT_QUIET;
        link_up = 0;
        observed_gen = PCIE_GEN1;
        observed_width = cfg.target_width;
        expected_tx_seq_num = 0;
        expected_rx_seq_num = 0;
        tlp_count = 0;
        dllp_count = 0;
        os_count = 0;
        error_count = 0;
        lcrc_errors = 0;
        seq_num_errors = 0;
        malformed_tlp_errors = 0;
    endtask
    
    virtual task wait_for_reset_done();
        if (cfg.if_mode == PCIE_PIPE_MODE) begin
            @(posedge vif_pipe.reset_n);
            repeat(10) @(vif_pipe.mon_cb);
        end else begin
            @(posedge vif_serial.refclk);
            repeat(100) @(posedge vif_serial.refclk);
        end
    endtask
    
    //-------------------------------------------------------------------------
    // TLP Monitoring
    //-------------------------------------------------------------------------
    
    virtual task monitor_tlps();
        forever begin
            pcie_transaction tr;
            
            if (cfg.if_mode == PCIE_PIPE_MODE)
                capture_tlp_pipe(tr);
            else
                capture_tlp_serial(tr);
            
            if (tr != null) begin
                // Update coverage
                observed_tlp_type = tr.tlp_type;
                observed_tc = tr.tc;
                observed_length = tr.length;
                observed_td = tr.td;
                if (cfg.enable_coverage)
                    cg_tlp_types.sample();
                
                // Check TLP validity
                if (cfg.enable_protocol_checks)
                    check_tlp_validity(tr);
                
                // Send to analysis port
                tlp_ap.write(tr);
                all_ap.write(tr);
                tlp_count++;
                
                if (cfg.dump_tlps)
                    tr.print_transaction("RX");
            end
        end
    endtask
    
    virtual task capture_tlp_pipe(output pcie_transaction tr);
        bit [31:0] packet[$];
        bit [11:0] seq_num;
        bit [31:0] received_lcrc;
        bit [31:0] calculated_lcrc;
        bit in_packet = 0;
        int byte_count = 0;
        bit [31:0] current_dw;
        
        // Wait for STP (Start TLP)
        forever begin
            @(vif_pipe.mon_cb);
            
            // Check for STP on lane 0
            if (vif_pipe.mon_cb.RxDataK[0] && vif_pipe.mon_cb.RxData[0] == 8'hFB) begin
                in_packet = 1;
                packet.delete();
                break;
            end
        end
        
        // Capture sequence number (2 bytes)
        @(vif_pipe.mon_cb);
        seq_num[7:0] = vif_pipe.mon_cb.RxData[0];
        seq_num[11:8] = vif_pipe.mon_cb.RxData[1][3:0];
        
        // Capture TLP data until END
        while (in_packet) begin
            @(vif_pipe.mon_cb);
            
            // Check for END
            if (vif_pipe.mon_cb.RxDataK[0] && vif_pipe.mon_cb.RxData[0] == 8'hFD) begin
                in_packet = 0;
            end else begin
                // Assemble 32-bit word from lanes
                current_dw = 0;
                for (int b = 0; b < 4 && b < cfg.get_num_lanes(); b++) begin
                    current_dw[b*8 +: 8] = vif_pipe.mon_cb.RxData[b];
                end
                packet.push_back(current_dw);
            end
        end
        
        // Need at least header (3 DW) + LCRC (1 DW)
        if (packet.size() < 4) begin
            `uvm_error("MON", $sformatf("TLP too short: %0d DW", packet.size()))
            malformed_tlp_errors++;
            error_count++;
            tr = null;
            return;
        end
        
        // Extract LCRC (last DW)
        received_lcrc = packet.pop_back();
        
        // Calculate expected LCRC
        calculated_lcrc = calculate_lcrc(packet);
        
        // Check LCRC
        if (received_lcrc != calculated_lcrc) begin
            `uvm_error("MON", $sformatf("LCRC mismatch: expected=%08X, received=%08X",
                                        calculated_lcrc, received_lcrc))
            lcrc_errors++;
            error_count++;
            // Continue anyway to capture transaction
        end
        
        // Check sequence number
        if (seq_num != expected_rx_seq_num) begin
            `uvm_error("MON", $sformatf("Sequence number mismatch: expected=%0d, received=%0d",
                                        expected_rx_seq_num, seq_num))
            seq_num_errors++;
            error_count++;
        end
        expected_rx_seq_num = (seq_num + 1) % 4096;
        
        // Build transaction from packet
        tr = new("captured_tlp");
        tr.trans_type = PCIE_TLP;
        tr.seq_num = seq_num;
        tr.lcrc = received_lcrc;
        tr.start_time = $time;
        
        // Parse TLP header
        begin
            bit [31:0] header[];
            int hdr_size = (packet[0][30:29] inside {2'b01, 2'b11}) ? 4 : 3;
            
            header = new[hdr_size];
            for (int i = 0; i < hdr_size; i++)
                header[i] = packet[i];
            
            tr.parse_tlp_header(header);
        end
        
        // Extract payload if present
        if (tr.has_data()) begin
            int hdr_size = tr.get_header_size_dw();
            int payload_size = packet.size() - hdr_size;
            
            if (tr.td)  // Has ECRC
                payload_size--;
            
            tr.payload = new[payload_size];
            for (int i = 0; i < payload_size; i++)
                tr.payload[i] = packet[hdr_size + i];
            
            // Extract ECRC if present
            if (tr.td)
                tr.ecrc = packet[packet.size() - 1];
        end
    endtask
    
    virtual task capture_tlp_serial(output pcie_transaction tr);
        // Serial TLP capture
        // Would include deserializing, decoding 8b/10b or 128b/130b, etc.
        
        // Placeholder
        @(posedge vif_serial.refclk);
        tr = null;
    endtask
    
    virtual function void check_tlp_validity(pcie_transaction tr);
        // Check format/type consistency
        if (tr.tlp_fmt inside {TLP_FMT_3DW_D, TLP_FMT_4DW_D}) begin
            if (tr.payload.size() == 0) begin
                `uvm_error("MON", "Data format TLP has no payload")
                malformed_tlp_errors++;
            end
        end
        
        // Check length matches payload
        if (tr.has_data()) begin
            int expected_len = (tr.length == 0) ? 1024 : tr.length;
            if (tr.payload.size() != expected_len) begin
                `uvm_error("MON", $sformatf("Length mismatch: header=%0d, payload=%0d",
                                            expected_len, tr.payload.size()))
                malformed_tlp_errors++;
            end
        end
        
        // Check byte enables for single DW
        if (tr.length == 1 && tr.last_be != 4'b0000) begin
            `uvm_error("MON", "Single DW transfer has non-zero last_be")
            malformed_tlp_errors++;
        end
        
        // Check 4KB boundary
        if (!tr.is_completion()) begin
            bit [63:0] start_addr = tr.address;
            bit [63:0] end_addr = start_addr + (tr.get_length_dw() * 4) - 1;
            bit [63:0] start_page = start_addr[63:12];
            bit [63:0] end_page = end_addr[63:12];
            
            if (start_page != end_page) begin
                `uvm_error("MON", "TLP crosses 4KB boundary")
                malformed_tlp_errors++;
            end
        end
        
        // Check completion status
        if (tr.is_completion() && tr.cpl_status == CPL_SC) begin
            if (tr.tlp_type == TLP_CPLD && tr.byte_count == 0) begin
                `uvm_error("MON", "Successful CplD has zero byte count")
                malformed_tlp_errors++;
            end
        end
    endfunction
    
    //-------------------------------------------------------------------------
    // DLLP Monitoring
    //-------------------------------------------------------------------------
    
    virtual task monitor_dllps();
        forever begin
            pcie_transaction tr;
            
            if (cfg.if_mode == PCIE_PIPE_MODE)
                capture_dllp_pipe(tr);
            else
                capture_dllp_serial(tr);
            
            if (tr != null) begin
                // Update coverage
                observed_dllp_type = tr.dllp_type;
                if (cfg.enable_coverage)
                    cg_dllp_types.sample();
                
                // Send to analysis port
                dllp_ap.write(tr);
                all_ap.write(tr);
                dllp_count++;
                
                if (cfg.dump_dllps)
                    tr.print_transaction("RX");
            end
        end
    endtask
    
    virtual task capture_dllp_pipe(output pcie_transaction tr);
        bit [7:0] dllp_bytes[8];
        bit [15:0] received_crc;
        bit [15:0] calculated_crc;
        int byte_idx = 0;
        
        // Wait for SDP (Start DLLP)
        forever begin
            @(vif_pipe.mon_cb);
            
            if (vif_pipe.mon_cb.RxDataK[0] && vif_pipe.mon_cb.RxData[0] == 8'h5C) begin
                byte_idx = 0;
                break;
            end
        end
        
        // Capture DLLP bytes
        while (byte_idx < 8) begin
            @(vif_pipe.mon_cb);
            
            if (vif_pipe.mon_cb.RxDataK[0] && vif_pipe.mon_cb.RxData[0] == 8'hFD) begin
                break;  // END
            end
            
            dllp_bytes[byte_idx++] = vif_pipe.mon_cb.RxData[0];
        end
        
        if (byte_idx < 6) begin
            tr = null;
            return;
        end
        
        // Build transaction
        tr = new("captured_dllp");
        tr.trans_type = PCIE_DLLP;
        tr.dllp_type = dllp_type_e'(dllp_bytes[0]);
        tr.start_time = $time;
        
        // Parse based on DLLP type
        case (tr.dllp_type)
            DLLP_ACK, DLLP_NAK: begin
                tr.ack_nak_seq_num = {dllp_bytes[2][3:0], dllp_bytes[1]};
            end
            DLLP_INITFC1_P, DLLP_INITFC1_NP, DLLP_INITFC1_CPL,
            DLLP_INITFC2_P, DLLP_INITFC2_NP, DLLP_INITFC2_CPL,
            DLLP_UPDATEFC_P, DLLP_UPDATEFC_NP, DLLP_UPDATEFC_CPL: begin
                tr.fc_hdr_credits = dllp_bytes[1];
                tr.fc_data_credits = {dllp_bytes[3][3:0], dllp_bytes[2]};
            end
        endcase
        
        // Extract and check CRC
        received_crc = {dllp_bytes[5], dllp_bytes[4]};
        calculated_crc = calculate_dllp_crc({dllp_bytes[3], dllp_bytes[2], 
                                             dllp_bytes[1], dllp_bytes[0]});
        
        if (received_crc != calculated_crc) begin
            `uvm_error("MON", $sformatf("DLLP CRC mismatch: expected=%04X, received=%04X",
                                        calculated_crc, received_crc))
            error_count++;
        end
    endtask
    
    virtual task capture_dllp_serial(output pcie_transaction tr);
        @(posedge vif_serial.refclk);
        tr = null;
    endtask
    
    //-------------------------------------------------------------------------
    // Ordered Set Monitoring
    //-------------------------------------------------------------------------
    
    virtual task monitor_ordered_sets();
        forever begin
            pcie_transaction tr;
            
            if (cfg.if_mode == PCIE_PIPE_MODE)
                capture_os_pipe(tr);
            else
                capture_os_serial(tr);
            
            if (tr != null) begin
                // Send to analysis port
                os_ap.write(tr);
                all_ap.write(tr);
                os_count++;
                
                if (cfg.dump_ordered_sets)
                    tr.print_transaction("RX");
            end
        end
    endtask
    
    virtual task capture_os_pipe(output pcie_transaction tr);
        bit [7:0] os_bytes[16];
        int byte_idx = 0;
        
        // Wait for COM character
        forever begin
            @(vif_pipe.mon_cb);
            
            if (vif_pipe.mon_cb.RxDataK[0] && vif_pipe.mon_cb.RxData[0] == 8'hBC) begin
                os_bytes[0] = 8'hBC;
                byte_idx = 1;
                break;
            end
        end
        
        // Capture remaining ordered set symbols
        while (byte_idx < 16) begin
            @(vif_pipe.mon_cb);
            
            // Check for new ordered set or packet
            if (vif_pipe.mon_cb.RxDataK[0])
                break;
            
            os_bytes[byte_idx++] = vif_pipe.mon_cb.RxData[0];
        end
        
        // Determine ordered set type
        tr = new("captured_os");
        tr.trans_type = PCIE_ORDERED_SET;
        tr.start_time = $time;
        
        // Check TS1/TS2 identifier
        if (byte_idx >= 7) begin
            if (os_bytes[6] == 8'h4A)
                tr.os_type = OS_TS1;
            else if (os_bytes[6] == 8'h45)
                tr.os_type = OS_TS2;
            else
                tr.os_type = OS_IDLE;
            
            // Extract TS fields
            tr.ts_link_num = os_bytes[1];
            tr.ts_lane_num = os_bytes[2];
            tr.ts_n_fts = os_bytes[3];
            tr.ts_rate_id = os_bytes[4];
            tr.ts_training_ctrl = os_bytes[5][5:0];
        end else if (byte_idx >= 4) begin
            // Short ordered sets
            if (os_bytes[1] == 8'h1C)
                tr.os_type = OS_SKP;
            else if (os_bytes[1] == 8'h3C)
                tr.os_type = OS_FTS;
            else
                tr.os_type = OS_IDLE;
        end else begin
            tr = null;
        end
    endtask
    
    virtual task capture_os_serial(output pcie_transaction tr);
        @(posedge vif_serial.refclk);
        tr = null;
    endtask
    
    //-------------------------------------------------------------------------
    // LTSSM Monitoring
    //-------------------------------------------------------------------------
    
    virtual task monitor_ltssm();
        ltssm_state_e prev_state;
        
        forever begin
            @(vif_pipe.mon_cb);
            
            prev_state = observed_ltssm_state;
            
            // Infer LTSSM state from interface signals
            if (cfg.if_mode == PCIE_PIPE_MODE) begin
                // Check TxElecIdle
                bit all_tx_elec_idle;
                all_tx_elec_idle = 1'b1;
                for (int lane = 0; lane < cfg.get_num_lanes(); lane++) begin
                    all_tx_elec_idle &= vif_pipe.TxElecIdle[lane];
                end
                if (all_tx_elec_idle) begin
                    // Electrical idle on all lanes
                    if (vif_pipe.PowerDown == 2'b11)
                        observed_ltssm_state = LTSSM_DETECT_QUIET;
                    else if (vif_pipe.PowerDown == 2'b10)
                        observed_ltssm_state = LTSSM_L1_ENTRY;
                end else begin
                    // Check for link up based on data activity
                    if (vif_pipe.RxValid[0] || vif_pipe.TxDataValid[0]) begin
                        observed_ltssm_state = LTSSM_L0;
                        link_up = 1;
                    end
                end
                
                // Track speed changes
                case (vif_pipe.Rate)
                    2'b00: observed_gen = PCIE_GEN1;
                    2'b01: observed_gen = PCIE_GEN2;
                    2'b10: observed_gen = PCIE_GEN3;
                    2'b11: observed_gen = PCIE_GEN4;
                endcase
            end
            
            // Log state changes
            if (prev_state != observed_ltssm_state) begin
                `uvm_info("MON", $sformatf("LTSSM: %s -> %s", 
                                           prev_state.name(), observed_ltssm_state.name()), UVM_MEDIUM)
                
                if (cfg.enable_coverage)
                    cg_ltssm_states.sample();
            end
        end
    endtask
    
    //-------------------------------------------------------------------------
    // Error Monitoring
    //-------------------------------------------------------------------------
    
    virtual task monitor_errors();
        forever begin
            @(vif_pipe.mon_cb);
            
            if (cfg.if_mode == PCIE_PIPE_MODE) begin
                // Check RxStatus for errors
                for (int lane = 0; lane < cfg.get_num_lanes(); lane++) begin
                    if (vif_pipe.RxValid[lane]) begin
                        case (vif_pipe.RxStatus[lane])
                            3'b001: begin  // SKP added
                                // Normal, not an error
                            end
                            3'b010: begin  // SKP deleted
                                // Normal, not an error
                            end
                            3'b100: begin  // 8b/10b decode error
                                `uvm_error("MON", $sformatf("8b/10b decode error on lane %0d", lane))
                                error_count++;
                            end
                            3'b101: begin  // Elastic buffer overflow
                                `uvm_error("MON", $sformatf("Elastic buffer overflow on lane %0d", lane))
                                error_count++;
                            end
                            3'b110: begin  // Elastic buffer underflow
                                `uvm_error("MON", $sformatf("Elastic buffer underflow on lane %0d", lane))
                                error_count++;
                            end
                            3'b111: begin  // Disparity error
                                `uvm_error("MON", $sformatf("Disparity error on lane %0d", lane))
                                error_count++;
                            end
                        endcase
                    end
                end
            end
        end
    endtask
    
    //-------------------------------------------------------------------------
    // CRC Calculation
    //-------------------------------------------------------------------------
    
    function bit [31:0] calculate_lcrc(bit [31:0] data[]);
        bit [31:0] crc = 32'hFFFFFFFF;
        
        foreach (data[i]) begin
            crc = crc ^ data[i];
            for (int b = 0; b < 32; b++) begin
                if (crc[0])
                    crc = (crc >> 1) ^ 32'hEDB88320;
                else
                    crc = crc >> 1;
            end
        end
        
        return ~crc;
    endfunction
    
    function bit [15:0] calculate_dllp_crc(bit [31:0] data);
        bit [15:0] crc = 16'hFFFF;
        
        for (int i = 0; i < 4; i++) begin
            crc = crc ^ data[i*8 +: 8];
            for (int b = 0; b < 8; b++) begin
                if (crc[0])
                    crc = (crc >> 1) ^ 16'h8005;
                else
                    crc = crc >> 1;
            end
        end
        
        return ~crc;
    endfunction
    
endclass
