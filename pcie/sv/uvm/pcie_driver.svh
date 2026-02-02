//-----------------------------------------------------------------------------
// File: pcie_driver.sv
// Description: PCIe Driver - Full Implementation
//
// Copyright (c) KVIPS Project
// SPDX-License-Identifier: Apache-2.0
//-----------------------------------------------------------------------------

class pcie_driver extends uvm_driver #(pcie_transaction);
    `uvm_component_utils(pcie_driver)
    
    //-------------------------------------------------------------------------
    // Configuration and Interface
    //-------------------------------------------------------------------------
    
    pcie_cfg cfg;
    virtual pcie_pipe_if.mac vif_pipe;
    virtual pcie_serial_if.tx vif_serial;
    
    //-------------------------------------------------------------------------
    // State Variables
    //-------------------------------------------------------------------------
    
    // LTSSM state
    ltssm_state_e current_ltssm_state;
    bit link_up;
    pcie_gen_e current_gen;
    pcie_width_e current_width;
    
    // Sequence numbering
    bit [11:0] next_seq_num;
    
    // Flow control credits
    int unsigned ph_credits;    // Posted header
    int unsigned pd_credits;    // Posted data
    int unsigned nph_credits;   // Non-posted header
    int unsigned npd_credits;   // Non-posted data
    int unsigned cplh_credits;  // Completion header
    int unsigned cpld_credits;  // Completion data
    
    // Replay buffer
    pcie_transaction replay_buffer[$];
    int unsigned replay_buffer_size = 256;
    
    // Outstanding transactions
    pcie_transaction outstanding_np[$];  // Pending non-posted (awaiting completion)
    
    //-------------------------------------------------------------------------
    // Events
    //-------------------------------------------------------------------------
    
    event e_link_up;
    event e_link_down;
    event e_speed_change;
    
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
        
        // Get virtual interface based on mode
        if (cfg.if_mode == PCIE_PIPE_MODE) begin
            if (!uvm_config_db #(virtual pcie_pipe_if.mac)::get(this, "", "vif_pipe", vif_pipe))
                `uvm_fatal("VIF", "Failed to get pcie_pipe_if")
        end else begin
            if (!uvm_config_db #(virtual pcie_serial_if.tx)::get(this, "", "vif_serial", vif_serial))
                `uvm_fatal("VIF", "Failed to get pcie_serial_if")
        end
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        // Initialize state
        reset_driver();
        
        // Wait for reset to complete
        wait_for_reset_done();
        
        // Fork parallel processes
        fork
            // Main transaction driver
            drive_transactions();
            
            // LTSSM state machine (for RC/EP modes)
            if (cfg.enable_ltssm && cfg.agent_mode != PCIE_MONITOR)
                run_ltssm();
            
            // Flow control update sender
            if (cfg.enable_ltssm && cfg.agent_mode != PCIE_MONITOR)
                send_fc_updates();
            
            // ACK/NAK handler
            if (cfg.enable_ltssm && cfg.agent_mode != PCIE_MONITOR)
                handle_ack_nak();
            
            // Replay timer
            if (cfg.enable_ltssm && cfg.agent_mode != PCIE_MONITOR)
                replay_timeout_handler();
        join
    endtask
    
    //-------------------------------------------------------------------------
    // Reset Handling
    //-------------------------------------------------------------------------
    
    virtual task reset_driver();
        current_ltssm_state = LTSSM_DETECT_QUIET;
        link_up = 0;
        current_gen = PCIE_GEN1;
        current_width = cfg.target_width;
        next_seq_num = 0;
        
        // Initialize FC credits
        ph_credits = cfg.init_ph_credits;
        pd_credits = cfg.init_pd_credits;
        nph_credits = cfg.init_nph_credits;
        npd_credits = cfg.init_npd_credits;
        cplh_credits = cfg.init_cplh_credits;
        cpld_credits = cfg.init_cpld_credits;
        
        // Clear buffers
        replay_buffer.delete();
        outstanding_np.delete();
        
        // Drive reset values on interface
        if (cfg.if_mode == PCIE_PIPE_MODE) begin
            drive_pipe_reset();
        end else begin
            drive_serial_reset();
        end
        
        `uvm_info("DRV", "Driver reset complete", UVM_LOW)
    endtask
    
    virtual task wait_for_reset_done();
        if (cfg.if_mode == PCIE_PIPE_MODE) begin
            @(posedge vif_pipe.reset_n);
            repeat(10) @(vif_pipe.mac_cb);
        end else begin
            @(posedge vif_serial.refclk);
            repeat(100) @(posedge vif_serial.refclk);
        end
    endtask
    
    virtual task drive_pipe_reset();
        for (int lane = 0; lane < cfg.get_num_lanes(); lane++) begin
            vif_pipe.mac_cb.TxData[lane] <= '0;
            vif_pipe.mac_cb.TxDataK[lane] <= '0;
            vif_pipe.mac_cb.TxDataValid[lane] <= 0;
            vif_pipe.mac_cb.TxElecIdle[lane] <= 1;
            vif_pipe.mac_cb.TxCompliance[lane] <= 0;
        end
        vif_pipe.mac_cb.TxDetectRx_Loopback <= 1'b0;
        vif_pipe.mac_cb.PowerDown <= 2'b11;  // P2 state
        vif_pipe.mac_cb.Rate <= 2'b00;  // Gen1
    endtask
    
    virtual task drive_serial_reset();
        for (int lane = 0; lane < cfg.get_num_lanes(); lane++) begin
            vif_serial.TXP[lane] <= 1'b0;
            vif_serial.TXN[lane] <= 1'b1;
        end
    endtask
    
    //-------------------------------------------------------------------------
    // Transaction Driver
    //-------------------------------------------------------------------------
    
    virtual task drive_transactions();
        pcie_transaction tr;
        
        forever begin
            // Wait for link up
            wait(link_up);
            
            // Get next transaction from sequencer
            seq_item_port.get_next_item(tr);
            
            `uvm_info("DRV", $sformatf("Driving transaction: %s", tr.trans_type.name()), UVM_HIGH)
            
            // Drive based on transaction type
            case (tr.trans_type)
                PCIE_TLP:         drive_tlp(tr);
                PCIE_DLLP:        drive_dllp(tr);
                PCIE_ORDERED_SET: drive_ordered_set(tr);
            endcase
            
            seq_item_port.item_done();
        end
    endtask
    
    //-------------------------------------------------------------------------
    // TLP Driving
    //-------------------------------------------------------------------------
    
    virtual task drive_tlp(pcie_transaction tr);
        bit [31:0] packet[];
        
        // Check flow control credits
        if (!check_fc_credits(tr)) begin
            `uvm_warning("DRV", "Insufficient FC credits, waiting...")
            wait_for_credits(tr);
        end
        
        // Assign sequence number
        tr.seq_num = next_seq_num;
        next_seq_num = (next_seq_num + 1) % 4096;
        
        // Build TLP packet
        tr.build_tlp_packet(packet);
        
        // Calculate LCRC
        tr.lcrc = calculate_lcrc(packet);
        
        // Add to replay buffer
        add_to_replay_buffer(tr);
        
        // Track non-posted transactions
        if (tr.is_non_posted()) begin
            outstanding_np.push_back(tr);
        end
        
        // Consume FC credits
        consume_fc_credits(tr);
        
        // Drive packet on interface
        if (cfg.if_mode == PCIE_PIPE_MODE) begin
            drive_tlp_pipe(tr, packet);
        end else begin
            drive_tlp_serial(tr, packet);
        end
        
        tr.start_time = $time;
        `uvm_info("DRV", $sformatf("TLP sent: %s tag=%0d addr=%016X", 
                                   tr.tlp_type.name(), tr.tag, tr.address), UVM_MEDIUM)
    endtask
    
    virtual task drive_tlp_pipe(pcie_transaction tr, bit [31:0] packet[]);
        bit [7:0] k_char;
        int num_lanes = cfg.get_num_lanes();
        
        // Send Start symbol
        @(vif_pipe.mac_cb);
        vif_pipe.mac_cb.TxData[0] <= 8'hFB;  // STP for Gen1/2, or block for Gen3+
        vif_pipe.mac_cb.TxDataK[0] <= 1'b1;
        for (int lane = 1; lane < num_lanes; lane++) begin
            vif_pipe.mac_cb.TxData[lane] <= 8'h00;
            vif_pipe.mac_cb.TxDataK[lane] <= 1'b0;
        end
        vif_pipe.mac_cb.TxDataValid[0] <= 1'b1;
        
        // Send sequence number (2 bytes)
        @(vif_pipe.mac_cb);
        vif_pipe.mac_cb.TxData[0] <= tr.seq_num[7:0];
        vif_pipe.mac_cb.TxData[1] <= {4'h0, tr.seq_num[11:8]};
        vif_pipe.mac_cb.TxDataK[0] <= 1'b0;
        vif_pipe.mac_cb.TxDataK[1] <= 1'b0;
        
        // Send TLP data
        for (int i = 0; i < packet.size(); i++) begin
            @(vif_pipe.mac_cb);
            // Distribute 32-bit word across lanes (depends on width)
            if (num_lanes >= 4) begin
                for (int b = 0; b < 4; b++) begin
                    vif_pipe.mac_cb.TxData[b] <= packet[i][b*8 +: 8];
                    vif_pipe.mac_cb.TxDataK[b] <= 1'b0;
                end
            end else begin
                // Serialize for narrower links
                for (int b = 0; b < 4; b++) begin
                    @(vif_pipe.mac_cb);
                    vif_pipe.mac_cb.TxData[0] <= packet[i][b*8 +: 8];
                    vif_pipe.mac_cb.TxDataK[0] <= 1'b0;
                end
            end
        end
        
        // Send LCRC
        @(vif_pipe.mac_cb);
        for (int b = 0; b < 4 && b < num_lanes; b++) begin
            vif_pipe.mac_cb.TxData[b] <= tr.lcrc[b*8 +: 8];
            vif_pipe.mac_cb.TxDataK[b] <= 1'b0;
        end
        
        // Send End symbol
        @(vif_pipe.mac_cb);
        vif_pipe.mac_cb.TxData[0] <= 8'hFD;  // END
        vif_pipe.mac_cb.TxDataK[0] <= 1'b1;
        
        // Return to idle
        @(vif_pipe.mac_cb);
        for (int lane = 0; lane < num_lanes; lane++) begin
            vif_pipe.mac_cb.TxData[lane] <= 8'h00;
            vif_pipe.mac_cb.TxDataK[lane] <= 1'b0;
            vif_pipe.mac_cb.TxDataValid[lane] <= 1'b0;
        end
    endtask
    
    virtual task drive_tlp_serial(pcie_transaction tr, bit [31:0] packet[]);
        // Serial interface driving - encode and serialize
        // This would include 8b/10b or 128b/130b encoding
        
        // Placeholder for serial transmission
        `uvm_info("DRV", "Serial TLP transmission not fully implemented", UVM_HIGH)
        
        // Simulate transmission delay
        repeat(packet.size() * 10) @(posedge vif_serial.refclk);
    endtask
    
    //-------------------------------------------------------------------------
    // DLLP Driving
    //-------------------------------------------------------------------------
    
    virtual task drive_dllp(pcie_transaction tr);
        bit [31:0] dllp_data;
        
        tr.build_dllp_packet(dllp_data);
        
        if (cfg.if_mode == PCIE_PIPE_MODE) begin
            drive_dllp_pipe(tr, dllp_data);
        end else begin
            drive_dllp_serial(tr, dllp_data);
        end
        
        `uvm_info("DRV", $sformatf("DLLP sent: %s", tr.dllp_type.name()), UVM_HIGH)
    endtask
    
    virtual task drive_dllp_pipe(pcie_transaction tr, bit [31:0] dllp_data);
        int num_lanes = cfg.get_num_lanes();
        bit [15:0] dllp_crc;
        
        // Calculate DLLP CRC
        dllp_crc = calculate_dllp_crc({tr.dllp_type[7:0], dllp_data[23:0]});
        
        // Send DLLP start
        @(vif_pipe.mac_cb);
        vif_pipe.mac_cb.TxData[0] <= 8'h5C;  // SDP symbol
        vif_pipe.mac_cb.TxDataK[0] <= 1'b1;
        
        // Send DLLP type and data
        @(vif_pipe.mac_cb);
        vif_pipe.mac_cb.TxData[0] <= tr.dllp_type[7:0];
        vif_pipe.mac_cb.TxDataK[0] <= 1'b0;
        
        @(vif_pipe.mac_cb);
        vif_pipe.mac_cb.TxData[0] <= dllp_data[7:0];
        vif_pipe.mac_cb.TxDataK[0] <= 1'b0;
        
        @(vif_pipe.mac_cb);
        vif_pipe.mac_cb.TxData[0] <= dllp_data[15:8];
        vif_pipe.mac_cb.TxDataK[0] <= 1'b0;
        
        @(vif_pipe.mac_cb);
        vif_pipe.mac_cb.TxData[0] <= dllp_data[23:16];
        vif_pipe.mac_cb.TxDataK[0] <= 1'b0;
        
        // Send CRC
        @(vif_pipe.mac_cb);
        vif_pipe.mac_cb.TxData[0] <= dllp_crc[7:0];
        vif_pipe.mac_cb.TxDataK[0] <= 1'b0;
        
        @(vif_pipe.mac_cb);
        vif_pipe.mac_cb.TxData[0] <= dllp_crc[15:8];
        vif_pipe.mac_cb.TxDataK[0] <= 1'b0;
        
        // End DLLP
        @(vif_pipe.mac_cb);
        vif_pipe.mac_cb.TxData[0] <= 8'hFD;  // END
        vif_pipe.mac_cb.TxDataK[0] <= 1'b1;
    endtask
    
    virtual task drive_dllp_serial(pcie_transaction tr, bit [31:0] dllp_data);
        // Serial DLLP transmission
        repeat(10) @(posedge vif_serial.refclk);
    endtask
    
    //-------------------------------------------------------------------------
    // Ordered Set Driving
    //-------------------------------------------------------------------------
    
    virtual task drive_ordered_set(pcie_transaction tr);
        if (cfg.if_mode == PCIE_PIPE_MODE) begin
            drive_os_pipe(tr);
        end else begin
            drive_os_serial(tr);
        end
        
        `uvm_info("DRV", $sformatf("Ordered set sent: %s", tr.os_type.name()), UVM_HIGH)
    endtask
    
    virtual task drive_os_pipe(pcie_transaction tr);
        int num_lanes = cfg.get_num_lanes();
        bit [7:0] os_data[];
        
        // Build ordered set based on type
        case (tr.os_type)
            OS_TS1: build_ts1(tr, os_data);
            OS_TS2: build_ts2(tr, os_data);
            OS_SKP: os_data = '{8'h1C, 8'h1C, 8'h1C, 8'h1C};  // SKP ordered set
            OS_FTS: os_data = '{8'h3C, 8'h3C, 8'h3C, 8'h3C};  // FTS
            OS_IDLE: os_data = '{8'h7C, 8'h7C, 8'h7C, 8'h7C}; // IDLE
            OS_EIEOS: os_data = '{8'h00, 8'hFF, 8'h00, 8'hFF}; // EIEOS
            default: os_data = '{8'h00, 8'h00, 8'h00, 8'h00};
        endcase
        
        // Drive ordered set on all lanes
        @(vif_pipe.mac_cb);
        for (int lane = 0; lane < num_lanes; lane++) begin
            vif_pipe.mac_cb.TxData[lane] <= os_data[0];
            vif_pipe.mac_cb.TxDataK[lane] <= 1'b1;  // COM character
        end
        
        // Send remaining symbols
        for (int i = 1; i < os_data.size(); i++) begin
            @(vif_pipe.mac_cb);
            for (int lane = 0; lane < num_lanes; lane++) begin
                vif_pipe.mac_cb.TxData[lane] <= os_data[i];
                vif_pipe.mac_cb.TxDataK[lane] <= 1'b0;
            end
        end
    endtask
    
    virtual task drive_os_serial(pcie_transaction tr);
        // Serial ordered set transmission
        repeat(16) @(posedge vif_serial.refclk);
    endtask
    
    function automatic void build_ts1(pcie_transaction tr, output bit [7:0] ts1[]);
        ts1 = new[16];
        ts1[0] = 8'hBC;  // COM
        ts1[1] = tr.ts_link_num;
        ts1[2] = tr.ts_lane_num;
        ts1[3] = tr.ts_n_fts;
        ts1[4] = tr.ts_rate_id;
        ts1[5] = tr.ts_training_ctrl;
        ts1[6] = 8'h4A;  // TS1 identifier
        for (int i = 7; i < ts1.size(); i++) begin
            ts1[i] = 8'h4A;
        end
    endfunction
    
    function automatic void build_ts2(pcie_transaction tr, output bit [7:0] ts2[]);
        ts2 = new[16];
        ts2[0] = 8'hBC;  // COM
        ts2[1] = tr.ts_link_num;
        ts2[2] = tr.ts_lane_num;
        ts2[3] = tr.ts_n_fts;
        ts2[4] = tr.ts_rate_id;
        ts2[5] = tr.ts_training_ctrl;
        ts2[6] = 8'h45;  // TS2 identifier
        for (int i = 7; i < ts2.size(); i++) begin
            ts2[i] = 8'h45;
        end
    endfunction
    
    //-------------------------------------------------------------------------
    // LTSSM State Machine
    //-------------------------------------------------------------------------
    
    virtual task run_ltssm();
        forever begin
            case (current_ltssm_state)
                LTSSM_DETECT_QUIET:       do_detect_quiet();
                LTSSM_DETECT_ACTIVE:      do_detect_active();
                LTSSM_POLLING_ACTIVE:     do_polling_active();
                LTSSM_POLLING_CONFIGURATION: do_polling_config();
                LTSSM_CONFIG_LINKWIDTH_START: do_config_linkwidth();
                LTSSM_CONFIG_LINKWIDTH_ACCEPT: do_config_accept();
                LTSSM_CONFIG_LANENUM_WAIT: do_config_lanenum();
                LTSSM_CONFIG_LANENUM_ACCEPT: do_config_lanenum_accept();
                LTSSM_CONFIG_COMPLETE:    do_config_complete();
                LTSSM_CONFIG_IDLE:        do_config_idle();
                LTSSM_L0:                 do_l0();
                LTSSM_L0S_ENTRY:          do_l0s();
                LTSSM_L1_ENTRY:           do_l1();
                LTSSM_RECOVERY_RCVRLOCK:  do_recovery();
                LTSSM_RECOVERY_SPEED:     do_recovery_speed();
                default: begin
                    `uvm_info("LTSSM", $sformatf("Unhandled state: %s", current_ltssm_state.name()), UVM_HIGH)
                    #100ns;
                end
            endcase
        end
    endtask
    
    virtual task do_detect_quiet();
        `uvm_info("LTSSM", "Detect.Quiet", UVM_LOW)
        
        // Wait 12ms (shortened for simulation). Use clock-based delay to avoid
        // compilation-unit timeunit/timescale differences.
        if (cfg.if_mode == PCIE_PIPE_MODE) begin
            repeat (250) @(posedge vif_pipe.pclk);
        end else begin
            repeat (100) @(posedge vif_serial.refclk);
        end
        
        current_ltssm_state = LTSSM_DETECT_ACTIVE;
    endtask
    
    virtual task do_detect_active();
        `uvm_info("LTSSM", "Detect.Active", UVM_LOW)
        
        // Assert receiver detect
        if (cfg.if_mode == PCIE_PIPE_MODE) begin
            vif_pipe.mac_cb.TxDetectRx_Loopback <= 1'b1;
            
            // Wait for PhyStatus pulse
            @(posedge vif_pipe.PhyStatus);
            
            // Check RxStatus for receiver present
            if (vif_pipe.RxStatus[0] == 3'b011) begin
                `uvm_info("LTSSM", "Receiver detected", UVM_LOW)
                current_ltssm_state = LTSSM_POLLING_ACTIVE;
            end else begin
                `uvm_warning("LTSSM", "No receiver detected")
                current_ltssm_state = LTSSM_DETECT_QUIET;
            end
            
            // Deassert detect
            vif_pipe.mac_cb.TxDetectRx_Loopback <= 1'b0;
        end else begin
            #100ns;
            current_ltssm_state = LTSSM_POLLING_ACTIVE;
        end
    endtask
    
    virtual task do_polling_active();
        `uvm_info("LTSSM", "Polling.Active", UVM_LOW)
        
        // Exit electrical idle
        if (cfg.if_mode == PCIE_PIPE_MODE) begin
            for (int lane = 0; lane < cfg.get_num_lanes(); lane++) begin
                vif_pipe.mac_cb.TxElecIdle[lane] <= 1'b0;
            end
            vif_pipe.mac_cb.PowerDown <= 2'b00;  // P0
        end
        
        // Send TS1s
        repeat(1024) begin
            pcie_transaction ts1 = new();
            ts1.trans_type = PCIE_ORDERED_SET;
            ts1.os_type = OS_TS1;
            ts1.ts_link_num = 8'hFF;  // PAD
            ts1.ts_lane_num = 8'hFF;  // PAD
            ts1.ts_n_fts = 8'hFF;
            ts1.ts_rate_id = 8'h02;   // Gen1 rate
            ts1.ts_training_ctrl = 6'h00;
            drive_ordered_set(ts1);
        end
        
        current_ltssm_state = LTSSM_POLLING_CONFIGURATION;
    endtask
    
    virtual task do_polling_config();
        `uvm_info("LTSSM", "Polling.Configuration", UVM_LOW)
        
        // Send TS2s
        repeat(1024) begin
            pcie_transaction ts2 = new();
            ts2.trans_type = PCIE_ORDERED_SET;
            ts2.os_type = OS_TS2;
            ts2.ts_link_num = 8'hFF;
            ts2.ts_lane_num = 8'hFF;
            ts2.ts_n_fts = 8'hFF;
            ts2.ts_rate_id = 8'h02;
            ts2.ts_training_ctrl = 6'h00;
            drive_ordered_set(ts2);
        end
        
        current_ltssm_state = LTSSM_CONFIG_LINKWIDTH_START;
    endtask
    
    virtual task do_config_linkwidth();
        `uvm_info("LTSSM", "Configuration.Linkwidth.Start", UVM_LOW)
        
        // Send TS1s with link number
        repeat(16) begin
            pcie_transaction ts1 = new();
            ts1.trans_type = PCIE_ORDERED_SET;
            ts1.os_type = OS_TS1;
            ts1.ts_link_num = 8'h00;  // Link 0
            ts1.ts_lane_num = 8'hFF;
            drive_ordered_set(ts1);
        end
        
        current_ltssm_state = LTSSM_CONFIG_LINKWIDTH_ACCEPT;
    endtask
    
    virtual task do_config_accept();
        current_ltssm_state = LTSSM_CONFIG_LANENUM_WAIT;
    endtask
    
    virtual task do_config_lanenum();
        `uvm_info("LTSSM", "Configuration.Lanenum.Wait", UVM_LOW)
        current_ltssm_state = LTSSM_CONFIG_LANENUM_ACCEPT;
    endtask
    
    virtual task do_config_lanenum_accept();
        current_ltssm_state = LTSSM_CONFIG_COMPLETE;
    endtask
    
    virtual task do_config_complete();
        `uvm_info("LTSSM", "Configuration.Complete", UVM_LOW)
        
        // Send TS2s
        repeat(16) begin
            pcie_transaction ts2 = new();
            ts2.trans_type = PCIE_ORDERED_SET;
            ts2.os_type = OS_TS2;
            ts2.ts_link_num = 8'h00;
            ts2.ts_lane_num = 8'h00;
            drive_ordered_set(ts2);
        end
        
        current_ltssm_state = LTSSM_CONFIG_IDLE;
    endtask
    
    virtual task do_config_idle();
        `uvm_info("LTSSM", "Configuration.Idle", UVM_LOW)
        
        // Send IDLEs and wait for FC initialization
        #100ns;
        
        // FC initialization
        init_flow_control();
        
        current_ltssm_state = LTSSM_L0;
    endtask
    
    virtual task do_l0();
        if (!link_up) begin
            link_up = 1;
            current_gen = cfg.target_gen;
            `uvm_info("LTSSM", $sformatf("Link Up! Gen%0d x%0d", 
                      current_gen + 1, cfg.get_num_lanes()), UVM_LOW)
            -> e_link_up;
        end
        
        // Stay in L0 until power management or recovery needed
        #1us;
    endtask
    
    virtual task do_l0s();
        `uvm_info("LTSSM", "L0s (Low Power)", UVM_LOW)
        #100ns;
    endtask
    
    virtual task do_l1();
        `uvm_info("LTSSM", "L1 (Low Power)", UVM_LOW)
        link_up = 0;
        -> e_link_down;
        #100ns;
    endtask
    
    virtual task do_recovery();
        `uvm_info("LTSSM", "Recovery", UVM_LOW)
        
        // Send TS1s
        repeat(32) begin
            pcie_transaction ts1 = new();
            ts1.trans_type = PCIE_ORDERED_SET;
            ts1.os_type = OS_TS1;
            drive_ordered_set(ts1);
        end
        
        current_ltssm_state = LTSSM_L0;
    endtask
    
    virtual task do_recovery_speed();
        `uvm_info("LTSSM", "Recovery.Speed", UVM_LOW)
        
        // Change speed
        if (cfg.if_mode == PCIE_PIPE_MODE) begin
            case (cfg.target_gen)
                PCIE_GEN1: vif_pipe.mac_cb.Rate <= 2'b00;
                PCIE_GEN2: vif_pipe.mac_cb.Rate <= 2'b01;
                PCIE_GEN3: vif_pipe.mac_cb.Rate <= 2'b10;
                PCIE_GEN4: vif_pipe.mac_cb.Rate <= 2'b11;
                default:   vif_pipe.mac_cb.Rate <= 2'b00;
            endcase
        end
        
        current_gen = cfg.target_gen;
        -> e_speed_change;
        
        current_ltssm_state = LTSSM_L0;
    endtask
    
    //-------------------------------------------------------------------------
    // Flow Control
    //-------------------------------------------------------------------------
    
    virtual task init_flow_control();
        pcie_transaction fc_dllp;
        
        `uvm_info("DRV", "Initializing flow control", UVM_LOW)
        
        // Send InitFC1 for each type (P, NP, CPL)
        // Posted
        fc_dllp = new();
        fc_dllp.trans_type = PCIE_DLLP;
        fc_dllp.dllp_type = DLLP_INITFC1_P;
        fc_dllp.fc_hdr_credits = cfg.init_ph_credits[7:0];
        fc_dllp.fc_data_credits = cfg.init_pd_credits[11:0];
        drive_dllp(fc_dllp);
        
        // Non-posted
        fc_dllp = new();
        fc_dllp.trans_type = PCIE_DLLP;
        fc_dllp.dllp_type = DLLP_INITFC1_NP;
        fc_dllp.fc_hdr_credits = cfg.init_nph_credits[7:0];
        fc_dllp.fc_data_credits = cfg.init_npd_credits[11:0];
        drive_dllp(fc_dllp);
        
        // Completion
        fc_dllp = new();
        fc_dllp.trans_type = PCIE_DLLP;
        fc_dllp.dllp_type = DLLP_INITFC1_CPL;
        fc_dllp.fc_hdr_credits = cfg.init_cplh_credits[7:0];
        fc_dllp.fc_data_credits = cfg.init_cpld_credits[11:0];
        drive_dllp(fc_dllp);
        
        // Repeat with InitFC2
        // Posted
        fc_dllp = new();
        fc_dllp.trans_type = PCIE_DLLP;
        fc_dllp.dllp_type = DLLP_INITFC2_P;
        fc_dllp.fc_hdr_credits = cfg.init_ph_credits[7:0];
        fc_dllp.fc_data_credits = cfg.init_pd_credits[11:0];
        drive_dllp(fc_dllp);
        
        // Non-posted
        fc_dllp = new();
        fc_dllp.trans_type = PCIE_DLLP;
        fc_dllp.dllp_type = DLLP_INITFC2_NP;
        fc_dllp.fc_hdr_credits = cfg.init_nph_credits[7:0];
        fc_dllp.fc_data_credits = cfg.init_npd_credits[11:0];
        drive_dllp(fc_dllp);
        
        // Completion
        fc_dllp = new();
        fc_dllp.trans_type = PCIE_DLLP;
        fc_dllp.dllp_type = DLLP_INITFC2_CPL;
        fc_dllp.fc_hdr_credits = cfg.init_cplh_credits[7:0];
        fc_dllp.fc_data_credits = cfg.init_cpld_credits[11:0];
        drive_dllp(fc_dllp);
        
        `uvm_info("DRV", "Flow control initialized", UVM_LOW)
    endtask
    
    virtual task send_fc_updates();
        forever begin
            // Send periodic UpdateFC DLLPs
            #10us;
            
            if (link_up) begin
                pcie_transaction fc_dllp;
                
                // Update Posted
                fc_dllp = new();
                fc_dllp.trans_type = PCIE_DLLP;
                fc_dllp.dllp_type = DLLP_UPDATEFC_P;
                fc_dllp.fc_hdr_credits = ph_credits[7:0];
                fc_dllp.fc_data_credits = pd_credits[11:0];
                drive_dllp(fc_dllp);
            end
        end
    endtask
    
    function bit check_fc_credits(pcie_transaction tr);
        int hdr_credits_needed = 1;
        int data_credits_needed = tr.has_data() ? ((tr.get_length_dw() + 3) / 4) : 0;
        
        if (cfg.infinite_fc_credits) return 1;
        
        if (tr.is_posted()) begin
            return (ph_credits >= hdr_credits_needed) && 
                   (pd_credits >= data_credits_needed);
        end else if (tr.is_non_posted()) begin
            return (nph_credits >= hdr_credits_needed) && 
                   (npd_credits >= data_credits_needed);
        end else if (tr.is_completion()) begin
            return (cplh_credits >= hdr_credits_needed) && 
                   (cpld_credits >= data_credits_needed);
        end
        
        return 1;
    endfunction
    
    task wait_for_credits(pcie_transaction tr);
        // Wait until credits become available
        wait(check_fc_credits(tr));
    endtask
    
    function void consume_fc_credits(pcie_transaction tr);
        int data_credits = tr.has_data() ? ((tr.get_length_dw() + 3) / 4) : 0;
        
        if (cfg.infinite_fc_credits) return;
        
        if (tr.is_posted()) begin
            ph_credits--;
            pd_credits -= data_credits;
        end else if (tr.is_non_posted()) begin
            nph_credits--;
            npd_credits -= data_credits;
        end else if (tr.is_completion()) begin
            cplh_credits--;
            cpld_credits -= data_credits;
        end
    endfunction
    
    //-------------------------------------------------------------------------
    // ACK/NAK and Replay
    //-------------------------------------------------------------------------
    
    virtual task handle_ack_nak();
        // Monitor for ACK/NAK DLLPs and update replay buffer
        forever begin
            @(posedge vif_pipe.pclk);
            // ACK/NAK processing would go here
            // This is a placeholder - actual implementation would monitor received DLLPs
        end
    endtask
    
    virtual task replay_timeout_handler();
        forever begin
            // Check for replay timeout
            #(cfg.replay_timeout * 1ns);
            
            if (replay_buffer.size() > 0 && link_up) begin
                `uvm_warning("DRV", "Replay timeout - retransmitting")
                // Retransmit from replay buffer
                foreach (replay_buffer[i]) begin
                    bit [31:0] packet[];
                    replay_buffer[i].build_tlp_packet(packet);
                    if (cfg.if_mode == PCIE_PIPE_MODE)
                        drive_tlp_pipe(replay_buffer[i], packet);
                end
            end
        end
    endtask
    
    function void add_to_replay_buffer(pcie_transaction tr);
        pcie_transaction tr_copy;
        
        tr_copy = new();
        tr_copy.copy(tr);
        
        replay_buffer.push_back(tr_copy);
        
        // Trim if too large
        while (replay_buffer.size() > replay_buffer_size)
            void'(replay_buffer.pop_front());
    endfunction
    
    function void ack_transaction(bit [11:0] ack_seq);
        // Remove all transactions with seq_num <= ack_seq from replay buffer
        replay_buffer = replay_buffer.find with (item.seq_num > ack_seq);
    endfunction
    
    //-------------------------------------------------------------------------
    // CRC Calculation
    //-------------------------------------------------------------------------
    
    function bit [31:0] calculate_lcrc(bit [31:0] data[]);
        bit [31:0] crc = 32'hFFFFFFFF;
        
        // Simplified CRC-32 calculation
        // Real implementation would use proper polynomial division
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
        
        // Simplified CRC-16 calculation
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
