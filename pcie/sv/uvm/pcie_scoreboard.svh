//-----------------------------------------------------------------------------
// File: pcie_scoreboard.sv
// Description: PCIe Scoreboard - Transaction Checking and Completion Matching
//
// Copyright (c) KVIPS Project
// SPDX-License-Identifier: Apache-2.0
//-----------------------------------------------------------------------------

class pcie_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(pcie_scoreboard)
    
    //-------------------------------------------------------------------------
    // Configuration
    //-------------------------------------------------------------------------
    
    pcie_cfg cfg;
    
    //-------------------------------------------------------------------------
    // Analysis Exports
    //-------------------------------------------------------------------------
    
    `uvm_analysis_imp_decl(_rc)
    `uvm_analysis_imp_decl(_ep)

    // Receive transactions from monitors
    uvm_analysis_imp_rc #(pcie_transaction, pcie_scoreboard) rc_export;
    uvm_analysis_imp_ep #(pcie_transaction, pcie_scoreboard) ep_export;
    
    //-------------------------------------------------------------------------
    // Transaction Tracking
    //-------------------------------------------------------------------------
    
    // Outstanding non-posted requests (awaiting completion)
    // Key: {requester_id, tag}
    pcie_transaction outstanding_np[bit [25:0]];
    
    // Posted write tracking (for memory compare)
    pcie_transaction posted_writes[$];
    
    // Completion tracking
    pcie_transaction completions[$];
    
    // Memory model (simple associative array)
    bit [31:0] memory[bit [63:0]];
    
    //-------------------------------------------------------------------------
    // Statistics
    //-------------------------------------------------------------------------
    
    int unsigned rc_tlp_count;
    int unsigned ep_tlp_count;
    int unsigned completions_matched;
    int unsigned completions_unexpected;
    int unsigned ordering_violations;
    int unsigned data_mismatches;
    int unsigned timeout_errors;
    
    //-------------------------------------------------------------------------
    // Ordering Tracking
    //-------------------------------------------------------------------------
    
    // Track ordering for each TC
    int unsigned posted_sn[8];      // Posted sequence number per TC
    int unsigned np_sn[8];          // Non-posted sequence number per TC
    int unsigned cpl_sn[8];         // Completion sequence number per TC
    
    //-------------------------------------------------------------------------
    // Methods
    //-------------------------------------------------------------------------
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create analysis exports
        rc_export = new("rc_export", this);
        ep_export = new("ep_export", this);
        
        // Get configuration
        if (!uvm_config_db #(pcie_cfg)::get(this, "", "cfg", cfg))
            `uvm_fatal("CFG", "Failed to get pcie_cfg")
    endfunction
    
    virtual function void start_of_simulation_phase(uvm_phase phase);
        // Initialize tracking
        outstanding_np.delete();
        posted_writes.delete();
        completions.delete();
        memory.delete();
        
        rc_tlp_count = 0;
        ep_tlp_count = 0;
        completions_matched = 0;
        completions_unexpected = 0;
        ordering_violations = 0;
        data_mismatches = 0;
        timeout_errors = 0;
        
        for (int tc = 0; tc < 8; tc++) begin
            posted_sn[tc] = 0;
            np_sn[tc] = 0;
            cpl_sn[tc] = 0;
        end
    endfunction
    
    //-------------------------------------------------------------------------
    // Analysis Write Methods
    //-------------------------------------------------------------------------
    
    // Receive TLP from RC monitor
    virtual function void write_rc(pcie_transaction tr);
        if (tr.trans_type != PCIE_TLP) return;
        
        rc_tlp_count++;
        
        `uvm_info("SCB", $sformatf("RC TX: %s tag=%0d addr=%016X", 
                                   tr.tlp_type.name(), tr.tag, tr.address), UVM_HIGH)
        
        // Process based on transaction type
        if (tr.is_non_posted()) begin
            process_non_posted_request(tr, 1);  // From RC
        end else if (tr.is_posted()) begin
            process_posted_request(tr, 1);
        end else if (tr.is_completion()) begin
            process_completion(tr, 1);
        end
        
        // Check ordering
        if (cfg.enable_ordering_checks)
            check_ordering(tr, 1);
    endfunction
    
    // Receive TLP from EP monitor
    virtual function void write_ep(pcie_transaction tr);
        if (tr.trans_type != PCIE_TLP) return;
        
        ep_tlp_count++;
        
        `uvm_info("SCB", $sformatf("EP TX: %s tag=%0d addr=%016X", 
                                   tr.tlp_type.name(), tr.tag, tr.address), UVM_HIGH)
        
        // Process based on transaction type
        if (tr.is_non_posted()) begin
            process_non_posted_request(tr, 0);  // From EP
        end else if (tr.is_posted()) begin
            process_posted_request(tr, 0);
        end else if (tr.is_completion()) begin
            process_completion(tr, 0);
        end
        
        // Check ordering
        if (cfg.enable_ordering_checks)
            check_ordering(tr, 0);
    endfunction
    
    //-------------------------------------------------------------------------
    // Transaction Processing
    //-------------------------------------------------------------------------
    
    virtual function void process_non_posted_request(pcie_transaction tr, bit from_rc);
        bit [25:0] key = {tr.requester_id, tr.tag};
        
        // Check for duplicate tag
        if (outstanding_np.exists(key)) begin
            `uvm_error("SCB", $sformatf("Duplicate tag detected: ReqID=%04X Tag=%0d",
                                        tr.requester_id, tr.tag))
        end
        
        // Add to outstanding
        outstanding_np[key] = tr;
        
        // For memory reads, predict completion data
        if (tr.tlp_type inside {TLP_MRD32, TLP_MRD64}) begin
            // Data would come from memory model
        end
    endfunction
    
    virtual function void process_posted_request(pcie_transaction tr, bit from_rc);
        // Track for ordering checks
        posted_writes.push_back(tr);
        
        // Update memory model for writes
        if (tr.tlp_type inside {TLP_MWR32, TLP_MWR64}) begin
            bit [63:0] addr = tr.address;
            
            foreach (tr.payload[i]) begin
                memory[addr] = tr.payload[i];
                addr += 4;
            end
            
            `uvm_info("SCB", $sformatf("Memory updated: addr=%016X, len=%0d DW",
                                       tr.address, tr.payload.size()), UVM_HIGH)
        end
    endfunction
    
    virtual function void process_completion(pcie_transaction tr, bit from_rc);
        bit [25:0] key = {tr.requester_id, tr.tag};
        pcie_transaction orig_req;
        
        // Find matching request
        if (outstanding_np.exists(key)) begin
            orig_req = outstanding_np[key];
            
            // Check completion status
            if (tr.cpl_status != CPL_SC) begin
                `uvm_warning("SCB", $sformatf("Non-successful completion: %s for tag=%0d",
                                              tr.cpl_status.name(), tr.tag))
            end
            
            // For memory reads, verify data
            if (orig_req.tlp_type inside {TLP_MRD32, TLP_MRD64} && 
                tr.tlp_type == TLP_CPLD) begin
                verify_completion_data(orig_req, tr);
            end
            
            // Check byte count
            if (tr.tlp_type == TLP_CPLD) begin
                int expected_bytes = orig_req.get_payload_bytes();
                if (tr.byte_count != expected_bytes) begin
                    // Could be split completion - track remaining
                    `uvm_info("SCB", $sformatf("Partial completion: %0d of %0d bytes",
                                               tr.byte_count, expected_bytes), UVM_MEDIUM)
                end
            end
            
            // Remove from outstanding (or update for split completions)
            if (is_final_completion(orig_req, tr)) begin
                outstanding_np.delete(key);
                completions_matched++;
            end
            
        end else begin
            `uvm_error("SCB", $sformatf("Unexpected completion: ReqID=%04X Tag=%0d",
                                        tr.requester_id, tr.tag))
            completions_unexpected++;
        end
        
        completions.push_back(tr);
    endfunction
    
    //-------------------------------------------------------------------------
    // Data Verification
    //-------------------------------------------------------------------------
    
    virtual function void verify_completion_data(pcie_transaction req, 
                                                  pcie_transaction cpl);
        bit [63:0] addr = req.address;
        bit [31:0] expected_data;
        
        `uvm_info("SCB", $sformatf("Verifying completion data: addr=%016X, len=%0d",
                                   addr, cpl.payload.size()), UVM_HIGH)
        
        foreach (cpl.payload[i]) begin
            // Get expected from memory model
            if (memory.exists(addr)) begin
                expected_data = memory[addr];
                
                if (cpl.payload[i] != expected_data) begin
                    `uvm_error("SCB", $sformatf("Data mismatch at addr=%016X: exp=%08X, got=%08X",
                                                addr, expected_data, cpl.payload[i]))
                    data_mismatches++;
                end
            end else begin
                `uvm_info("SCB", $sformatf("No expected data at addr=%016X (uninitialized)",
                                           addr), UVM_HIGH)
            end
            
            addr += 4;
        end
    endfunction
    
    virtual function bit is_final_completion(pcie_transaction req, 
                                             pcie_transaction cpl);
        // Check if this completion satisfies the entire request
        int requested_bytes = req.get_payload_bytes();
        
        // For simplicity, assume single completion
        // Real implementation would track split completions
        return (cpl.byte_count >= requested_bytes);
    endfunction
    
    //-------------------------------------------------------------------------
    // Ordering Checks
    //-------------------------------------------------------------------------
    
    virtual function void check_ordering(pcie_transaction tr, bit from_rc);
        bit [2:0] tc = tr.tc;
        
        // PCIe ordering rules:
        // 1. Posted requests can pass non-posted requests
        // 2. Non-posted requests cannot pass posted requests (to same address)
        // 3. Completions can pass posted requests
        // 4. Read completions cannot pass write completions (relaxed ordering)
        
        if (tr.is_posted()) begin
            // Check against outstanding non-posted to same address
            foreach (outstanding_np[key]) begin
                pcie_transaction np = outstanding_np[key];
                if (np.tc == tc && addresses_overlap(tr, np)) begin
                    if (!tr.attr[0]) begin  // Relaxed ordering not set
                        // This might be an ordering violation depending on implementation
                        `uvm_info("SCB", $sformatf("Posted passing non-posted to overlapping addr"),
                                  UVM_MEDIUM)
                    end
                end
            end
            posted_sn[tc]++;
        end else if (tr.is_non_posted()) begin
            np_sn[tc]++;
        end else if (tr.is_completion()) begin
            cpl_sn[tc]++;
        end
    endfunction
    
    virtual function bit addresses_overlap(pcie_transaction a, pcie_transaction b);
        bit [63:0] a_start = a.address;
        bit [63:0] a_end = a.address + a.get_length_dw() * 4 - 1;
        bit [63:0] b_start = b.address;
        bit [63:0] b_end = b.address + b.get_length_dw() * 4 - 1;
        
        return !((a_end < b_start) || (b_end < a_start));
    endfunction
    
    //-------------------------------------------------------------------------
    // Timeout Checking
    //-------------------------------------------------------------------------
    
    virtual function void check_phase(uvm_phase phase);
        // Check for outstanding transactions at end of test
        if (outstanding_np.size() > 0) begin
            `uvm_error("SCB", $sformatf("%0d non-posted transactions without completions",
                                        outstanding_np.size()))
            
            foreach (outstanding_np[key]) begin
                pcie_transaction tr = outstanding_np[key];
                `uvm_info("SCB", $sformatf("  Outstanding: %s ReqID=%04X Tag=%0d Addr=%016X",
                                           tr.tlp_type.name(), tr.requester_id, 
                                           tr.tag, tr.address), UVM_LOW)
                timeout_errors++;
            end
        end
    endfunction
    
    //-------------------------------------------------------------------------
    // Reporting
    //-------------------------------------------------------------------------
    
    virtual function void report_phase(uvm_phase phase);
        bit pass = (data_mismatches == 0 && completions_unexpected == 0 && 
                   ordering_violations == 0 && timeout_errors == 0);
        
        `uvm_info("SCB", "===== Scoreboard Report =====", UVM_LOW)
        `uvm_info("SCB", $sformatf("RC TLPs:              %0d", rc_tlp_count), UVM_LOW)
        `uvm_info("SCB", $sformatf("EP TLPs:              %0d", ep_tlp_count), UVM_LOW)
        `uvm_info("SCB", $sformatf("Completions matched:  %0d", completions_matched), UVM_LOW)
        `uvm_info("SCB", $sformatf("Unexpected completions: %0d", completions_unexpected), UVM_LOW)
        `uvm_info("SCB", $sformatf("Data mismatches:      %0d", data_mismatches), UVM_LOW)
        `uvm_info("SCB", $sformatf("Ordering violations:  %0d", ordering_violations), UVM_LOW)
        `uvm_info("SCB", $sformatf("Timeout errors:       %0d", timeout_errors), UVM_LOW)
        `uvm_info("SCB", $sformatf("Result:               %s", pass ? "PASS" : "FAIL"), UVM_LOW)
        `uvm_info("SCB", "==============================", UVM_LOW)
        
        if (!pass)
            `uvm_error("SCB", "Scoreboard detected errors")
    endfunction
    
endclass

//-----------------------------------------------------------------------------
// PCIe Coverage Collector
//-----------------------------------------------------------------------------

class pcie_coverage extends uvm_subscriber #(pcie_transaction);
    `uvm_component_utils(pcie_coverage)
    
    //-------------------------------------------------------------------------
    // Configuration
    //-------------------------------------------------------------------------
    
    pcie_cfg cfg;
    
    //-------------------------------------------------------------------------
    // Sampled Values
    //-------------------------------------------------------------------------
    
    pcie_transaction current_tr;
    bit current_is_completion;
    
    //-------------------------------------------------------------------------
    // Coverage Groups
    //-------------------------------------------------------------------------
    
    covergroup cg_tlp_coverage;
        option.per_instance = 1;
        option.name = "TLP_Coverage";
        
        // TLP types
        cp_tlp_type: coverpoint current_tr.tlp_type {
            bins memory_rd = {TLP_MRD32, TLP_MRD64};
            bins memory_wr = {TLP_MWR32, TLP_MWR64};
            bins memory_rdlk = {TLP_MRDLK32, TLP_MRDLK64};
            bins io = {TLP_IORD, TLP_IOWR};
            bins cfg_type0 = {TLP_CFGRD0, TLP_CFGWR0};
            bins cfg_type1 = {TLP_CFGRD1, TLP_CFGWR1};
            bins completion = {TLP_CPL, TLP_CPLD, TLP_CPLLK, TLP_CPLDLK};
            bins message = {TLP_MSG, TLP_MSGD};
            bins atomic = {TLP_FETCH_ADD32, TLP_FETCH_ADD64, TLP_SWAP32, TLP_SWAP64, TLP_CAS32, TLP_CAS64};
        }
        
        // Traffic class
        cp_tc: coverpoint current_tr.tc {
            bins tc[] = {[0:7]};
        }
        
        // Attributes
        cp_relaxed_ordering: coverpoint current_tr.attr[0] {
            bins no_ro = {0};
            bins ro = {1};
        }
        
        cp_no_snoop: coverpoint current_tr.attr[1] {
            bins no_ns = {0};
            bins ns = {1};
        }
        
        // TLP digest (ECRC)
        cp_td: coverpoint current_tr.td {
            bins no_ecrc = {0};
            bins has_ecrc = {1};
        }
        
        // Poisoned
        cp_ep: coverpoint current_tr.ep {
            bins not_poisoned = {0};
            bins poisoned = {1};
        }
        
        // Length categories
        cp_length: coverpoint current_tr.length {
            bins len_1 = {1};
            bins len_2_3 = {[2:3]};
            bins len_4_7 = {[4:7]};
            bins len_8_15 = {[8:15]};
            bins len_16_31 = {[16:31]};
            bins len_32_63 = {[32:63]};
            bins len_64_127 = {[64:127]};
            bins len_128_255 = {[128:255]};
            bins len_256_511 = {[256:511]};
            bins len_512_1023 = {[512:1023]};
            bins len_1024 = {0};  // 0 means 1024
        }
        
        // Address alignment
        cp_addr_align: coverpoint current_tr.address[5:2] {
            bins aligned_16b = {4'b0000};
            bins aligned_32b = {4'b0000, 4'b0100};
            bins aligned_64b = {4'b0000};
            bins aligned_128b = {4'b0000};
            bins unaligned[] = default;
        }
        
        // First byte enable
        cp_first_be: coverpoint current_tr.first_be {
            bins all_enabled = {4'b1111};
            bins partial[] = {4'b0001, 4'b0011, 4'b0111, 4'b1110, 4'b1100, 4'b1000};
            bins others = default;
        }
        
        // Last byte enable
        cp_last_be: coverpoint current_tr.last_be iff (current_tr.length > 1) {
            bins all_enabled = {4'b1111};
            bins partial[] = {4'b0001, 4'b0011, 4'b0111, 4'b1110, 4'b1100, 4'b1000};
            bins others = default;
        }
        
        // Completion status
        cp_cpl_status: coverpoint current_tr.cpl_status iff (current_is_completion) {
            bins success = {CPL_SC};
            bins ur = {CPL_UR};
            bins crs = {CPL_CRS};
            bins ca = {CPL_CA};
        }
        
        // Cross coverage
        cross_type_tc: cross cp_tlp_type, cp_tc;
        cross_type_length: cross cp_tlp_type, cp_length {
            ignore_bins cfg_length = binsof(cp_tlp_type) intersect {TLP_CFGRD0, TLP_CFGRD1, 
                                                                     TLP_CFGWR0, TLP_CFGWR1} &&
                                    (binsof(cp_length) intersect {[0:0], [2:1023]});
        }
        cross_type_attr: cross cp_tlp_type, cp_relaxed_ordering, cp_no_snoop;
    endgroup
    
    covergroup cg_completion_coverage;
        option.per_instance = 1;
        option.name = "Completion_Coverage";
        
        cp_cpl_type: coverpoint current_tr.tlp_type iff (current_is_completion) {
            bins cpl = {TLP_CPL};
            bins cpld = {TLP_CPLD};
            bins cpllk = {TLP_CPLLK};
            bins cpldlk = {TLP_CPLDLK};
        }
        
        cp_byte_count: coverpoint current_tr.byte_count iff (current_is_completion) {
            bins bc_small = {[1:64]};
            bins bc_medium = {[65:256]};
            bins bc_large = {[257:4096]};
        }
        
        cp_lower_addr: coverpoint current_tr.lower_addr iff (current_is_completion) {
            bins aligned = {7'h00};
            bins unaligned = default;
        }
    endgroup
    
    covergroup cg_address_coverage;
        option.per_instance = 1;
        option.name = "Address_Coverage";
        
        cp_addr_type: coverpoint current_tr.addr_type_64bit iff (!current_is_completion) {
            bins addr_32bit = {0};
            bins addr_64bit = {1};
        }
        
        cp_addr_range: coverpoint current_tr.address[31:28] iff (!current_is_completion) {
            bins low[] = {[0:3]};
            bins mid[] = {[4:11]};
            bins high[] = {[12:15]};
        }
        
        cp_4kb_boundary: coverpoint (current_tr.address[11:0] + current_tr.get_length_dw()*4 > 4096) 
                         iff (!current_is_completion) {
            bins within_page = {0};
            // bins crosses_page = {1};  // Should never happen for valid TLPs
        }
    endgroup
    
    //-------------------------------------------------------------------------
    // Methods
    //-------------------------------------------------------------------------
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        
        cg_tlp_coverage = new();
        cg_completion_coverage = new();
        cg_address_coverage = new();
        current_is_completion = 0;
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if (!uvm_config_db #(pcie_cfg)::get(this, "", "cfg", cfg))
            `uvm_fatal("CFG", "Failed to get pcie_cfg")
    endfunction
    
    // Required write method for uvm_subscriber
    virtual function void write(pcie_transaction t);
        if (!cfg.enable_coverage) return;
        if (t.trans_type != PCIE_TLP) return;
        
        current_tr = t;
        current_is_completion = t.is_completion();
        
        cg_tlp_coverage.sample();
        
        if (current_is_completion)
            cg_completion_coverage.sample();
        
        if (!current_is_completion)
            cg_address_coverage.sample();
    endfunction
    
    virtual function void report_phase(uvm_phase phase);
        `uvm_info("COV", "===== Coverage Report =====", UVM_LOW)
        `uvm_info("COV", $sformatf("TLP Coverage:        %.2f%%", cg_tlp_coverage.get_coverage()), UVM_LOW)
        `uvm_info("COV", $sformatf("Completion Coverage: %.2f%%", cg_completion_coverage.get_coverage()), UVM_LOW)
        `uvm_info("COV", $sformatf("Address Coverage:    %.2f%%", cg_address_coverage.get_coverage()), UVM_LOW)
        `uvm_info("COV", "============================", UVM_LOW)
    endfunction
    
endclass
