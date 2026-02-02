//-----------------------------------------------------------------------------
// File: pcie_sequencer.sv
// Description: PCIe Sequencer with Tag Management
//
// Copyright (c) KVIPS Project
// SPDX-License-Identifier: Apache-2.0
//-----------------------------------------------------------------------------

class pcie_sequencer extends uvm_sequencer #(pcie_transaction);
    `uvm_component_utils(pcie_sequencer)
    
    //-------------------------------------------------------------------------
    // Configuration
    //-------------------------------------------------------------------------
    
    pcie_cfg cfg;
    
    //-------------------------------------------------------------------------
    // Tag Management
    //-------------------------------------------------------------------------
    
    // Tag pool - tracks which tags are in use
    bit [1023:0] tag_in_use;          // Supports up to 10-bit tags
    int unsigned max_tag;              // Maximum tag value
    int unsigned tags_available;       // Count of available tags
    
    // Outstanding transactions by tag
    pcie_transaction outstanding_by_tag[int];
    
    // Tag allocation semaphore
    semaphore tag_sem;
    
    //-------------------------------------------------------------------------
    // Traffic Class Management
    //-------------------------------------------------------------------------
    
    // Per-TC ordering queues
    pcie_transaction posted_queue[8][$];      // Posted requests by TC
    pcie_transaction non_posted_queue[8][$];  // Non-posted requests by TC
    
    //-------------------------------------------------------------------------
    // Methods
    //-------------------------------------------------------------------------
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        tag_sem = new(1);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db #(pcie_cfg)::get(this, "", "cfg", cfg))
            `uvm_fatal("CFG", "Failed to get pcie_cfg")
        
        // Initialize tag management
        init_tags();
    endfunction
    
    //-------------------------------------------------------------------------
    // Tag Allocation/Deallocation
    //-------------------------------------------------------------------------
    
    virtual function void init_tags();
        // Determine max tag based on capabilities
        if (cfg.supports_10bit_tag)
            max_tag = 1023;  // 10-bit tags
        else if (cfg.supports_extended_tag)
            max_tag = 255;   // 8-bit tags
        else
            max_tag = 31;    // 5-bit tags (default)
        
        tag_in_use = '0;
        tags_available = max_tag + 1;
        outstanding_by_tag.delete();
        
        `uvm_info("SEQ", $sformatf("Tag pool initialized: %0d tags available (max=%0d)", 
                                   tags_available, max_tag), UVM_LOW)
    endfunction
    
    // Allocate a tag for a non-posted transaction
    virtual function bit allocate_tag(output bit [9:0] tag, input pcie_transaction tr = null);
        if (tags_available == 0) begin
            `uvm_warning("SEQ", "No tags available")
            return 0;
        end
        
        // Find first available tag
        for (int i = 0; i <= max_tag; i++) begin
            if (!tag_in_use[i]) begin
                tag_in_use[i] = 1;
                tags_available--;
                tag = i[9:0];
                
                if (tr != null)
                    outstanding_by_tag[tag] = tr;
                
                `uvm_info("SEQ", $sformatf("Tag %0d allocated (%0d remaining)", 
                                           tag, tags_available), UVM_HIGH)
                return 1;
            end
        end
        return 0;
    endfunction
    
    // Release a tag (after completion received)
    virtual function void release_tag(bit [9:0] tag);
        if (tag > max_tag) begin
            `uvm_error("SEQ", $sformatf("Invalid tag: %0d", tag))
            return;
        end
        
        if (!tag_in_use[tag]) begin
            `uvm_warning("SEQ", $sformatf("Tag %0d already released", tag))
            return;
        end
        
        tag_in_use[tag] = 0;
        tags_available++;
        outstanding_by_tag.delete(tag);
        
        `uvm_info("SEQ", $sformatf("Tag %0d released (%0d available)", 
                                   tag, tags_available), UVM_HIGH)
    endfunction
    
    // Get outstanding transaction by tag
    virtual function pcie_transaction get_outstanding(bit [9:0] tag);
        if (outstanding_by_tag.exists(tag))
            return outstanding_by_tag[tag];
        else
            return null;
    endfunction
    
    // Check if tag is in use
    virtual function bit is_tag_in_use(bit [9:0] tag);
        if (tag > max_tag)
            return 0;
        return tag_in_use[tag];
    endfunction
    
    // Get number of available tags
    function int unsigned get_available_tags();
        return tags_available;
    endfunction
    
    //-------------------------------------------------------------------------
    // Ordering Queue Management
    //-------------------------------------------------------------------------
    
    // Add transaction to ordering queue
    virtual function void add_to_ordering_queue(pcie_transaction tr);
        bit [2:0] tc = tr.tc;
        
        if (tr.is_posted())
            posted_queue[tc].push_back(tr);
        else if (tr.is_non_posted())
            non_posted_queue[tc].push_back(tr);
    endfunction
    
    // Get transactions from queue (maintains ordering)
    virtual function pcie_transaction get_from_queue(bit posted, bit [2:0] tc);
        pcie_transaction tr;
        
        if (posted) begin
            if (posted_queue[tc].size() > 0)
                tr = posted_queue[tc].pop_front();
        end else begin
            if (non_posted_queue[tc].size() > 0)
                tr = non_posted_queue[tc].pop_front();
        end
        
        return tr;
    endfunction
    
    //-------------------------------------------------------------------------
    // Statistics
    //-------------------------------------------------------------------------
    
    virtual function void report_phase(uvm_phase phase);
        int outstanding_count;
        
        foreach (outstanding_by_tag[i])
            outstanding_count++;
        
        `uvm_info("SEQ", "===== Sequencer Statistics =====", UVM_LOW)
        `uvm_info("SEQ", $sformatf("Max tags:            %0d", max_tag + 1), UVM_LOW)
        `uvm_info("SEQ", $sformatf("Tags available:      %0d", tags_available), UVM_LOW)
        `uvm_info("SEQ", $sformatf("Outstanding NP:      %0d", outstanding_count), UVM_LOW)
        
        if (outstanding_count > 0) begin
            `uvm_warning("SEQ", $sformatf("%0d transactions still outstanding at end of test",
                                          outstanding_count))
            foreach (outstanding_by_tag[tag]) begin
                `uvm_info("SEQ", $sformatf("  Tag %0d: %s", tag, 
                                           outstanding_by_tag[tag].tlp_type.name()), UVM_LOW)
            end
        end
        
        `uvm_info("SEQ", "=================================", UVM_LOW)
    endfunction
    
endclass

//-----------------------------------------------------------------------------
// Base Sequence
//-----------------------------------------------------------------------------

class pcie_base_seq extends uvm_sequence #(pcie_transaction);
    `uvm_object_utils(pcie_base_seq)
    
    //-------------------------------------------------------------------------
    // Configuration
    //-------------------------------------------------------------------------
    
    pcie_cfg cfg;
    
    // Sequence parameters
    rand int unsigned num_transactions;
    rand bit [63:0] base_address;
    rand bit [2:0] traffic_class;
    rand bit use_extended_tag;
    rand bit use_64bit_addr;
    
    // Constraints
    constraint c_defaults {
        soft num_transactions inside {[1:100]};
        soft base_address[1:0] == 2'b00;  // DW aligned
        soft traffic_class == 0;
        soft use_extended_tag == 1;
        soft use_64bit_addr == 0;
    }
    
    //-------------------------------------------------------------------------
    // Methods
    //-------------------------------------------------------------------------
    
    function new(string name = "pcie_base_seq");
        super.new(name);
    endfunction
    
    virtual task pre_start();
        // Get configuration
        if (!uvm_config_db #(pcie_cfg)::get(null, get_full_name(), "cfg", cfg)) begin
            if (!uvm_config_db #(pcie_cfg)::get(m_sequencer, "", "cfg", cfg))
                `uvm_fatal("CFG", "Failed to get pcie_cfg")
        end
    endtask
    
    virtual task body();
        `uvm_info("SEQ", $sformatf("Starting %s with %0d transactions", 
                                   get_type_name(), num_transactions), UVM_LOW)
    endtask
    
    // Helper: Create memory read transaction
    virtual function pcie_transaction create_mem_read(bit [63:0] addr, int length_dw,
                                                      bit [9:0] tag);
        pcie_transaction tr = new();
        
        tr.trans_type = PCIE_TLP;
        tr.tc = traffic_class;
        tr.tag = tag;
        tr.address = addr;
        tr.length = (length_dw == 1024) ? 0 : length_dw;
        tr.first_be = 4'hF;
        tr.last_be = (length_dw > 1) ? 4'hF : 4'h0;
        tr.requester_id = cfg.get_requester_id();
        
        if (addr[63:32] != 0 || use_64bit_addr) begin
            tr.tlp_type = TLP_MRD64;
            tr.tlp_fmt = TLP_FMT_4DW_ND;
            tr.addr_type_64bit = 1;
        end else begin
            tr.tlp_type = TLP_MRD32;
            tr.tlp_fmt = TLP_FMT_3DW_ND;
            tr.addr_type_64bit = 0;
        end
        
        return tr;
    endfunction
    
    // Helper: Create memory write transaction
    virtual function pcie_transaction create_mem_write(bit [63:0] addr, 
                                                       bit [31:0] data[]);
        pcie_transaction tr = new();
        int length_dw = data.size();
        
        tr.trans_type = PCIE_TLP;
        tr.tc = traffic_class;
        tr.address = addr;
        tr.length = (length_dw == 1024) ? 0 : length_dw;
        tr.payload = data;
        tr.first_be = 4'hF;
        tr.last_be = (length_dw > 1) ? 4'hF : 4'h0;
        tr.requester_id = cfg.get_requester_id();
        
        if (addr[63:32] != 0 || use_64bit_addr) begin
            tr.tlp_type = TLP_MWR64;
            tr.tlp_fmt = TLP_FMT_4DW_D;
            tr.addr_type_64bit = 1;
        end else begin
            tr.tlp_type = TLP_MWR32;
            tr.tlp_fmt = TLP_FMT_3DW_D;
            tr.addr_type_64bit = 0;
        end
        
        return tr;
    endfunction
    
    // Helper: Create config read transaction
    virtual function pcie_transaction create_cfg_read(bit [7:0] bus, bit [4:0] dev,
                                                      bit [2:0] func, bit [9:0] reg_addr,
                                                      bit [9:0] tag, bit type1 = 0);
        pcie_transaction tr = new();
        
        tr.trans_type = PCIE_TLP;
        tr.tlp_type = type1 ? TLP_CFGRD1 : TLP_CFGRD0;
        tr.tlp_fmt = TLP_FMT_3DW_ND;
        tr.tc = 0;  // Config always TC0
        tr.tag = tag;
        tr.length = 1;
        tr.first_be = 4'hF;
        tr.last_be = 4'h0;
        tr.requester_id = cfg.get_requester_id();
        tr.completer_id = {bus, dev, func};
        tr.ext_reg_num = reg_addr[9:6];
        tr.reg_num = reg_addr[5:0];
        
        return tr;
    endfunction
    
    // Helper: Create config write transaction
    virtual function pcie_transaction create_cfg_write(bit [7:0] bus, bit [4:0] dev,
                                                       bit [2:0] func, bit [9:0] reg_addr,
                                                       bit [31:0] data, bit [9:0] tag,
                                                       bit type1 = 0);
        pcie_transaction tr = new();
        
        tr.trans_type = PCIE_TLP;
        tr.tlp_type = type1 ? TLP_CFGWR1 : TLP_CFGWR0;
        tr.tlp_fmt = TLP_FMT_3DW_D;
        tr.tc = 0;
        tr.tag = tag;
        tr.length = 1;
        tr.payload = new[1];
        tr.payload[0] = data;
        tr.first_be = 4'hF;
        tr.last_be = 4'h0;
        tr.requester_id = cfg.get_requester_id();
        tr.completer_id = {bus, dev, func};
        tr.ext_reg_num = reg_addr[9:6];
        tr.reg_num = reg_addr[5:0];
        
        return tr;
    endfunction
    
endclass

//-----------------------------------------------------------------------------
// Memory Read/Write Sequence
//-----------------------------------------------------------------------------

class pcie_mem_seq extends pcie_base_seq;
    `uvm_object_utils(pcie_mem_seq)
    
    rand bit do_write;
    rand int unsigned length_dw;
    rand bit [31:0] write_data[];
    
    constraint c_mem {
        length_dw inside {[1:cfg.get_max_payload_bytes()/4]};
        write_data.size() == length_dw;
        do_write dist {1 := 50, 0 := 50};
    }
    
    function new(string name = "pcie_mem_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        pcie_transaction tr;
        bit [9:0] tag;
        pcie_sequencer seqr;
        
        super.body();
        
        $cast(seqr, m_sequencer);
        
        for (int i = 0; i < num_transactions; i++) begin
            if (do_write) begin
                // Memory write (posted - no tag needed)
                tr = create_mem_write(base_address + i * 4 * length_dw, write_data);
                start_item(tr);
                finish_item(tr);
            end else begin
                // Memory read (non-posted - needs tag)
                if (!seqr.allocate_tag(tag, null)) begin
                    `uvm_warning("SEQ", "Waiting for tag...")
                    wait(seqr.tags_available > 0);
                    void'(seqr.allocate_tag(tag, null));
                end
                
                tr = create_mem_read(base_address + i * 4 * length_dw, length_dw, tag);
                seqr.outstanding_by_tag[tag] = tr;
                
                start_item(tr);
                finish_item(tr);
            end
        end
    endtask
    
endclass

//-----------------------------------------------------------------------------
// Configuration Space Sequence
//-----------------------------------------------------------------------------

class pcie_cfg_seq extends pcie_base_seq;
    `uvm_object_utils(pcie_cfg_seq)
    
    rand bit [7:0] target_bus;
    rand bit [4:0] target_dev;
    rand bit [2:0] target_func;
    rand bit [9:0] reg_addresses[];
    rand bit do_write;
    rand bit [31:0] write_values[];
    
    constraint c_cfg {
        target_bus == 0;
        target_dev inside {[0:31]};
        target_func inside {[0:7]};
        reg_addresses.size() == num_transactions;
        foreach (reg_addresses[i]) {
            reg_addresses[i][1:0] == 2'b00;  // DW aligned
            reg_addresses[i] < 1024;  // Max config space
        }
        do_write dist {0 := 80, 1 := 20};  // Mostly reads
        write_values.size() == num_transactions;
    }
    
    function new(string name = "pcie_cfg_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        pcie_transaction tr;
        bit [9:0] tag;
        pcie_sequencer seqr;
        
        super.body();
        
        $cast(seqr, m_sequencer);
        
        for (int i = 0; i < num_transactions; i++) begin
            // Allocate tag (config accesses are non-posted)
            if (!seqr.allocate_tag(tag, null)) begin
                wait(seqr.tags_available > 0);
                void'(seqr.allocate_tag(tag, null));
            end
            
            if (do_write) begin
                tr = create_cfg_write(target_bus, target_dev, target_func,
                                     reg_addresses[i], write_values[i], tag);
            end else begin
                tr = create_cfg_read(target_bus, target_dev, target_func,
                                    reg_addresses[i], tag);
            end
            
            seqr.outstanding_by_tag[tag] = tr;
            
            start_item(tr);
            finish_item(tr);
            
            // Small delay between config accesses
            #100ns;
        end
    endtask
    
endclass

//-----------------------------------------------------------------------------
// Stress Sequence
//-----------------------------------------------------------------------------

class pcie_stress_seq extends pcie_base_seq;
    `uvm_object_utils(pcie_stress_seq)
    
    rand int unsigned burst_size;
    rand int unsigned inter_burst_delay_ns;
    
    constraint c_stress {
        num_transactions inside {[100:10000]};
        burst_size inside {[1:32]};
        inter_burst_delay_ns inside {[0:100]};
    }
    
    function new(string name = "pcie_stress_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        pcie_transaction tr;
        bit [9:0] tag;
        pcie_sequencer seqr;
        int transaction_count = 0;
        bit [31:0] data[];
        
        super.body();
        
        $cast(seqr, m_sequencer);
        
        while (transaction_count < num_transactions) begin
            // Generate burst
            for (int b = 0; b < burst_size && transaction_count < num_transactions; b++) begin
                int op = $urandom_range(0, 2);
                
                case (op)
                    0: begin  // Memory write
                        data = new[4];
                        foreach (data[i]) data[i] = $urandom();
                        tr = create_mem_write(base_address + transaction_count * 16, data);
                    end
                    1: begin  // Memory read
                        if (seqr.allocate_tag(tag, null)) begin
                            tr = create_mem_read(base_address + transaction_count * 16, 4, tag);
                            seqr.outstanding_by_tag[tag] = tr;
                        end else begin
                            // Fall back to write if no tags
                            data = new[4];
                            foreach (data[i]) data[i] = $urandom();
                            tr = create_mem_write(base_address + transaction_count * 16, data);
                        end
                    end
                    2: begin  // Config read
                        if (seqr.allocate_tag(tag, null)) begin
                            tr = create_cfg_read(0, $urandom_range(0, 31), 0, 
                                               $urandom_range(0, 63) << 2, tag);
                            seqr.outstanding_by_tag[tag] = tr;
                        end else begin
                            continue;
                        end
                    end
                endcase
                
                start_item(tr);
                finish_item(tr);
                transaction_count++;
            end
            
            // Inter-burst delay
            if (inter_burst_delay_ns > 0)
                #(inter_burst_delay_ns * 1ns);
        end
        
        `uvm_info("SEQ", $sformatf("Stress sequence completed: %0d transactions", 
                                   transaction_count), UVM_LOW)
    endtask
    
endclass
