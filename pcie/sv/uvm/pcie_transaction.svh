//-----------------------------------------------------------------------------
// File: pcie_transaction.sv
// Description: PCIe Transaction Class - Full Implementation
//
// Copyright (c) KVIPS Project
// SPDX-License-Identifier: Apache-2.0
//-----------------------------------------------------------------------------

class pcie_transaction extends uvm_sequence_item;
    
    //-------------------------------------------------------------------------
    // Transaction Type
    //-------------------------------------------------------------------------
    
    rand pcie_trans_type_e trans_type;      // TLP, DLLP, ORDERED_SET
    
    //-------------------------------------------------------------------------
    // TLP Fields
    //-------------------------------------------------------------------------
    
    // TLP Header fields
    rand tlp_type_e       tlp_type;
    rand tlp_fmt_e        tlp_fmt;
    rand bit [2:0]        tc;               // Traffic class
    rand bit              ln;               // Lightweight notification (Gen4+)
    rand bit              th;               // TLP hints
    rand bit              td;               // TLP digest (ECRC present)
    rand bit              ep;               // Error/poison
    rand bit [1:0]        attr;             // Attributes (relaxed ordering, no snoop)
    rand bit [1:0]        at;               // Address type
    rand bit [9:0]        length;           // Length in DW (0 = 1024 DW)
    
    // Requester/Completer ID
    rand bit [15:0]       requester_id;
    rand bit [15:0]       completer_id;
    
    // Tag
    rand bit [9:0]        tag;              // 10-bit tag support
    
    // Address
    rand bit [63:0]       address;
    rand bit              addr_type_64bit;  // 64-bit vs 32-bit addressing
    
    // Byte Enables
    rand bit [3:0]        first_be;
    rand bit [3:0]        last_be;
    
    // Completion specific
    rand cpl_status_e     cpl_status;
    rand bit              bcm;              // Byte count modified
    rand bit [11:0]       byte_count;
    rand bit [6:0]        lower_addr;
    
    // Message specific
    rand bit [7:0]        msg_code;
    rand bit [63:0]       msg_data;
    
    // Config specific
    rand bit [3:0]        ext_reg_num;      // Extended register number
    rand bit [5:0]        reg_num;          // Register number
    
    // Payload
    rand bit [31:0]       payload[];
    rand int              payload_size;     // Size in bytes
    
    // CRC
    rand bit [31:0]       ecrc;             // End-to-end CRC
    bit [31:0]            lcrc;             // Link CRC (calculated by DLL)
    
    //-------------------------------------------------------------------------
    // DLLP Fields
    //-------------------------------------------------------------------------
    
    rand dllp_type_e      dllp_type;
    rand bit [11:0]       ack_nak_seq_num;
    
    // Flow control DLLP fields
    rand bit [1:0]        fc_type;          // P, NP, CPL
    rand bit              hdr_fc;           // Header vs data
    rand bit [7:0]        fc_hdr_credits;
    rand bit [11:0]       fc_data_credits;
    rand bit [1:0]        fc_hdr_scale;     // For larger credit values
    rand bit [1:0]        fc_data_scale;
    
    // Power management DLLP
    rand bit [7:0]        pm_data;
    
    //-------------------------------------------------------------------------
    // Ordered Set Fields
    //-------------------------------------------------------------------------
    
    rand ordered_set_type_e os_type;
    rand bit [7:0]          ts_link_num;
    rand bit [7:0]          ts_lane_num;
    rand bit [7:0]          ts_n_fts;
    rand bit [7:0]          ts_rate_id;
    rand bit [5:0]          ts_training_ctrl;
    rand bit [7:0]          ts_eq_info;
    
    //-------------------------------------------------------------------------
    // Sequence Number (DLL)
    //-------------------------------------------------------------------------
    
    rand bit [11:0]       seq_num;
    
    //-------------------------------------------------------------------------
    // Timing Information
    //-------------------------------------------------------------------------
    
    time                  start_time;
    time                  end_time;
    
    //-------------------------------------------------------------------------
    // Status/Response
    //-------------------------------------------------------------------------
    
    bit                   is_response;
    bit                   completed;
    bit                   timed_out;
    bit                   had_error;
    string                error_msg;
    
    //-------------------------------------------------------------------------
    // UVM Macros
    //-------------------------------------------------------------------------
    
    `uvm_object_utils_begin(pcie_transaction)
        `uvm_field_enum(pcie_trans_type_e, trans_type, UVM_ALL_ON)
        `uvm_field_enum(tlp_type_e, tlp_type, UVM_ALL_ON)
        `uvm_field_enum(tlp_fmt_e, tlp_fmt, UVM_ALL_ON)
        `uvm_field_int(tc, UVM_ALL_ON)
        `uvm_field_int(td, UVM_ALL_ON)
        `uvm_field_int(ep, UVM_ALL_ON)
        `uvm_field_int(attr, UVM_ALL_ON)
        `uvm_field_int(length, UVM_ALL_ON)
        `uvm_field_int(requester_id, UVM_ALL_ON)
        `uvm_field_int(completer_id, UVM_ALL_ON)
        `uvm_field_int(tag, UVM_ALL_ON)
        `uvm_field_int(address, UVM_ALL_ON)
        `uvm_field_int(first_be, UVM_ALL_ON)
        `uvm_field_int(last_be, UVM_ALL_ON)
        `uvm_field_enum(cpl_status_e, cpl_status, UVM_ALL_ON)
        `uvm_field_int(byte_count, UVM_ALL_ON)
        `uvm_field_array_int(payload, UVM_ALL_ON)
        `uvm_field_enum(dllp_type_e, dllp_type, UVM_ALL_ON)
        `uvm_field_int(seq_num, UVM_ALL_ON)
    `uvm_object_utils_end
    
    //-------------------------------------------------------------------------
    // Constraints
    //-------------------------------------------------------------------------
    
    // TLP type vs format consistency
    constraint c_fmt_type {
        solve trans_type before tlp_type;
        solve tlp_type before tlp_fmt;
        solve tlp_fmt before length;
        solve length before payload;
        
        // Memory read has no data
        (tlp_type == TLP_MRD32 || tlp_type == TLP_MRD64) -> (tlp_fmt inside {TLP_FMT_3DW_ND, TLP_FMT_4DW_ND});
        
        // Memory write has data
        (tlp_type == TLP_MWR32 || tlp_type == TLP_MWR64) -> (tlp_fmt inside {TLP_FMT_3DW_D, TLP_FMT_4DW_D});
        
        // Config reads have no data
        (tlp_type inside {TLP_CFGRD0, TLP_CFGRD1}) -> (tlp_fmt == TLP_FMT_3DW_ND);
        
        // Config writes have data
        (tlp_type inside {TLP_CFGWR0, TLP_CFGWR1}) -> (tlp_fmt == TLP_FMT_3DW_D);
        
        // Completion with data
        (tlp_type == TLP_CPLD) -> (tlp_fmt inside {TLP_FMT_3DW_D});
        
        // Completion without data
        (tlp_type == TLP_CPL) -> (tlp_fmt inside {TLP_FMT_3DW_ND});
        
        // 64-bit addressing
        addr_type_64bit -> (tlp_fmt inside {TLP_FMT_4DW_ND, TLP_FMT_4DW_D});
    }
    
    // Address alignment
    constraint c_address {
        // DW aligned for memory operations
        (tlp_type inside {TLP_MRD32, TLP_MRD64, TLP_MWR32, TLP_MWR64}) -> 
            (address[1:0] == 2'b00);
        
        // 32-bit address fit
        (!addr_type_64bit) -> (address[63:32] == 32'h0);
    }
    
    // Length constraints
    constraint c_length {
        // 0 means 1024 DW
        length inside {[0:1023]};
        
        // Config accesses are 1 DW
        (tlp_type inside {TLP_CFGRD0, TLP_CFGRD1, TLP_CFGWR0, TLP_CFGWR1}) -> 
            (length == 1);
    }
    
    // Payload constraints
    constraint c_payload {
        solve length before payload;
        
        // Payload size matches length for data TLPs
        (tlp_fmt inside {TLP_FMT_3DW_D, TLP_FMT_4DW_D}) -> 
            (payload.size() == ((length == 0) ? 1024 : length));
        
        // No payload for non-data TLPs
        (tlp_fmt inside {TLP_FMT_3DW_ND, TLP_FMT_4DW_ND}) -> 
            (payload.size() == 0);
    }
    
    // Byte enable constraints
    constraint c_byte_enables {
        // First BE cannot be 0 for non-zero length
        (length > 0) -> (first_be != 4'b0000);
        
        // Last BE is 0 for single DW transfer
        (length == 1) -> (last_be == 4'b0000);
        
        // Last BE cannot be 0 for multi-DW transfer
        (length > 1) -> (last_be != 4'b0000);
        
        // Contiguous byte enables (simplified)
        first_be inside {4'b0001, 4'b0011, 4'b0111, 4'b1111,
                         4'b0010, 4'b0110, 4'b1110,
                         4'b0100, 4'b1100,
                         4'b1000,
                         4'b0101, 4'b1010, 4'b1001, 4'b0110};
    }
    
    // Tag constraints
    constraint c_tag {
        // 8-bit or 10-bit tag based on capabilities
        soft tag inside {[0:255]};  // Default 8-bit
    }
    
    // Completion constraints
    constraint c_completion {
        (tlp_type inside {TLP_CPL, TLP_CPLD}) -> (cpl_status inside {CPL_SC, CPL_UR, CPL_CRS, CPL_CA});
        
        // Byte count for completions
        (tlp_type == TLP_CPLD) -> (byte_count > 0);
    }
    
    // DLLP constraints
    constraint c_dllp {
        (trans_type == PCIE_DLLP) -> (dllp_type != DLLP_NOP);
        
        // FC type consistency
        (dllp_type inside {DLLP_INITFC1_P, DLLP_INITFC2_P, DLLP_UPDATEFC_P}) -> (fc_type == 2'b00);
        (dllp_type inside {DLLP_INITFC1_NP, DLLP_INITFC2_NP, DLLP_UPDATEFC_NP}) -> (fc_type == 2'b01);
        (dllp_type inside {DLLP_INITFC1_CPL, DLLP_INITFC2_CPL, DLLP_UPDATEFC_CPL}) -> (fc_type == 2'b10);
    }
    
    // Traffic class constraint
    constraint c_traffic_class {
        tc inside {[0:7]};
    }
    
    //-------------------------------------------------------------------------
    // Methods
    //-------------------------------------------------------------------------
    
    function new(string name = "pcie_transaction");
        super.new(name);
    endfunction
    
    // Check if this is a posted transaction
    function bit is_posted();
        return (tlp_type inside {TLP_MWR32, TLP_MWR64, TLP_MSG, TLP_MSGD});
    endfunction
    
    // Check if this is a non-posted transaction
    function bit is_non_posted();
        return (tlp_type inside {TLP_MRD32, TLP_MRD64, TLP_MRDLK32, TLP_MRDLK64,
                                 TLP_CFGRD0, TLP_CFGRD1, TLP_CFGWR0, TLP_CFGWR1,
                                 TLP_IORD, TLP_IOWR});
    endfunction
    
    // Check if this is a completion
    function bit is_completion();
        return (tlp_type inside {TLP_CPL, TLP_CPLD, TLP_CPLLK, TLP_CPLDLK});
    endfunction
    
    // Check if TLP has data
    function bit has_data();
        return (tlp_fmt inside {TLP_FMT_3DW_D, TLP_FMT_4DW_D});
    endfunction
    
    // Check if TLP is 64-bit
    function bit is_64bit();
        return (tlp_fmt inside {TLP_FMT_4DW_ND, TLP_FMT_4DW_D});
    endfunction
    
    // Get actual length in DW
    function int get_length_dw();
        return (length == 0) ? 1024 : length;
    endfunction
    
    // Get payload size in bytes
    function int get_payload_bytes();
        int dw_count = get_length_dw();
        int total_bytes = dw_count * 4;
        int first_be_bytes = $countones(first_be);
        int last_be_bytes = (dw_count > 1) ? $countones(last_be) : 0;
        
        if (dw_count == 1)
            return first_be_bytes;
        else
            return (dw_count - 2) * 4 + first_be_bytes + last_be_bytes;
    endfunction
    
    // Calculate header size in DW
    function int get_header_size_dw();
        if (tlp_fmt inside {TLP_FMT_3DW_ND, TLP_FMT_3DW_D})
            return 3;
        else
            return 4;
    endfunction
    
    // Build TLP header (3 or 4 DW)
    function void build_tlp_header(output bit [31:0] header[]);
        int hdr_size = get_header_size_dw();
        header = new[hdr_size];
        
        // DW0: Fmt, Type, TC, Attr, Length
        header[0] = {tlp_fmt, tlp_type[4:0], 1'b0, tc, ln, th, td, ep, attr, at, length};
        
        // DW1: Depends on TLP type
        if (is_completion()) begin
            header[1] = {completer_id, cpl_status, bcm, byte_count};
        end else begin
            header[1] = {requester_id, tag[7:0], last_be, first_be};
        end
        
        // DW2/3: Address or Completion lower
        if (is_completion()) begin
            header[2] = {requester_id, tag[7:0], 1'b0, lower_addr};
        end else if (is_64bit()) begin
            header[2] = address[63:32];
            header[3] = {address[31:2], 2'b00};
        end else begin
            header[2] = {address[31:2], 2'b00};
        end
    endfunction
    
    // Build full TLP packet
    function void build_tlp_packet(output bit [31:0] packet[]);
        bit [31:0] header[];
        int pkt_size;
        
        build_tlp_header(header);
        
        pkt_size = header.size() + payload.size();
        if (td) pkt_size++;  // ECRC
        
        packet = new[pkt_size];
        
        // Copy header
        foreach (header[i])
            packet[i] = header[i];
        
        // Copy payload
        foreach (payload[i])
            packet[header.size() + i] = payload[i];
        
        // Add ECRC
        if (td)
            packet[pkt_size-1] = ecrc;
    endfunction
    
    // Build DLLP packet
    function void build_dllp_packet(output bit [31:0] dllp_data);
        case (dllp_type)
            DLLP_ACK, DLLP_NAK: begin
                dllp_data = {4'h0, ack_nak_seq_num, 16'h0};
            end
            DLLP_INITFC1_P, DLLP_INITFC1_NP, DLLP_INITFC1_CPL,
            DLLP_INITFC2_P, DLLP_INITFC2_NP, DLLP_INITFC2_CPL,
            DLLP_UPDATEFC_P, DLLP_UPDATEFC_NP, DLLP_UPDATEFC_CPL: begin
                dllp_data = {fc_hdr_scale, fc_hdr_credits, fc_data_scale, fc_data_credits};
            end
            DLLP_PM_ENTER_L1, DLLP_PM_ENTER_L23, DLLP_PM_REQ_L1, DLLP_PM_REQ_ACK: begin
                dllp_data = {24'h0, pm_data};
            end
            default: begin
                dllp_data = 32'h0;
            end
        endcase
    endfunction
    
    // Parse TLP header
    function void parse_tlp_header(bit [31:0] header[]);
        // DW0
        tlp_fmt = tlp_fmt_e'(header[0][31:29]);
        tlp_type = tlp_type_e'(header[0][28:24]);
        tc = header[0][22:20];
        ln = header[0][19];
        th = header[0][18];
        td = header[0][17];
        ep = header[0][16];
        attr = header[0][13:12];
        at = header[0][11:10];
        length = header[0][9:0];
        
        // DW1
        if (is_completion()) begin
            completer_id = header[1][31:16];
            cpl_status = cpl_status_e'(header[1][15:13]);
            bcm = header[1][12];
            byte_count = header[1][11:0];
        end else begin
            requester_id = header[1][31:16];
            tag[7:0] = header[1][15:8];
            last_be = header[1][7:4];
            first_be = header[1][3:0];
        end
        
        // DW2/3
        if (is_completion()) begin
            requester_id = header[2][31:16];
            tag[7:0] = header[2][15:8];
            lower_addr = header[2][6:0];
        end else if (is_64bit()) begin
            address[63:32] = header[2];
            address[31:2] = header[3][31:2];
            address[1:0] = 2'b00;
            addr_type_64bit = 1;
        end else begin
            address[63:32] = 32'h0;
            address[31:2] = header[2][31:2];
            address[1:0] = 2'b00;
            addr_type_64bit = 0;
        end
    endfunction
    
    // Calculate ECRC
    function bit [31:0] calculate_ecrc();
        bit [31:0] packet[];
        bit [31:0] crc;
        
        build_tlp_packet(packet);
        
        // CRC-32 calculation (simplified - real implementation needs proper CRC)
        crc = 32'hFFFFFFFF;
        foreach (packet[i]) begin
            if (i < packet.size() - 1) begin  // Exclude ECRC position
                crc = crc ^ packet[i];
                // Polynomial division would go here
            end
        end
        
        return ~crc;
    endfunction
    
    // Create completion for this request
    function pcie_transaction create_completion(cpl_status_e status = CPL_SC, 
                                                bit [31:0] data[$] = {});
        pcie_transaction cpl = new();
        
        cpl.trans_type = PCIE_TLP;
        cpl.is_response = 1;
        cpl.cpl_status = status;
        cpl.completer_id = this.completer_id;
        cpl.requester_id = this.requester_id;
        cpl.tag = this.tag;
        cpl.tc = this.tc;
        cpl.attr = this.attr;
        
        if (data.size() > 0) begin
            cpl.tlp_type = TLP_CPLD;
            cpl.tlp_fmt = TLP_FMT_3DW_D;
            cpl.payload = new[data.size()];
            foreach (data[i]) begin
                cpl.payload[i] = data[i];
            end
            cpl.length = data.size();
            cpl.byte_count = data.size() * 4;
        end else begin
            cpl.tlp_type = TLP_CPL;
            cpl.tlp_fmt = TLP_FMT_3DW_ND;
            cpl.byte_count = 0;
        end
        
        cpl.lower_addr = this.address[6:0];
        
        return cpl;
    endfunction
    
    // Print transaction
    function void print_transaction(string prefix = "");
        string msg;
        
        msg = $sformatf("%s Transaction: %s", prefix, trans_type.name());
        
        if (trans_type == PCIE_TLP) begin
            msg = {msg, $sformatf("\n  TLP Type: %s, Fmt: %s", tlp_type.name(), tlp_fmt.name())};
            msg = {msg, $sformatf("\n  TC: %0d, TD: %0d, EP: %0d", tc, td, ep)};
            msg = {msg, $sformatf("\n  Length: %0d DW (%0d bytes)", get_length_dw(), get_payload_bytes())};
            msg = {msg, $sformatf("\n  Req ID: %04X, Tag: %03X", requester_id, tag)};
            
            if (!is_completion()) begin
                msg = {msg, $sformatf("\n  Address: %016X", address)};
                msg = {msg, $sformatf("\n  First BE: %04b, Last BE: %04b", first_be, last_be)};
            end else begin
                msg = {msg, $sformatf("\n  Cpl ID: %04X, Status: %s", completer_id, cpl_status.name())};
                msg = {msg, $sformatf("\n  Byte Count: %0d, Lower Addr: %02X", byte_count, lower_addr)};
            end
        end else if (trans_type == PCIE_DLLP) begin
            msg = {msg, $sformatf("\n  DLLP Type: %s", dllp_type.name())};
            if (dllp_type inside {DLLP_ACK, DLLP_NAK})
                msg = {msg, $sformatf("\n  Seq Num: %0d", ack_nak_seq_num)};
        end else if (trans_type == PCIE_ORDERED_SET) begin
            msg = {msg, $sformatf("\n  Ordered Set: %s", os_type.name())};
        end
        
        `uvm_info("TXN", msg, UVM_MEDIUM)
    endfunction
    
    // Compare transactions
    function bit compare_trans(pcie_transaction rhs);
        if (this.trans_type != rhs.trans_type) return 0;
        
        if (trans_type == PCIE_TLP) begin
            if (this.tlp_type != rhs.tlp_type) return 0;
            if (this.requester_id != rhs.requester_id) return 0;
            if (this.tag != rhs.tag) return 0;
            if (this.address != rhs.address) return 0;
            if (this.length != rhs.length) return 0;
            
            if (has_data()) begin
                if (this.payload.size() != rhs.payload.size()) return 0;
                foreach (this.payload[i])
                    if (this.payload[i] != rhs.payload[i]) return 0;
            end
        end
        
        return 1;
    endfunction
    
endclass
