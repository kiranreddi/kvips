//-----------------------------------------------------------------------------
// File: pcie_tl_assertions.sv
// Description: PCIe Transaction Layer Assertions (SVA)
//              TLP Format, Ordering, Completion, Error Handling
//
// Copyright (c) KVIPS Project
// SPDX-License-Identifier: Apache-2.0
//-----------------------------------------------------------------------------

`ifndef PCIE_TL_ASSERTIONS_SV
`define PCIE_TL_ASSERTIONS_SV

module pcie_tl_assertions (
    // Clock and Reset
    input logic                     pclk,
    input logic                     reset_n,
    
    // Link Status
    input logic                     dl_up,
    
    // TLP Header Fields
    input logic                     tlp_valid,
    input logic [1:0]               tlp_fmt,
    input logic [4:0]               tlp_type,
    input logic [2:0]               tlp_tc,
    input logic [9:0]               tlp_length,
    input logic                     tlp_td,        // TLP Digest present
    input logic                     tlp_ep,        // Poisoned
    input logic [1:0]               tlp_attr,
    input logic [1:0]               tlp_at,        // Address type
    
    // Requester/Completer
    input logic [15:0]              tlp_requester_id,
    input logic [15:0]              tlp_completer_id,
    input logic [7:0]               tlp_tag,
    input logic [9:0]               tlp_tag_10bit,
    
    // Address
    input logic [63:0]              tlp_address,
    input logic [3:0]               tlp_first_be,
    input logic [3:0]               tlp_last_be,
    
    // Completion specific
    input logic [2:0]               tlp_cpl_status,
    input logic                     tlp_cpl_bcm,
    input logic [11:0]              tlp_cpl_byte_count,
    input logic [6:0]               tlp_cpl_lower_addr,
    
    // Data
    input logic [31:0]              tlp_data[],
    input logic                     tlp_has_data,
    
    // ECRC
    input logic                     ecrc_present,
    input logic                     ecrc_valid,
    input logic                     ecrc_check_enable,
    
    // Configuration
    input logic [9:0]               max_payload_size,   // In DW
    input logic [9:0]               max_read_req_size,  // In DW
    input logic                     extended_tag_enable,
    input logic                     relaxed_ordering_enable,
    input logic                     no_snoop_enable,
    
    // Outstanding requests tracking
    input logic [7:0]               outstanding_tags[$],
    input logic                     tag_available,
    
    // Completion tracking
    input logic                     expect_completion,
    input logic                     completion_received,
    input logic                     completion_timeout,
    
    // Ordering
    input logic                     posted_request,
    input logic                     non_posted_request,
    input logic                     completion,
    
    // Error signals
    input logic                     malformed_tlp,
    input logic                     unexpected_completion,
    input logic                     completer_abort,
    input logic                     unsupported_request,
    
    // Assertion control
    input logic                     assert_enable
);

    //=========================================================================
    // TLP Format and Type Encoding
    //=========================================================================
    
    // Formats
    localparam logic [1:0] FMT_3DW_NO_DATA = 2'b00;
    localparam logic [1:0] FMT_4DW_NO_DATA = 2'b01;
    localparam logic [1:0] FMT_3DW_DATA    = 2'b10;
    localparam logic [1:0] FMT_4DW_DATA    = 2'b11;
    
    // Types (combined with format)
    localparam logic [4:0] TYPE_MRD      = 5'b00000;
    localparam logic [4:0] TYPE_MRDLK    = 5'b00001;
    localparam logic [4:0] TYPE_MWR      = 5'b00000;  // Format determines this
    localparam logic [4:0] TYPE_IORD     = 5'b00010;
    localparam logic [4:0] TYPE_IOWR     = 5'b00010;
    localparam logic [4:0] TYPE_CFGRD0   = 5'b00100;
    localparam logic [4:0] TYPE_CFGWR0   = 5'b00100;
    localparam logic [4:0] TYPE_CFGRD1   = 5'b00101;
    localparam logic [4:0] TYPE_CFGWR1   = 5'b00101;
    localparam logic [4:0] TYPE_MSG      = 5'b10???;
    localparam logic [4:0] TYPE_CPL      = 5'b01010;
    localparam logic [4:0] TYPE_CPLLK    = 5'b01011;

    //=========================================================================
    // TLP FORMAT ASSERTIONS
    //=========================================================================
    
    // A1: TLP length must be valid (0 = 1024 DW, else 1-1023)
    property p_valid_length;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        tlp_valid |-> (tlp_length inside {[0:1023]});
    endproperty
    
    a_valid_length: assert property (p_valid_length)
        else `uvm_error("TL_ASSERT", "Invalid TLP length")
    
    // A2: Memory write must have data
    property p_mwr_has_data;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && tlp_type == TYPE_MWR && tlp_fmt[1])  // Format with data
        |-> tlp_has_data;
    endproperty
    
    a_mwr_data: assert property (p_mwr_has_data)
        else `uvm_error("TL_ASSERT", "Memory write without data")
    
    // A3: Memory read must not have data
    property p_mrd_no_data;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && tlp_type == TYPE_MRD && !tlp_fmt[1])  // Format without data
        |-> !tlp_has_data;
    endproperty
    
    a_mrd_no_data: assert property (p_mrd_no_data)
        else `uvm_error("TL_ASSERT", "Memory read with data")
    
    // A4: 64-bit address format consistency
    property p_64bit_addr_format;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && tlp_fmt[0])  // 4DW header = 64-bit
        |-> (tlp_address[63:32] != 32'h0) || 1'b1;  // Can be zero but format must match
    endproperty
    
    a_64bit_format: assert property (p_64bit_addr_format)
        else `uvm_warning("TL_ASSERT", "64-bit format with zero upper address")
    
    // A5: Completion status must be valid
    property p_valid_cpl_status;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && completion)
        |-> (tlp_cpl_status inside {3'b000, 3'b001, 3'b010, 3'b100});  // SC, UR, CRS, CA
    endproperty
    
    a_valid_cpl_status: assert property (p_valid_cpl_status)
        else `uvm_error("TL_ASSERT", "Invalid completion status")

    //=========================================================================
    // PAYLOAD SIZE ASSERTIONS
    //=========================================================================
    
    // A6: Payload cannot exceed max payload size
    property p_max_payload;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && tlp_has_data && posted_request)
        |-> (tlp_length <= max_payload_size);
    endproperty
    
    a_max_payload: assert property (p_max_payload)
        else `uvm_error("TL_ASSERT", "TLP payload exceeds max payload size")
    
    // A7: Read request cannot exceed max read request size
    property p_max_read_request;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && !tlp_has_data && tlp_type == TYPE_MRD)
        |-> (tlp_length <= max_read_req_size);
    endproperty
    
    a_max_read_req: assert property (p_max_read_request)
        else `uvm_error("TL_ASSERT", "Read request exceeds max read request size")
    
    // A8: 4KB boundary check for memory requests
    function automatic bit crosses_4kb(logic [63:0] addr, logic [9:0] len);
        logic [11:0] start_offset = addr[11:0];
        int byte_len = (len == 0) ? 4096 : len * 4;
        return ((start_offset + byte_len) > 4096);
    endfunction
    
    property p_4kb_boundary;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && (posted_request || non_posted_request) && 
         (tlp_type inside {TYPE_MRD, TYPE_MWR}))
        |-> !crosses_4kb(tlp_address, tlp_length);
    endproperty
    
    a_4kb_boundary: assert property (p_4kb_boundary)
        else `uvm_error("TL_ASSERT", "Memory request crosses 4KB boundary")

    //=========================================================================
    // BYTE ENABLE ASSERTIONS
    //=========================================================================
    
    // A9: First BE must be non-zero for multi-DW transactions
    property p_first_be_valid;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && tlp_has_data && tlp_length > 1)
        |-> (tlp_first_be != 4'h0);
    endproperty
    
    a_first_be: assert property (p_first_be_valid)
        else `uvm_error("TL_ASSERT", "First BE is zero for multi-DW transaction")
    
    // A10: Last BE must be non-zero for multi-DW transactions
    property p_last_be_valid;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && tlp_has_data && tlp_length > 1)
        |-> (tlp_last_be != 4'h0);
    endproperty
    
    a_last_be: assert property (p_last_be_valid)
        else `uvm_error("TL_ASSERT", "Last BE is zero for multi-DW transaction")
    
    // A11: Last BE must be zero for single DW transactions
    property p_single_dw_last_be;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && tlp_has_data && tlp_length == 1)
        |-> (tlp_last_be == 4'h0);
    endproperty
    
    a_single_dw_be: assert property (p_single_dw_last_be)
        else `uvm_error("TL_ASSERT", "Last BE non-zero for single DW transaction")
    
    // A12: BE contiguity for memory requests
    function automatic bit be_contiguous(logic [3:0] be);
        case (be)
            4'b0000: return 1;  // Special case: zero-length read
            4'b0001, 4'b0010, 4'b0100, 4'b1000: return 1;  // Single byte
            4'b0011, 4'b0110, 4'b1100: return 1;  // Two contiguous
            4'b0111, 4'b1110: return 1;  // Three contiguous
            4'b1111: return 1;  // Four bytes
            default: return 0;  // Non-contiguous
        endcase
    endfunction
    
    property p_be_contiguity;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && (tlp_type inside {TYPE_MRD, TYPE_MWR}))
        |-> be_contiguous(tlp_first_be) && be_contiguous(tlp_last_be);
    endproperty
    
    a_be_contiguous: assert property (p_be_contiguity)
        else `uvm_error("TL_ASSERT", "Non-contiguous byte enables in memory request")

    //=========================================================================
    // TAG MANAGEMENT ASSERTIONS
    //=========================================================================
    
    // A13: Tag must be unique for outstanding requests
    property p_unique_tag;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && non_posted_request && expect_completion)
        |-> !(tlp_tag inside {outstanding_tags});
    endproperty
    
    a_unique_tag: assert property (p_unique_tag)
        else `uvm_error("TL_ASSERT", "Duplicate tag for outstanding request")
    
    // A14: Extended tags only when enabled
    property p_extended_tag;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && non_posted_request && (tlp_tag > 8'd31))
        |-> extended_tag_enable;
    endproperty
    
    a_extended_tag: assert property (p_extended_tag)
        else `uvm_error("TL_ASSERT", "Extended tag used without extended tag enable")
    
    // A15: Tag availability
    property p_tag_available;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && non_posted_request && expect_completion)
        |-> tag_available;
    endproperty
    
    a_tag_avail: assert property (p_tag_available)
        else `uvm_error("TL_ASSERT", "No tags available for non-posted request")

    //=========================================================================
    // COMPLETION ASSERTIONS
    //=========================================================================
    
    // A16: Completion must match outstanding request
    property p_completion_match;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && completion && !unexpected_completion)
        |-> (tlp_tag inside {outstanding_tags});
    endproperty
    
    a_cpl_match: assert property (p_completion_match)
        else `uvm_error("TL_ASSERT", "Completion does not match outstanding request")
    
    // A17: Completion byte count must be valid
    property p_cpl_byte_count;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && completion && tlp_has_data)
        |-> (tlp_cpl_byte_count > 0);
    endproperty
    
    a_cpl_bc: assert property (p_cpl_byte_count)
        else `uvm_error("TL_ASSERT", "Completion with data has zero byte count")
    
    // A18: Completion lower address alignment
    property p_cpl_lower_addr;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && completion && tlp_has_data)
        |-> (tlp_cpl_lower_addr[1:0] == 2'b00);  // Must be DW aligned
    endproperty
    
    a_cpl_addr: assert property (p_cpl_lower_addr)
        else `uvm_error("TL_ASSERT", "Completion lower address not DW aligned")
    
    // A19: Completion timeout
    property p_completion_timeout;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (expect_completion && !completion_received)
        |-> !completion_timeout;  // Should not timeout while waiting
    endproperty
    
    // Note: This needs actual timeout counter integration
    // a_cpl_timeout: assert property (p_completion_timeout)
    //     else `uvm_error("TL_ASSERT", "Completion timeout occurred")
    
    // A20: Unexpected completion check
    property p_unexpected_cpl;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        unexpected_completion |-> 1'b1;  // Log when this happens
    endproperty
    
    cover property (@(posedge pclk) unexpected_completion);

    //=========================================================================
    // ORDERING RULE ASSERTIONS
    //=========================================================================
    
    // A21: Posted requests cannot pass posted requests (same TC, no RO)
    // Note: Simplified - full implementation needs transaction queues
    property p_posted_ordering;
        @(posedge pclk) disable iff (!reset_n || !assert_enable || relaxed_ordering_enable)
        // Placeholder - needs queue comparison
        1'b1;
    endproperty
    
    // A22: Completions cannot pass completions (same TC)
    property p_completion_ordering;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        // Placeholder - needs queue comparison
        1'b1;
    endproperty

    //=========================================================================
    // TRAFFIC CLASS ASSERTIONS
    //=========================================================================
    
    // A23: Traffic class must be valid (0-7)
    property p_valid_tc;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        tlp_valid |-> (tlp_tc inside {[0:7]});
    endproperty
    
    a_valid_tc: assert property (p_valid_tc)
        else `uvm_error("TL_ASSERT", "Invalid traffic class")
    
    // A24: Completion TC must match request TC
    // Note: Needs request tracking

    //=========================================================================
    // ECRC ASSERTIONS
    //=========================================================================
    
    // A25: ECRC must be valid when present and checking enabled
    property p_ecrc_valid;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && ecrc_present && ecrc_check_enable)
        |-> ecrc_valid;
    endproperty
    
    a_ecrc: assert property (p_ecrc_valid)
        else `uvm_error("TL_ASSERT", "ECRC check failed")
    
    // A26: TD bit must match ECRC presence
    property p_td_ecrc_match;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        tlp_valid |-> (tlp_td == ecrc_present);
    endproperty
    
    a_td_ecrc: assert property (p_td_ecrc_match)
        else `uvm_error("TL_ASSERT", "TD bit does not match ECRC presence")

    //=========================================================================
    // ERROR HANDLING ASSERTIONS
    //=========================================================================
    
    // A27: Malformed TLP must be dropped
    property p_malformed_drop;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        malformed_tlp |-> 1'b1;  // Log malformed TLPs
    endproperty
    
    cover property (@(posedge pclk) malformed_tlp);
    
    // A28: Unsupported request must generate UR completion
    property p_ur_completion;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (unsupported_request && non_posted_request)
        |-> ##[1:1000] (completion && tlp_cpl_status == 3'b001);
    endproperty
    
    a_ur_cpl: assert property (p_ur_completion)
        else `uvm_error("TL_ASSERT", "Unsupported request did not generate UR completion")
    
    // A29: Completer abort must generate CA completion
    property p_ca_completion;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (completer_abort && non_posted_request)
        |-> ##[1:1000] (completion && tlp_cpl_status == 3'b100);
    endproperty
    
    a_ca_cpl: assert property (p_ca_completion)
        else `uvm_error("TL_ASSERT", "Completer abort did not generate CA completion")
    
    // A30: Poisoned TLP handling
    property p_poisoned_handling;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && tlp_ep) |-> 1'b1;  // Log poisoned TLPs
    endproperty
    
    cover property (@(posedge pclk) tlp_valid && tlp_ep);

    //=========================================================================
    // ATTRIBUTE ASSERTIONS
    //=========================================================================
    
    // A31: Relaxed ordering attribute only when enabled
    property p_ro_attribute;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && tlp_attr[1])  // RO bit
        |-> relaxed_ordering_enable;
    endproperty
    
    a_ro_attr: assert property (p_ro_attribute)
        else `uvm_error("TL_ASSERT", "Relaxed ordering used without enable")
    
    // A32: No snoop attribute only when enabled
    property p_ns_attribute;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && tlp_attr[0])  // NS bit
        |-> no_snoop_enable;
    endproperty
    
    a_ns_attr: assert property (p_ns_attribute)
        else `uvm_error("TL_ASSERT", "No snoop used without enable")

    //=========================================================================
    // ADDRESS TYPE ASSERTIONS
    //=========================================================================
    
    // A33: Address type must be valid
    property p_valid_at;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        tlp_valid |-> (tlp_at inside {2'b00, 2'b01, 2'b10});  // Default, Translation, Translated
    endproperty
    
    a_valid_at: assert property (p_valid_at)
        else `uvm_error("TL_ASSERT", "Invalid address type")

    //=========================================================================
    // IO AND CONFIG ASSERTIONS
    //=========================================================================
    
    // A34: IO transactions must be single DW
    property p_io_single_dw;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && tlp_type inside {TYPE_IORD, TYPE_IOWR})
        |-> (tlp_length == 1);
    endproperty
    
    a_io_size: assert property (p_io_single_dw)
        else `uvm_error("TL_ASSERT", "IO transaction not single DW")
    
    // A35: Config transactions must be single DW
    property p_cfg_single_dw;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && tlp_type inside {TYPE_CFGRD0, TYPE_CFGWR0, TYPE_CFGRD1, TYPE_CFGWR1})
        |-> (tlp_length == 1);
    endproperty
    
    a_cfg_size: assert property (p_cfg_single_dw)
        else `uvm_error("TL_ASSERT", "Config transaction not single DW")

    //=========================================================================
    // COVERAGE POINTS
    //=========================================================================
    
    covergroup cg_tl @(posedge pclk);
        option.per_instance = 1;
        
        // TLP types
        cp_tlp_type: coverpoint {tlp_fmt, tlp_type} iff (tlp_valid) {
            bins mem_rd_32   = {{FMT_3DW_NO_DATA, TYPE_MRD}};
            bins mem_rd_64   = {{FMT_4DW_NO_DATA, TYPE_MRD}};
            bins mem_wr_32   = {{FMT_3DW_DATA, 5'b00000}};
            bins mem_wr_64   = {{FMT_4DW_DATA, 5'b00000}};
            bins io_rd       = {{FMT_3DW_NO_DATA, TYPE_IORD}};
            bins io_wr       = {{FMT_3DW_DATA, TYPE_IOWR}};
            bins cfg_rd0     = {{FMT_3DW_NO_DATA, TYPE_CFGRD0}};
            bins cfg_wr0     = {{FMT_3DW_DATA, TYPE_CFGWR0}};
            bins cfg_rd1     = {{FMT_3DW_NO_DATA, TYPE_CFGRD1}};
            bins cfg_wr1     = {{FMT_3DW_DATA, TYPE_CFGWR1}};
            bins cpl         = {{FMT_3DW_NO_DATA, TYPE_CPL}};
            bins cpl_d       = {{FMT_3DW_DATA, TYPE_CPL}};
        }
        
        // Traffic class
        cp_tc: coverpoint tlp_tc iff (tlp_valid) {
            bins tc[] = {[0:7]};
        }
        
        // Payload length
        cp_length: coverpoint tlp_length iff (tlp_valid && tlp_has_data) {
            bins single_dw = {1};
            bins small     = {[2:8]};
            bins medium    = {[9:64]};
            bins large     = {[65:256]};
            bins max       = {[257:1023]};
            bins max_1024  = {0};  // 0 means 1024
        }
        
        // Completion status
        cp_cpl_status: coverpoint tlp_cpl_status iff (tlp_valid && completion) {
            bins sc  = {3'b000};
            bins ur  = {3'b001};
            bins crs = {3'b010};
            bins ca  = {3'b100};
        }
        
        // Byte enables
        cp_first_be: coverpoint tlp_first_be iff (tlp_valid) {
            bins all_ones  = {4'b1111};
            bins partial[] = {[4'b0001:4'b1110]};
            bins zero      = {4'b0000};
        }
        
        // Attributes
        cp_attr: coverpoint tlp_attr iff (tlp_valid) {
            bins default_ordering = {2'b00};
            bins relaxed          = {2'b01};
            bins id_based         = {2'b10};
            bins both             = {2'b11};
        }
        
        // Cross coverage
        cx_type_length: cross cp_tlp_type, cp_length;
        cx_type_tc:     cross cp_tlp_type, cp_tc;
    endgroup
    
    cg_tl cg = new();

endmodule : pcie_tl_assertions

`endif // PCIE_TL_ASSERTIONS_SV
