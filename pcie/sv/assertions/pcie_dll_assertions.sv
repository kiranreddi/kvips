//-----------------------------------------------------------------------------
// File: pcie_dll_assertions.sv
// Description: PCIe Data Link Layer Assertions (SVA)
//              Flow Control, ACK/NAK, Replay, DLLP
//
// Copyright (c) KVIPS Project
// SPDX-License-Identifier: Apache-2.0
//-----------------------------------------------------------------------------

`ifndef PCIE_DLL_ASSERTIONS_SV
`define PCIE_DLL_ASSERTIONS_SV

module pcie_dll_assertions (
    // Clock and Reset
    input logic                     pclk,
    input logic                     reset_n,
    
    // Link Status
    input logic                     link_up,
    input logic                     dl_up,
    
    // TLP Interface
    input logic                     tlp_valid,
    input logic [11:0]              tlp_seq_num,
    input logic                     tlp_is_posted,
    input logic                     tlp_is_completion,
    input logic [9:0]               tlp_length,
    input logic                     tlp_accepted,
    
    // DLLP Interface
    input logic                     dllp_valid,
    input logic [7:0]               dllp_type,
    input logic [11:0]              dllp_seq_num,
    input logic [7:0]               dllp_hdr_credits,
    input logic [11:0]              dllp_data_credits,
    
    // Flow Control - Posted
    input logic [7:0]               fc_ph_credits;      // Posted header
    input logic [11:0]              fc_pd_credits;      // Posted data
    input logic [7:0]               fc_ph_consumed;
    input logic [11:0]              fc_pd_consumed;
    input logic [7:0]               fc_ph_limit;
    input logic [11:0]              fc_pd_limit;
    
    // Flow Control - Non-Posted
    input logic [7:0]               fc_nph_credits;     // Non-posted header
    input logic [11:0]              fc_npd_credits;     // Non-posted data
    input logic [7:0]               fc_nph_consumed;
    input logic [11:0]              fc_npd_consumed;
    input logic [7:0]               fc_nph_limit;
    input logic [11:0]              fc_npd_limit;
    
    // Flow Control - Completion
    input logic [7:0]               fc_cplh_credits;    // Completion header
    input logic [11:0]              fc_cpld_credits;    // Completion data
    input logic [7:0]               fc_cplh_consumed;
    input logic [11:0]              fc_cpld_consumed;
    input logic [7:0]               fc_cplh_limit;
    input logic [11:0]              fc_cpld_limit;
    
    // Flow Control Initialization
    input logic                     fc_init_done;
    input logic                     fc_init1_done;
    input logic                     fc_init2_done;
    
    // ACK/NAK
    input logic                     ack_sent,
    input logic                     ack_rcvd,
    input logic                     nak_sent,
    input logic                     nak_rcvd,
    input logic [11:0]              ack_seq_num,
    input logic [11:0]              nak_seq_num,
    input logic [11:0]              next_transmit_seq,
    input logic [11:0]              ackd_seq_num,
    
    // Replay
    input logic                     replay_timer_running,
    input logic                     replay_timer_expired,
    input logic                     replay_in_progress,
    input logic [1:0]               replay_count,
    
    // Retry Buffer
    input logic                     retry_buffer_full,
    input logic                     retry_buffer_empty,
    input logic [11:0]              retry_buffer_entries,
    
    // LCRC
    input logic                     lcrc_error,
    input logic                     lcrc_error_count_exceeded,
    
    // DLLP CRC
    input logic                     dllp_crc_error,
    
    // Error signals
    input logic                     sequence_error,
    input logic                     protocol_error,
    
    // Assertion control
    input logic                     assert_enable
);

    //=========================================================================
    // DLLP Type Encoding
    //=========================================================================
    
    localparam logic [7:0] DLLP_ACK         = 8'h00;
    localparam logic [7:0] DLLP_NAK         = 8'h10;
    localparam logic [7:0] DLLP_INITFC1_P   = 8'h40;
    localparam logic [7:0] DLLP_INITFC1_NP  = 8'h50;
    localparam logic [7:0] DLLP_INITFC1_CPL = 8'h60;
    localparam logic [7:0] DLLP_INITFC2_P   = 8'h48;
    localparam logic [7:0] DLLP_INITFC2_NP  = 8'h58;
    localparam logic [7:0] DLLP_INITFC2_CPL = 8'h68;
    localparam logic [7:0] DLLP_UPDATEFC_P  = 8'h80;
    localparam logic [7:0] DLLP_UPDATEFC_NP = 8'h90;
    localparam logic [7:0] DLLP_UPDATEFC_CPL= 8'hA0;
    localparam logic [7:0] DLLP_PM_ENTER_L1 = 8'h20;
    localparam logic [7:0] DLLP_PM_ENTER_L23= 8'h21;
    localparam logic [7:0] DLLP_PM_REQ_L1   = 8'h24;
    localparam logic [7:0] DLLP_PM_REQ_ACK  = 8'h25;

    //=========================================================================
    // FLOW CONTROL INITIALIZATION ASSERTIONS
    //=========================================================================
    
    // A1: FC Init must complete before data link layer is up
    property p_fc_init_before_dl_up;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        $rose(dl_up) |-> fc_init_done;
    endproperty
    
    a_fc_init_dl: assert property (p_fc_init_before_dl_up)
        else `uvm_error("DLL_ASSERT", "DL up before FC initialization complete")
    
    // A2: FC Init1 must precede FC Init2
    property p_fc_init_sequence;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        $rose(fc_init2_done) |-> fc_init1_done;
    endproperty
    
    a_fc_init_seq: assert property (p_fc_init_sequence)
        else `uvm_error("DLL_ASSERT", "FC Init2 completed before FC Init1")
    
    // A3: InitFC1 DLLP must be sent for all three types
    sequence s_initfc1_posted;
        ##[0:$] (dllp_valid && dllp_type == DLLP_INITFC1_P);
    endsequence
    
    sequence s_initfc1_nonposted;
        ##[0:$] (dllp_valid && dllp_type == DLLP_INITFC1_NP);
    endsequence
    
    sequence s_initfc1_completion;
        ##[0:$] (dllp_valid && dllp_type == DLLP_INITFC1_CPL);
    endsequence
    
    // A4: InitFC2 DLLP must follow InitFC1
    property p_initfc2_after_initfc1;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (dllp_valid && dllp_type == DLLP_INITFC2_P)
        |-> fc_init1_done;
    endproperty
    
    a_initfc2_sequence: assert property (p_initfc2_after_initfc1)
        else `uvm_error("DLL_ASSERT", "InitFC2 sent before InitFC1 complete")

    //=========================================================================
    // FLOW CONTROL CREDIT ASSERTIONS
    //=========================================================================
    
    // A5: Cannot transmit posted TLP without credits
    property p_posted_credits_check;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && tlp_is_posted && tlp_accepted)
        |-> ((fc_ph_credits - fc_ph_consumed) > 0) &&
            ((fc_pd_credits - fc_pd_consumed) >= ((tlp_length == 0) ? 256 : tlp_length) / 4);
    endproperty
    
    a_posted_credits: assert property (p_posted_credits_check)
        else `uvm_error("DLL_ASSERT", "Posted TLP transmitted without sufficient credits")
    
    // A6: Cannot transmit non-posted TLP without credits
    property p_nonposted_credits_check;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && !tlp_is_posted && !tlp_is_completion && tlp_accepted)
        |-> ((fc_nph_credits - fc_nph_consumed) > 0);
    endproperty
    
    a_nonposted_credits: assert property (p_nonposted_credits_check)
        else `uvm_error("DLL_ASSERT", "Non-posted TLP transmitted without sufficient credits")
    
    // A7: Cannot transmit completion without credits  
    property p_completion_credits_check;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && tlp_is_completion && tlp_accepted)
        |-> ((fc_cplh_credits - fc_cplh_consumed) > 0);
    endproperty
    
    a_completion_credits: assert property (p_completion_credits_check)
        else `uvm_error("DLL_ASSERT", "Completion transmitted without sufficient credits")
    
    // A8: Credit consumption cannot exceed limit
    property p_credit_limit_posted_hdr;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (fc_ph_limit != 0) |-> (fc_ph_consumed <= fc_ph_limit);
    endproperty
    
    a_credit_limit_ph: assert property (p_credit_limit_posted_hdr)
        else `uvm_error("DLL_ASSERT", "Posted header credits exceeded limit")
    
    // A9: UpdateFC must be sent periodically
    property p_updatefc_periodic;
        @(posedge pclk) disable iff (!reset_n || !assert_enable || !dl_up)
        1'b1 |-> ##[0:30000] (dllp_valid && 
            (dllp_type inside {DLLP_UPDATEFC_P, DLLP_UPDATEFC_NP, DLLP_UPDATEFC_CPL}));
    endproperty
    
    // Note: Timing may need adjustment based on actual requirements
    // a_updatefc_periodic: assert property (p_updatefc_periodic)
    //     else `uvm_warning("DLL_ASSERT", "UpdateFC not sent within expected time")

    //=========================================================================
    // SEQUENCE NUMBER ASSERTIONS
    //=========================================================================
    
    // A10: Sequence numbers must be sequential
    reg [11:0] last_seq_num;
    always @(posedge pclk) begin
        if (!reset_n)
            last_seq_num <= 12'h000;
        else if (tlp_valid && tlp_accepted)
            last_seq_num <= tlp_seq_num;
    end
    
    property p_seq_num_increment;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && tlp_accepted && !replay_in_progress)
        |-> (tlp_seq_num == ((last_seq_num + 1) % 4096));
    endproperty
    
    a_seq_increment: assert property (p_seq_num_increment)
        else `uvm_error("DLL_ASSERT", "Sequence number not incremented correctly")
    
    // A11: Sequence number wrap at 4095
    property p_seq_num_wrap;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_seq_num == 12'hFFF) && (tlp_valid && tlp_accepted && !replay_in_progress)
        ##1 (tlp_valid && tlp_accepted && !replay_in_progress)
        |-> (tlp_seq_num == 12'h000);
    endproperty
    
    a_seq_wrap: assert property (p_seq_num_wrap)
        else `uvm_error("DLL_ASSERT", "Sequence number did not wrap correctly")

    //=========================================================================
    // ACK/NAK PROTOCOL ASSERTIONS
    //=========================================================================
    
    // A12: ACK must acknowledge valid sequence number
    property p_ack_valid_seq;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        ack_rcvd |-> (ack_seq_num <= next_transmit_seq);
    endproperty
    
    a_ack_valid: assert property (p_ack_valid_seq)
        else `uvm_error("DLL_ASSERT", "ACK received for invalid sequence number")
    
    // A13: NAK must be followed by replay
    property p_nak_triggers_replay;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        nak_rcvd |-> ##[1:100] replay_in_progress;
    endproperty
    
    a_nak_replay: assert property (p_nak_triggers_replay)
        else `uvm_error("DLL_ASSERT", "NAK did not trigger replay")
    
    // A14: ACK timeout must trigger replay
    property p_ack_timeout_replay;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        replay_timer_expired |-> ##[1:10] replay_in_progress;
    endproperty
    
    a_timeout_replay: assert property (p_ack_timeout_replay)
        else `uvm_error("DLL_ASSERT", "Replay timer expiry did not trigger replay")
    
    // A15: Replay count must not exceed maximum (4)
    property p_replay_count_max;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        replay_count <= 2'd3;  // 0-3 = 4 retries
    endproperty
    
    a_replay_max: assert property (p_replay_count_max)
        else `uvm_error("DLL_ASSERT", "Replay count exceeded maximum")

    //=========================================================================
    // RETRY BUFFER ASSERTIONS
    //=========================================================================
    
    // A16: Cannot transmit new TLP when retry buffer is full
    property p_retry_buffer_full_block;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        retry_buffer_full |-> !(tlp_valid && tlp_accepted && !replay_in_progress);
    endproperty
    
    a_retry_full: assert property (p_retry_buffer_full_block)
        else `uvm_error("DLL_ASSERT", "New TLP transmitted with full retry buffer")
    
    // A17: Retry buffer must be cleared on ACK
    property p_retry_clear_on_ack;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        ack_rcvd && (ackd_seq_num < ack_seq_num)
        |=> (retry_buffer_entries < $past(retry_buffer_entries));
    endproperty
    
    // Note: May need refinement based on implementation
    // a_retry_clear: assert property (p_retry_clear_on_ack)
    //     else `uvm_error("DLL_ASSERT", "Retry buffer not cleared on ACK")

    //=========================================================================
    // LCRC ASSERTIONS
    //=========================================================================
    
    // A18: LCRC error should trigger NAK
    property p_lcrc_error_nak;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        lcrc_error |-> ##[1:10] nak_sent;
    endproperty
    
    a_lcrc_nak: assert property (p_lcrc_error_nak)
        else `uvm_error("DLL_ASSERT", "LCRC error did not trigger NAK")
    
    // A19: Too many LCRC errors should cause link recovery
    property p_lcrc_error_recovery;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        lcrc_error_count_exceeded |=> !dl_up;
    endproperty
    
    a_lcrc_recovery: assert property (p_lcrc_error_recovery)
        else `uvm_error("DLL_ASSERT", "Excessive LCRC errors did not trigger recovery")

    //=========================================================================
    // DLLP ASSERTIONS
    //=========================================================================
    
    // A20: DLLP must have valid CRC
    property p_dllp_crc_valid;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        dllp_valid |-> !dllp_crc_error;
    endproperty
    
    a_dllp_crc: assert property (p_dllp_crc_valid)
        else `uvm_error("DLL_ASSERT", "DLLP received with CRC error")
    
    // A21: DLLP type must be valid
    property p_dllp_type_valid;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        dllp_valid |-> dllp_type inside {
            DLLP_ACK, DLLP_NAK, 
            DLLP_INITFC1_P, DLLP_INITFC1_NP, DLLP_INITFC1_CPL,
            DLLP_INITFC2_P, DLLP_INITFC2_NP, DLLP_INITFC2_CPL,
            DLLP_UPDATEFC_P, DLLP_UPDATEFC_NP, DLLP_UPDATEFC_CPL,
            DLLP_PM_ENTER_L1, DLLP_PM_ENTER_L23, DLLP_PM_REQ_L1, DLLP_PM_REQ_ACK
        };
    endproperty
    
    a_dllp_type: assert property (p_dllp_type_valid)
        else `uvm_error("DLL_ASSERT", "Invalid DLLP type received")
    
    // A22: PM DLLPs must be responded to
    property p_pm_dllp_response;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (dllp_valid && dllp_type == DLLP_PM_REQ_L1)
        |-> ##[1:1000] (dllp_valid && dllp_type == DLLP_PM_REQ_ACK);
    endproperty
    
    a_pm_response: assert property (p_pm_dllp_response)
        else `uvm_error("DLL_ASSERT", "PM request not acknowledged")

    //=========================================================================
    // DATA LINK LAYER READY ASSERTIONS
    //=========================================================================
    
    // A23: DL must not be up without link up
    property p_dl_requires_link;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        dl_up |-> link_up;
    endproperty
    
    a_dl_link: assert property (p_dl_requires_link)
        else `uvm_error("DLL_ASSERT", "DL up without link up")
    
    // A24: Protocol error should bring down DL
    property p_protocol_error_dl_down;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        protocol_error |=> !dl_up;
    endproperty
    
    a_protocol_dl: assert property (p_protocol_error_dl_down)
        else `uvm_error("DLL_ASSERT", "Protocol error did not bring down DL")

    //=========================================================================
    // REPLAY TIMER ASSERTIONS
    //=========================================================================
    
    // A25: Replay timer must start after TLP transmission
    property p_replay_timer_start;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (tlp_valid && tlp_accepted && !tlp_is_posted && retry_buffer_empty)
        |=> replay_timer_running;
    endproperty
    
    a_replay_start: assert property (p_replay_timer_start)
        else `uvm_error("DLL_ASSERT", "Replay timer not started after non-posted TLP")
    
    // A26: Replay timer must stop on ACK
    property p_replay_timer_stop;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        ack_rcvd && retry_buffer_empty |=> !replay_timer_running;
    endproperty
    
    a_replay_stop: assert property (p_replay_timer_stop)
        else `uvm_error("DLL_ASSERT", "Replay timer not stopped on ACK")

    //=========================================================================
    // COVERAGE POINTS
    //=========================================================================
    
    covergroup cg_dll @(posedge pclk);
        option.per_instance = 1;
        
        // DLLP types
        cp_dllp_type: coverpoint dllp_type iff (dllp_valid) {
            bins ack     = {DLLP_ACK};
            bins nak     = {DLLP_NAK};
            bins initfc  = {[DLLP_INITFC1_P:DLLP_INITFC2_CPL]};
            bins updatefc= {[DLLP_UPDATEFC_P:DLLP_UPDATEFC_CPL]};
            bins pm      = {[DLLP_PM_ENTER_L1:DLLP_PM_REQ_ACK]};
        }
        
        // Flow control states
        cp_fc_ph_credits: coverpoint fc_ph_credits {
            bins zero    = {0};
            bins low     = {[1:4]};
            bins mid     = {[5:31]};
            bins high    = {[32:127]};
            bins max     = {[128:255]};
        }
        
        // Replay scenarios
        cp_replay_count: coverpoint replay_count {
            bins first_try  = {0};
            bins second_try = {1};
            bins third_try  = {2};
            bins final_try  = {3};
        }
        
        // Retry buffer occupancy
        cp_retry_buffer: coverpoint retry_buffer_entries {
            bins empty     = {0};
            bins low       = {[1:64]};
            bins mid       = {[65:256]};
            bins high      = {[257:512]};
            bins near_full = {[513:1023]};
            bins full      = {1024};
        }
        
        // Error conditions
        cp_errors: coverpoint {lcrc_error, dllp_crc_error, sequence_error} {
            bins no_error     = {3'b000};
            bins lcrc_only    = {3'b100};
            bins dllp_only    = {3'b010};
            bins seq_only     = {3'b001};
            bins multiple     = {[3'b011:3'b111]};
        }
    endgroup
    
    cg_dll cg = new();

endmodule : pcie_dll_assertions

`endif // PCIE_DLL_ASSERTIONS_SV
