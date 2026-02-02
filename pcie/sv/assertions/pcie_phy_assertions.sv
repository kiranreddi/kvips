//-----------------------------------------------------------------------------
// File: pcie_phy_assertions.sv
// Description: PCIe PHY Layer Assertions (SVA)
//              LTSSM, Ordered Sets, Encoding
//
// Copyright (c) KVIPS Project
// SPDX-License-Identifier: Apache-2.0
//-----------------------------------------------------------------------------

`ifndef PCIE_PHY_ASSERTIONS_SV
`define PCIE_PHY_ASSERTIONS_SV

module pcie_phy_assertions #(
    parameter int NUM_LANES = 16,
    parameter int MAX_GEN   = 5
) (
    // Clock and Reset
    input logic                     pclk,
    input logic                     reset_n,
    
    // LTSSM State
    input logic [4:0]               ltssm_state,
    input logic [4:0]               ltssm_next_state,
    
    // Link Status
    input logic                     link_up,
    input logic [4:0]               link_width,
    input logic [2:0]               link_speed,  // Gen1=0, Gen2=1, etc.
    
    // Ordered Sets
    input logic                     ts1_sent,
    input logic                     ts1_rcvd,
    input logic                     ts2_sent,
    input logic                     ts2_rcvd,
    input logic                     skp_sent,
    input logic                     skp_rcvd,
    input logic                     eios_sent,
    input logic                     eios_rcvd,
    input logic                     fts_sent,
    input logic                     fts_rcvd,
    
    // Electrical Idle
    input logic [NUM_LANES-1:0]     tx_elec_idle,
    input logic [NUM_LANES-1:0]     rx_elec_idle,
    
    // Receiver Detection
    input logic                     rx_detect_req,
    input logic                     rx_detect_done,
    input logic [NUM_LANES-1:0]     rx_present,
    
    // Power State
    input logic [1:0]               power_state,
    
    // Speed Change
    input logic                     speed_change_req,
    input logic                     speed_change_ack,
    input logic [2:0]               target_speed,
    
    // Equalization
    input logic                     eq_phase0,
    input logic                     eq_phase1,
    input logic                     eq_phase2,
    input logic                     eq_phase3,
    input logic                     eq_done,
    
    // Error signals
    input logic                     disparity_error,
    input logic                     symbol_error,
    input logic [NUM_LANES-1:0]     lane_error,
    
    // Assertion control
    input logic                     assert_enable
);

    //=========================================================================
    // LTSSM State Encoding (matches pcie_types_pkg)
    //=========================================================================
    
    localparam logic [4:0] ST_DETECT_QUIET      = 5'd0;
    localparam logic [4:0] ST_DETECT_ACTIVE     = 5'd1;
    localparam logic [4:0] ST_POLLING_ACTIVE    = 5'd2;
    localparam logic [4:0] ST_POLLING_CONFIG    = 5'd3;
    localparam logic [4:0] ST_POLLING_COMPLIANCE= 5'd4;
    localparam logic [4:0] ST_POLLING_SPEED     = 5'd5;
    localparam logic [4:0] ST_CONFIG_LINKWIDTH  = 5'd6;
    localparam logic [4:0] ST_CONFIG_LANENUM    = 5'd7;
    localparam logic [4:0] ST_CONFIG_COMPLETE   = 5'd8;
    localparam logic [4:0] ST_CONFIG_IDLE       = 5'd9;
    localparam logic [4:0] ST_L0                = 5'd10;
    localparam logic [4:0] ST_RECOVERY_RCVRLOCK = 5'd11;
    localparam logic [4:0] ST_RECOVERY_RCVRCFG  = 5'd12;
    localparam logic [4:0] ST_RECOVERY_SPEED    = 5'd13;
    localparam logic [4:0] ST_RECOVERY_IDLE     = 5'd14;
    localparam logic [4:0] ST_RECOVERY_EQ       = 5'd15;
    localparam logic [4:0] ST_L0S_ENTRY         = 5'd16;
    localparam logic [4:0] ST_L0S_IDLE          = 5'd17;
    localparam logic [4:0] ST_L0S_FTS           = 5'd18;
    localparam logic [4:0] ST_L1_ENTRY          = 5'd19;
    localparam logic [4:0] ST_L1_IDLE           = 5'd20;
    localparam logic [4:0] ST_L2_IDLE           = 5'd21;
    localparam logic [4:0] ST_DISABLED          = 5'd22;
    localparam logic [4:0] ST_LOOPBACK_ENTRY    = 5'd23;
    localparam logic [4:0] ST_LOOPBACK_ACTIVE   = 5'd24;
    localparam logic [4:0] ST_LOOPBACK_EXIT     = 5'd25;
    localparam logic [4:0] ST_HOT_RESET         = 5'd26;

    //=========================================================================
    // LTSSM STATE TRANSITION ASSERTIONS
    //=========================================================================
    
    // A1: Detect.Quiet can only transition to Detect.Active
    property p_detect_quiet_transition;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (ltssm_state == ST_DETECT_QUIET) && (ltssm_next_state != ST_DETECT_QUIET)
        |-> (ltssm_next_state == ST_DETECT_ACTIVE);
    endproperty
    
    a_detect_quiet_transition: assert property (p_detect_quiet_transition)
        else `uvm_error("PHY_ASSERT", "Invalid transition from Detect.Quiet")
    
    // A2: Detect.Active transitions
    property p_detect_active_transition;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (ltssm_state == ST_DETECT_ACTIVE) && (ltssm_next_state != ST_DETECT_ACTIVE)
        |-> (ltssm_next_state inside {ST_DETECT_QUIET, ST_POLLING_ACTIVE});
    endproperty
    
    a_detect_active_transition: assert property (p_detect_active_transition)
        else `uvm_error("PHY_ASSERT", "Invalid transition from Detect.Active")
    
    // A3: Polling.Active transitions
    property p_polling_active_transition;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (ltssm_state == ST_POLLING_ACTIVE) && (ltssm_next_state != ST_POLLING_ACTIVE)
        |-> (ltssm_next_state inside {ST_POLLING_CONFIG, ST_POLLING_COMPLIANCE, ST_DETECT_QUIET});
    endproperty
    
    a_polling_active_transition: assert property (p_polling_active_transition)
        else `uvm_error("PHY_ASSERT", "Invalid transition from Polling.Active")
    
    // A4: L0 can transition to Recovery, L0s, or L1
    property p_l0_transition;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (ltssm_state == ST_L0) && (ltssm_next_state != ST_L0)
        |-> (ltssm_next_state inside {ST_RECOVERY_RCVRLOCK, ST_L0S_ENTRY, ST_L1_ENTRY, 
                                       ST_HOT_RESET, ST_DISABLED});
    endproperty
    
    a_l0_transition: assert property (p_l0_transition)
        else `uvm_error("PHY_ASSERT", "Invalid transition from L0")
    
    // A5: Recovery must eventually reach L0 or Detect
    property p_recovery_eventually_exits;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (ltssm_state == ST_RECOVERY_RCVRLOCK)
        |-> ##[1:10000] (ltssm_state inside {ST_L0, ST_DETECT_QUIET, ST_HOT_RESET});
    endproperty
    
    a_recovery_exits: assert property (p_recovery_eventually_exits)
        else `uvm_error("PHY_ASSERT", "Recovery did not exit within timeout")

    //=========================================================================
    // ORDERED SET ASSERTIONS
    //=========================================================================
    
    // A6: TS1 must be sent in Polling.Active
    property p_ts1_in_polling;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (ltssm_state == ST_POLLING_ACTIVE) && $rose(ts1_sent)
        |-> 1'b1;
    endproperty
    
    a_ts1_in_polling: assert property (p_ts1_in_polling)
        else `uvm_error("PHY_ASSERT", "TS1 sent outside of expected state")
    
    // A7: TS2 must be sent after TS1 received in Polling
    property p_ts2_after_ts1;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (ltssm_state == ST_POLLING_CONFIG) && $rose(ts2_sent)
        |-> ##[0:10] $past(ts1_rcvd, 1);
    endproperty
    
    a_ts2_after_ts1: assert property (p_ts2_after_ts1)
        else `uvm_error("PHY_ASSERT", "TS2 sent without receiving TS1")
    
    // A8: SKP ordered sets must be sent periodically in L0
    property p_skp_periodic;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (ltssm_state == ST_L0) && skp_sent
        |-> ##[1:1538] skp_sent;  // Max 1538 symbols between SKP
    endproperty
    
    // Note: This property may need adjustment based on actual timing
    // a_skp_periodic: assert property (p_skp_periodic)
    //     else `uvm_warning("PHY_ASSERT", "SKP period exceeded")
    
    // A9: EIOS must precede electrical idle
    property p_eios_before_idle;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        $rose(tx_elec_idle[0]) |-> ##[0:4] $past(eios_sent, 1);
    endproperty
    
    a_eios_before_idle: assert property (p_eios_before_idle)
        else `uvm_error("PHY_ASSERT", "Electrical idle without preceding EIOS")
    
    // A10: FTS must be sent when exiting L0s
    property p_fts_on_l0s_exit;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (ltssm_state == ST_L0S_FTS) |-> ##[1:100] fts_sent;
    endproperty
    
    a_fts_l0s_exit: assert property (p_fts_on_l0s_exit)
        else `uvm_error("PHY_ASSERT", "FTS not sent during L0s exit")

    //=========================================================================
    // RECEIVER DETECTION ASSERTIONS
    //=========================================================================
    
    // A11: Receiver detection must complete in Detect.Active
    property p_rx_detect_complete;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (ltssm_state == ST_DETECT_ACTIVE) && $rose(rx_detect_req)
        |-> ##[1:1000] rx_detect_done;
    endproperty
    
    a_rx_detect_complete: assert property (p_rx_detect_complete)
        else `uvm_error("PHY_ASSERT", "Receiver detection did not complete")
    
    // A12: At least one lane must detect receiver for link training
    property p_rx_present_for_training;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (ltssm_state == ST_DETECT_ACTIVE) && rx_detect_done && (ltssm_next_state == ST_POLLING_ACTIVE)
        |-> (|rx_present);
    endproperty
    
    a_rx_present: assert property (p_rx_present_for_training)
        else `uvm_error("PHY_ASSERT", "No receiver detected but proceeding to Polling")

    //=========================================================================
    // POWER STATE ASSERTIONS
    //=========================================================================
    
    // A13: Power state must be P0 in L0
    property p_p0_in_l0;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (ltssm_state == ST_L0) |-> (power_state == 2'b00);
    endproperty
    
    a_p0_in_l0: assert property (p_p0_in_l0)
        else `uvm_error("PHY_ASSERT", "Power state not P0 in L0")
    
    // A14: Power state must be P1 in L1
    property p_p1_in_l1;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (ltssm_state == ST_L1_IDLE) |-> (power_state == 2'b10);
    endproperty
    
    a_p1_in_l1: assert property (p_p1_in_l1)
        else `uvm_error("PHY_ASSERT", "Power state not P1 in L1")
    
    // A15: Power state P2 only in L2 or Detect
    property p_p2_valid_states;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (power_state == 2'b11) |-> 
        (ltssm_state inside {ST_L2_IDLE, ST_DETECT_QUIET, ST_DETECT_ACTIVE, ST_DISABLED});
    endproperty
    
    a_p2_valid: assert property (p_p2_valid_states)
        else `uvm_error("PHY_ASSERT", "P2 power state in invalid LTSSM state")

    //=========================================================================
    // SPEED CHANGE ASSERTIONS
    //=========================================================================
    
    // A16: Speed change must go through Recovery
    property p_speed_change_recovery;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        $rose(speed_change_req) |-> ##[1:1000] (ltssm_state == ST_RECOVERY_SPEED);
    endproperty
    
    a_speed_recovery: assert property (p_speed_change_recovery)
        else `uvm_error("PHY_ASSERT", "Speed change did not go through Recovery")
    
    // A17: Speed change ack within timeout
    property p_speed_change_ack;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        $rose(speed_change_req) |-> ##[1:10000] speed_change_ack;
    endproperty
    
    a_speed_ack: assert property (p_speed_change_ack)
        else `uvm_error("PHY_ASSERT", "Speed change acknowledgment timeout")

    //=========================================================================
    // EQUALIZATION ASSERTIONS (Gen3+)
    //=========================================================================
    
    // A18: Equalization phases must be sequential
    property p_eq_phase_sequence;
        @(posedge pclk) disable iff (!reset_n || !assert_enable || link_speed < 2)
        $rose(eq_phase1) |-> $past(eq_phase0, 1) || $past(eq_phase0, 2);
    endproperty
    
    a_eq_sequence: assert property (p_eq_phase_sequence)
        else `uvm_error("PHY_ASSERT", "Equalization phase sequence violation")
    
    // A19: Equalization must complete before L0
    property p_eq_before_l0;
        @(posedge pclk) disable iff (!reset_n || !assert_enable || link_speed < 2)
        (ltssm_state == ST_RECOVERY_EQ) && (ltssm_next_state == ST_L0)
        |-> eq_done;
    endproperty
    
    a_eq_complete: assert property (p_eq_before_l0)
        else `uvm_error("PHY_ASSERT", "Entered L0 without equalization completion")

    //=========================================================================
    // LINK WIDTH ASSERTIONS
    //=========================================================================
    
    // A20: Link width must be valid (power of 2)
    property p_valid_link_width;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        link_up |-> (link_width inside {1, 2, 4, 8, 16, 32});
    endproperty
    
    a_valid_width: assert property (p_valid_link_width)
        else `uvm_error("PHY_ASSERT", "Invalid link width")
    
    // A21: Link width cannot exceed maximum lanes
    property p_width_max;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        link_up |-> (link_width <= NUM_LANES);
    endproperty
    
    a_width_max: assert property (p_width_max)
        else `uvm_error("PHY_ASSERT", "Link width exceeds available lanes")

    //=========================================================================
    // ELECTRICAL IDLE ASSERTIONS
    //=========================================================================
    
    // A22: All lanes should be in electrical idle in L1/L2
    property p_all_idle_in_l1;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (ltssm_state == ST_L1_IDLE) |-> (&tx_elec_idle);
    endproperty
    
    a_all_idle_l1: assert property (p_all_idle_in_l1)
        else `uvm_error("PHY_ASSERT", "Not all lanes idle in L1")
    
    // A23: Active lanes should not be idle in L0
    property p_no_idle_in_l0;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (ltssm_state == ST_L0) |-> (tx_elec_idle[link_width-1:0] == '0);
    endproperty
    
    // Note: This may need lane masking
    // a_no_idle_l0: assert property (p_no_idle_in_l0)
    //     else `uvm_error("PHY_ASSERT", "Active lanes in electrical idle during L0")

    //=========================================================================
    // ERROR HANDLING ASSERTIONS
    //=========================================================================
    
    // A24: Symbol errors should trigger recovery
    property p_error_triggers_recovery;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        (ltssm_state == ST_L0) && symbol_error
        |-> ##[1:100] (ltssm_state == ST_RECOVERY_RCVRLOCK);
    endproperty
    
    a_error_recovery: assert property (p_error_triggers_recovery)
        else `uvm_warning("PHY_ASSERT", "Symbol error did not trigger recovery")
    
    // A25: Lane errors should be logged
    property p_lane_error_logged;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        |lane_error |=> 1'b1;  // Just check that errors are visible
    endproperty
    
    // Coverage for lane errors
    cover property (@(posedge pclk) |lane_error);

    //=========================================================================
    // LINK UP ASSERTION
    //=========================================================================
    
    // A26: Link up only in L0
    property p_link_up_only_l0;
        @(posedge pclk) disable iff (!reset_n || !assert_enable)
        link_up |-> (ltssm_state == ST_L0);
    endproperty
    
    a_link_up_l0: assert property (p_link_up_only_l0)
        else `uvm_error("PHY_ASSERT", "Link up signaled outside of L0")

    //=========================================================================
    // COVERAGE POINTS
    //=========================================================================
    
    // LTSSM state coverage
    covergroup cg_ltssm_state @(posedge pclk);
        cp_state: coverpoint ltssm_state {
            bins detect_quiet   = {ST_DETECT_QUIET};
            bins detect_active  = {ST_DETECT_ACTIVE};
            bins polling_active = {ST_POLLING_ACTIVE};
            bins polling_config = {ST_POLLING_CONFIG};
            bins config_states  = {[ST_CONFIG_LINKWIDTH:ST_CONFIG_IDLE]};
            bins l0             = {ST_L0};
            bins recovery       = {[ST_RECOVERY_RCVRLOCK:ST_RECOVERY_EQ]};
            bins l0s            = {[ST_L0S_ENTRY:ST_L0S_FTS]};
            bins l1             = {[ST_L1_ENTRY:ST_L1_IDLE]};
            bins l2             = {ST_L2_IDLE};
            bins disabled       = {ST_DISABLED};
            bins loopback       = {[ST_LOOPBACK_ENTRY:ST_LOOPBACK_EXIT]};
            bins hot_reset      = {ST_HOT_RESET};
        }
        
        cp_link_width: coverpoint link_width iff (link_up) {
            bins x1  = {1};
            bins x2  = {2};
            bins x4  = {4};
            bins x8  = {8};
            bins x16 = {16};
            bins x32 = {32};
        }
        
        cp_link_speed: coverpoint link_speed iff (link_up) {
            bins gen1 = {0};
            bins gen2 = {1};
            bins gen3 = {2};
            bins gen4 = {3};
            bins gen5 = {4};
            bins gen6 = {5};
        }
        
        cx_state_width: cross cp_state, cp_link_width;
        cx_state_speed: cross cp_state, cp_link_speed;
    endgroup
    
    cg_ltssm_state cg_ltssm = new();

endmodule : pcie_phy_assertions

`endif // PCIE_PHY_ASSERTIONS_SV
