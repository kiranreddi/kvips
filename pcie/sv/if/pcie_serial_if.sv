//-----------------------------------------------------------------------------
// File: pcie_serial_if.sv
// Description: PCIe Serial Interface (Full SerDes Mode)
//              Supports Gen1-Gen6, widths x1-x32
//
// Copyright (c) KVIPS Project
// SPDX-License-Identifier: Apache-2.0
//-----------------------------------------------------------------------------

`ifndef PCIE_SERIAL_IF_SV
`define PCIE_SERIAL_IF_SV

interface pcie_serial_if #(
    parameter int NUM_LANES = 16,         // Number of lanes (1,2,4,8,16,32)
    parameter int MAX_GEN   = 5           // Maximum supported generation (1-6)
) (
    input logic refclk,                   // Reference clock (100 MHz typical)
    input logic perst_n                   // Fundamental reset (active low)
);

    //-------------------------------------------------------------------------
    // Reference Clock Frequencies:
    // Standard: 100 MHz
    // Optional: 125 MHz, 133.33 MHz
    // Spread Spectrum: 0%, -0.5%, -0.25%~-0.75%
    //-------------------------------------------------------------------------

    //=========================================================================
    // SERIAL LANES
    //=========================================================================
    
    // Differential Transmit
    logic TXP [NUM_LANES];                // TX positive
    logic TXN [NUM_LANES];                // TX negative
    
    // Differential Receive
    logic RXP [NUM_LANES];                // RX positive
    logic RXN [NUM_LANES];                // RX negative

    //=========================================================================
    // SIDEBAND SIGNALS (Optional)
    //=========================================================================
    
    // Presence Detection
    logic               PRSNT1_N;         // Card present (primary)
    logic               PRSNT2_N;         // Card present (secondary)
    
    // Power Control
    logic               PWREN;            // Power enable
    logic               PWRGD;            // Power good
    logic               PWRBRK;           // Power brake
    
    // Wake/PME
    logic               WAKE_N;           // Wake signal
    logic               PME_N;            // PME signal
    
    // Hot Plug
    logic               ATTN_N;           // Attention button
    logic               ATTN_LED;         // Attention LED
    logic               PWR_LED;          // Power LED
    
    // Refclk Control
    logic               REFCLK_REQ;       // Reference clock request
    logic               REFCLK_ACK;       // Reference clock acknowledge
    
    // CLKREQ (ASPM)
    logic               CLKREQ_N;         // Clock request (for ASPM L1.2)

    //=========================================================================
    // GENERATION/SPEED PARAMETERS
    //=========================================================================
    
    // Speed table (GT/s)
    localparam real SPEED_GEN1 = 2.5;
    localparam real SPEED_GEN2 = 5.0;
    localparam real SPEED_GEN3 = 8.0;
    localparam real SPEED_GEN4 = 16.0;
    localparam real SPEED_GEN5 = 32.0;
    localparam real SPEED_GEN6 = 64.0;
    
    // Encoding overhead
    localparam real ENC_8B10B   = 0.8;      // Gen1-2
    localparam real ENC_128B130B = 0.9846;  // Gen3-5
    localparam real ENC_FLIT   = 0.98;      // Gen6 (approximate)

    //=========================================================================
    // LANE STRUCTURE
    //=========================================================================
    
    // Lane state tracking
    typedef struct {
        logic         active;              // Lane is active
        int           gen;                 // Current generation
        logic         polarity_invert;     // Polarity inverted
        logic         scrambler_disable;   // Scrambler disabled
    } lane_state_t;
    
    lane_state_t lane_state [NUM_LANES];

    //=========================================================================
    // CLOCKING BLOCKS
    //=========================================================================
    
    // Reference clock domain
    clocking refclk_cb @(posedge refclk);
        default input #1step output #1step;
        
        input  PWRGD;
        input  PRSNT1_N, PRSNT2_N;
        input  WAKE_N, PME_N;
        input  ATTN_N;
        input  REFCLK_ACK;
        input  CLKREQ_N;
        
        output PWREN;
        output PWRBRK;
        output ATTN_LED, PWR_LED;
        output REFCLK_REQ;
    endclocking

    //=========================================================================
    // MODPORTS
    //=========================================================================
    
    // Root Complex side (upstream)
    modport rc (
        input  refclk, perst_n,
        output TXP, TXN,
        input  RXP, RXN,
        input  PRSNT1_N, PRSNT2_N,
        output PWREN, PWRBRK,
        input  PWRGD,
        input  WAKE_N, PME_N,
        input  ATTN_N,
        output ATTN_LED, PWR_LED,
        output REFCLK_REQ,
        input  REFCLK_ACK,
        input  CLKREQ_N,
        clocking refclk_cb
    );
    
    // Endpoint side (downstream)
    modport ep (
        input  refclk, perst_n,
        input  TXP, TXN,
        output RXP, RXN,
        output PRSNT1_N, PRSNT2_N,
        input  PWREN, PWRBRK,
        output PWRGD,
        output WAKE_N, PME_N,
        output ATTN_N,
        input  ATTN_LED, PWR_LED,
        input  REFCLK_REQ,
        output REFCLK_ACK,
        output CLKREQ_N,
        clocking refclk_cb
    );
    
    // Monitor (passive, all inputs)
    modport monitor (
        input  refclk, perst_n,
        input  TXP, TXN,
        input  RXP, RXN,
        input  PRSNT1_N, PRSNT2_N,
        input  PWREN, PWRBRK,
        input  PWRGD,
        input  WAKE_N, PME_N,
        input  ATTN_N,
        input  ATTN_LED, PWR_LED,
        input  REFCLK_REQ, REFCLK_ACK,
        input  CLKREQ_N
    );
    
    // TX modport (for driver transmit)
    modport tx (
        input  refclk, perst_n,
        output TXP, TXN,
        clocking refclk_cb
    );
    
    // RX modport (for monitor receive)
    modport rx (
        input  refclk, perst_n,
        input  RXP, RXN,
        clocking refclk_cb
    );
    
    // Note: loopback/b2b wiring should be done at the TB/top level.

    //=========================================================================
    // ANALOG MODELING (Simplified)
    //=========================================================================
    
    // Voltage levels for signal quality modeling
    typedef struct {
        real vdiff;                        // Differential voltage
        real vcommon;                      // Common mode voltage
        real rise_time;                    // Rise time
        real fall_time;                    // Fall time
        real jitter_rms;                   // RMS jitter
    } signal_quality_t;
    
    signal_quality_t tx_quality [NUM_LANES];
    signal_quality_t rx_quality [NUM_LANES];
    
    // Default signal quality parameters
    initial begin
        for (int i = 0; i < NUM_LANES; i++) begin
            tx_quality[i].vdiff     = 800.0e-3;  // 800 mV differential
            tx_quality[i].vcommon   = 0.0;       // 0V common mode
            tx_quality[i].rise_time = 50.0e-12;  // 50 ps
            tx_quality[i].fall_time = 50.0e-12;  // 50 ps
            tx_quality[i].jitter_rms = 5.0e-12;  // 5 ps RMS jitter
            
            rx_quality[i] = tx_quality[i];       // Same for RX initially
        end
    end

    //=========================================================================
    // LOOPBACK SUPPORT
    //=========================================================================
    
    // Internal loopback enable
    logic loopback_enable;
    
    // Perform loopback connection (TX -> RX)
    task automatic enable_loopback();
        loopback_enable = 1'b1;
        $display("[%0t] SERIAL_IF: Loopback enabled on all lanes", $time);
    endtask
    
    task automatic disable_loopback();
        loopback_enable = 1'b0;
        $display("[%0t] SERIAL_IF: Loopback disabled", $time);
    endtask
    
    // Note: this interface does not drive RX pins by default. If you want a
    // back-to-back/loopback hookup, do it at the TB/top level by wiring one
    // side's TX to the other side's RX (keeps interface multi-driver safe).

    //=========================================================================
    // HELPER TASKS
    //=========================================================================
    
    // Wait for fundamental reset to deassert
    task automatic wait_perst_deassert();
        @(posedge refclk);
        while (!perst_n) @(posedge refclk);
        $display("[%0t] SERIAL_IF: PERST# deasserted", $time);
    endtask
    
    // Wait for power good
    task automatic wait_power_good();
        @(posedge refclk);
        while (!PWRGD) @(posedge refclk);
        $display("[%0t] SERIAL_IF: Power good detected", $time);
    endtask
    
    // Assert fundamental reset
    task automatic assert_perst(int duration_us = 100);
        // Note: This is a helper - actual control would be external
        $display("[%0t] SERIAL_IF: PERST# assertion requested for %0d us", $time, duration_us);
    endtask
    
    // Calculate bandwidth
    function automatic real get_max_bandwidth_gbps(int gen, int width);
        real speed;
        real encoding;
        
        case (gen)
            1: speed = SPEED_GEN1;
            2: speed = SPEED_GEN2;
            3: speed = SPEED_GEN3;
            4: speed = SPEED_GEN4;
            5: speed = SPEED_GEN5;
            6: speed = SPEED_GEN6;
            default: speed = SPEED_GEN1;
        endcase
        
        if (gen <= 2)
            encoding = ENC_8B10B;
        else if (gen <= 5)
            encoding = ENC_128B130B;
        else
            encoding = ENC_FLIT;
            
        return (speed * width * encoding) / 8.0;
    endfunction

    //=========================================================================
    // INITIALIZATION
    //=========================================================================
    
    initial begin
        // Initialize TX lanes to electrical idle (differential = 0)
        for (int i = 0; i < NUM_LANES; i++) begin
            TXP[i] = 1'b0;
            TXN[i] = 1'b0;
            lane_state[i].active = 1'b0;
            lane_state[i].gen = 1;
            lane_state[i].polarity_invert = 1'b0;
            lane_state[i].scrambler_disable = 1'b0;
        end
        
        // Sideband signals
        PRSNT1_N  = 1'b1;  // Not present initially
        PRSNT2_N  = 1'b1;
        PWREN     = 1'b0;
        PWRGD     = 1'b0;
        PWRBRK    = 1'b0;
        WAKE_N    = 1'b1;  // Not asserted
        PME_N     = 1'b1;
        ATTN_N    = 1'b1;
        ATTN_LED  = 1'b0;
        PWR_LED   = 1'b0;
        REFCLK_REQ = 1'b0;
        REFCLK_ACK = 1'b1;  // Clock available
        CLKREQ_N  = 1'b0;   // Clock requested
        
        loopback_enable = 1'b0;
    end

    //=========================================================================
    // ASSERTIONS
    //=========================================================================
    
    // Reference clock must be stable
    property p_refclk_stable;
        @(posedge refclk) disable iff (!perst_n)
        1;
    endproperty
    
    // PERST must be held for minimum time after power stable
    property p_perst_hold;
        @(posedge refclk)
        $fell(perst_n) |-> ##[1:$] perst_n;
    endproperty
    
    // Power good must follow power enable
    property p_pwrgd_follows_pwren;
        @(posedge refclk)
        $rose(PWREN) |-> ##[1:1000] PWRGD;
    endproperty
    
    // Assertions (can be disabled via define)
    `ifndef PCIE_SERIAL_IF_NO_ASSERT
        assert_refclk_stable: assert property (p_refclk_stable);
        // assert_perst_hold: assert property (p_perst_hold);
        // assert_pwrgd: assert property (p_pwrgd_follows_pwren);
    `endif

endinterface : pcie_serial_if

`endif // PCIE_SERIAL_IF_SV
