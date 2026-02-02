//-----------------------------------------------------------------------------
// File: pcie_pipe_if.sv
// Description: PCIe PIPE Interface (PHY Interface for PCI Express)
//              Supports Gen1-Gen6, widths x1-x32
//
// Copyright (c) KVIPS Project
// SPDX-License-Identifier: Apache-2.0
//-----------------------------------------------------------------------------

`ifndef PCIE_PIPE_IF_SV
`define PCIE_PIPE_IF_SV

interface pcie_pipe_if #(
    parameter int NUM_LANES    = 16,      // Number of lanes (1,2,4,8,16,32)
    parameter int MAX_GEN      = 5,       // Maximum supported generation (1-6)
    parameter int DATA_WIDTH   = 32       // Data width per lane (8,16,32)
) (
    input logic pclk,                     // PIPE clock
    input logic reset_n                   // Active low reset
);

    //-------------------------------------------------------------------------
    // Clock Requirements by Generation:
    // Gen1: 250 MHz (2.5 GT/s / 10)
    // Gen2: 250 MHz (5.0 GT/s / 20) or 500 MHz
    // Gen3: 250 MHz (8.0 GT/s / 32) 
    // Gen4: 500 MHz (16.0 GT/s / 32)
    // Gen5: 1000 MHz (32.0 GT/s / 32) or 500 MHz with 64-bit
    // Gen6: 2000 MHz or lower with wider data path (FLIT mode)
    //-------------------------------------------------------------------------

    //=========================================================================
    // TRANSMIT PATH - Per Lane Signals
    //=========================================================================
    
    // Transmit Data (Per Lane)
    logic [DATA_WIDTH-1:0] TxData       [NUM_LANES];  // Transmit data
    logic [DATA_WIDTH/8-1:0] TxDataK    [NUM_LANES];  // K-character indication (Gen1/2)
    logic                  TxDataValid  [NUM_LANES];  // Data valid (Gen3+)
    logic                  TxStartBlock[NUM_LANES];   // Start of 128b block (Gen3+)
    logic [1:0]            TxSyncHeader[NUM_LANES];   // Sync header (Gen3+)
    
    // Transmit Control (Per Lane)
    logic                  TxElecIdle   [NUM_LANES];  // Electrical idle
    logic                  TxCompliance [NUM_LANES];  // Compliance pattern
    logic [1:0]            TxMargin     [NUM_LANES];  // Voltage margin
    logic                  TxSwing      [NUM_LANES];  // Full/reduced swing
    logic                  TxDeemph     [NUM_LANES];  // De-emphasis level
    
    // Transmit Equalization (Gen3+)
    logic [5:0]            TxPreset     [NUM_LANES];  // Tx preset (Gen3+)
    logic [3:0]            TxCoeff      [NUM_LANES];  // Tx coefficient
    logic [17:0]           TxEqCoeff    [NUM_LANES];  // Full EQ coefficients (Gen4+)
    
    // Transmit Pattern (Gen3+)
    logic [1:0]            TxPattern    [NUM_LANES];  // Pattern for compliance

    //=========================================================================
    // RECEIVE PATH - Per Lane Signals
    //=========================================================================
    
    // Receive Data (Per Lane)
    logic [DATA_WIDTH-1:0] RxData       [NUM_LANES];  // Receive data
    logic [DATA_WIDTH/8-1:0] RxDataK    [NUM_LANES];  // K-character indication (Gen1/2)
    logic                  RxDataValid  [NUM_LANES];  // Data valid
    logic                  RxStartBlock[NUM_LANES];   // Start of 128b block (Gen3+)
    logic [1:0]            RxSyncHeader[NUM_LANES];   // Sync header (Gen3+)
    
    // Receive Status (Per Lane)
    logic                  RxElecIdle   [NUM_LANES];  // Electrical idle detected
    logic [2:0]            RxStatus     [NUM_LANES];  // Receiver status
    logic                  RxValid      [NUM_LANES];  // Symbol lock achieved
    
    // Receive Equalization (Gen3+)
    logic [5:0]            RxPreset     [NUM_LANES];  // Rx preset hint (Gen3+)
    logic [17:0]           RxEqCoeff    [NUM_LANES];  // Full EQ coefficients (Gen4+)
    logic                  RxEqEval     [NUM_LANES];  // EQ evaluation request
    logic                  RxEqInProg   [NUM_LANES];  // EQ in progress

    //=========================================================================
    // COMMON SIGNALS
    //=========================================================================
    
    // Power State
    logic [1:0]            PowerDown;                 // Power state request
                                                      // 00: P0 (active)
                                                      // 01: P0s
                                                      // 10: P1
                                                      // 11: P2
    
    // Rate/Speed Control
    logic [1:0]            Rate;                      // Rate selection
                                                      // 00: Gen1 (2.5 GT/s)
                                                      // 01: Gen2 (5.0 GT/s)
                                                      // 10: Gen3 (8.0 GT/s)
                                                      // 11: Gen4+ (16.0+ GT/s)
    logic [2:0]            RateGen;                   // Extended generation (Gen4+)
                                                      // Actual generation = RateGen + 1
    
    // PHY Status
    logic                  PhyStatus;                 // PHY ready/ack
    logic                  PhyMode;                   // PHY mode (PIPE/SerDes)
    
    // Link Control
    logic                  TxDetectRx_Loopback;       // Detect/Loopback request
    logic                  TxElecIdleIn;              // Electrical idle control
    logic                  RxPolarity [NUM_LANES];    // Polarity inversion
    logic                  RxEqTraining;              // EQ training mode
    
    // Reset
    logic                  PipeReset;                 // PIPE reset
    
    // Width Control
    logic [4:0]            Width;                     // Negotiated width
    
    // Clock Requirements
    logic                  PclkChangeAck;             // Clock change acknowledge
    logic                  PclkChangeOk;              // Clock change allowed
    
    // Lane Margining (Gen4+)
    logic [NUM_LANES-1:0]  LaneMarginReq;             // Margin request
    logic [NUM_LANES-1:0]  LaneMarginAck;             // Margin acknowledge
    logic [7:0]            LaneMarginCmd [NUM_LANES]; // Margin command
    logic [7:0]            LaneMarginRsp [NUM_LANES]; // Margin response

    //=========================================================================
    // RxStatus Encoding
    //=========================================================================
    // 000: Received data OK
    // 001: SKP added
    // 010: SKP removed  
    // 011: Receiver detect (P1 only)
    // 100: 8b/10b decode error
    // 101: Elastic buffer overflow
    // 110: Elastic buffer underflow
    // 111: Disparity error

    //=========================================================================
    // CLOCKING BLOCKS
    //=========================================================================
    
    // MAC/Controller Driving Clocking Block
    clocking mac_cb @(posedge pclk);
        default input #1step output #1step;
        
        // Outputs from MAC
        output TxData, TxDataK, TxDataValid;
        output TxStartBlock, TxSyncHeader;
        output TxElecIdle, TxCompliance;
        output TxMargin, TxSwing, TxDeemph;
        output TxPreset, TxCoeff, TxEqCoeff;
        output TxPattern;
        output PowerDown, Rate, RateGen;
        output TxDetectRx_Loopback, TxElecIdleIn;
        output RxPolarity, RxEqTraining;
        output Width;
        output PclkChangeOk;
        output LaneMarginReq, LaneMarginCmd;
        
        // Inputs to MAC
        input RxData, RxDataK, RxDataValid;
        input RxStartBlock, RxSyncHeader;
        input RxElecIdle, RxStatus, RxValid;
        input RxPreset, RxEqCoeff;
        input RxEqEval, RxEqInProg;
        input PhyStatus, PhyMode;
        input PclkChangeAck;
        input LaneMarginAck, LaneMarginRsp;
    endclocking
    
    // PHY Driving Clocking Block
    clocking phy_cb @(posedge pclk);
        default input #1step output #1step;
        
        // Outputs from PHY
        output RxData, RxDataK, RxDataValid;
        output RxStartBlock, RxSyncHeader;
        output RxElecIdle, RxStatus, RxValid;
        output RxPreset, RxEqCoeff;
        output RxEqEval, RxEqInProg;
        output PhyStatus, PhyMode;
        output PclkChangeAck;
        output LaneMarginAck, LaneMarginRsp;
        
        // Inputs to PHY
        input TxData, TxDataK, TxDataValid;
        input TxStartBlock, TxSyncHeader;
        input TxElecIdle, TxCompliance;
        input TxMargin, TxSwing, TxDeemph;
        input TxPreset, TxCoeff, TxEqCoeff;
        input TxPattern;
        input PowerDown, Rate, RateGen;
        input TxDetectRx_Loopback, TxElecIdleIn;
        input RxPolarity, RxEqTraining;
        input Width;
        input PclkChangeOk;
        input LaneMarginReq, LaneMarginCmd;
    endclocking
    
    // Monitor Clocking Block
    clocking mon_cb @(posedge pclk);
        default input #1step;
        
        // All signals as inputs
        input TxData, TxDataK, TxDataValid;
        input TxStartBlock, TxSyncHeader;
        input TxElecIdle, TxCompliance;
        input TxMargin, TxSwing, TxDeemph;
        input TxPreset, TxCoeff, TxEqCoeff;
        input TxPattern;
        input RxData, RxDataK, RxDataValid;
        input RxStartBlock, RxSyncHeader;
        input RxElecIdle, RxStatus, RxValid;
        input RxPreset, RxEqCoeff;
        input RxEqEval, RxEqInProg;
        input PowerDown, Rate, RateGen;
        input PhyStatus, PhyMode;
        input TxDetectRx_Loopback, TxElecIdleIn;
        input RxPolarity, RxEqTraining;
        input PipeReset;
        input Width;
        input PclkChangeAck, PclkChangeOk;
        input LaneMarginReq, LaneMarginCmd;
        input LaneMarginAck, LaneMarginRsp;
    endclocking

    //=========================================================================
    // MODPORTS
    //=========================================================================
    
    // MAC/Controller side (drives TX, receives RX)
    modport mac (
        input  pclk, reset_n,
        output TxData, TxDataK, TxDataValid,
        output TxStartBlock, TxSyncHeader,
        output TxElecIdle, TxCompliance,
        output TxMargin, TxSwing, TxDeemph,
        output TxPreset, TxCoeff, TxEqCoeff,
        output TxPattern,
        input  RxData, RxDataK, RxDataValid,
        input  RxStartBlock, RxSyncHeader,
        input  RxElecIdle, RxStatus, RxValid,
        input  RxPreset, RxEqCoeff,
        input  RxEqEval, RxEqInProg,
        output PowerDown, Rate, RateGen,
        input  PhyStatus, PhyMode,
        output TxDetectRx_Loopback, TxElecIdleIn,
        output RxPolarity, RxEqTraining,
        output PipeReset,
        output Width,
        output PclkChangeOk,
        input  PclkChangeAck,
        output LaneMarginReq, LaneMarginCmd,
        input  LaneMarginAck, LaneMarginRsp,
        clocking mac_cb
    );
    
    // PHY side (drives RX, receives TX)
    modport phy (
        input  pclk, reset_n,
        input  TxData, TxDataK, TxDataValid,
        input  TxStartBlock, TxSyncHeader,
        input  TxElecIdle, TxCompliance,
        input  TxMargin, TxSwing, TxDeemph,
        input  TxPreset, TxCoeff, TxEqCoeff,
        input  TxPattern,
        output RxData, RxDataK, RxDataValid,
        output RxStartBlock, RxSyncHeader,
        output RxElecIdle, RxStatus, RxValid,
        output RxPreset, RxEqCoeff,
        output RxEqEval, RxEqInProg,
        input  PowerDown, Rate, RateGen,
        output PhyStatus, PhyMode,
        input  TxDetectRx_Loopback, TxElecIdleIn,
        input  RxPolarity, RxEqTraining,
        input  PipeReset,
        input  Width,
        input  PclkChangeOk,
        output PclkChangeAck,
        input  LaneMarginReq, LaneMarginCmd,
        output LaneMarginAck, LaneMarginRsp,
        clocking phy_cb
    );
    
    // Monitor (passive, all inputs)
    modport monitor (
        input  pclk, reset_n,
        input  TxData, TxDataK, TxDataValid,
        input  TxStartBlock, TxSyncHeader,
        input  TxElecIdle, TxCompliance,
        input  TxMargin, TxSwing, TxDeemph,
        input  TxPreset, TxCoeff, TxEqCoeff,
        input  TxPattern,
        input  RxData, RxDataK, RxDataValid,
        input  RxStartBlock, RxSyncHeader,
        input  RxElecIdle, RxStatus, RxValid,
        input  RxPreset, RxEqCoeff,
        input  RxEqEval, RxEqInProg,
        input  PowerDown, Rate, RateGen,
        input  PhyStatus, PhyMode,
        input  TxDetectRx_Loopback, TxElecIdleIn,
        input  RxPolarity, RxEqTraining,
        input  PipeReset,
        input  Width,
        input  PclkChangeOk, PclkChangeAck,
        input  LaneMarginReq, LaneMarginCmd,
        input  LaneMarginAck, LaneMarginRsp,
        clocking mon_cb
    );

    //=========================================================================
    // HELPER TASKS
    //=========================================================================
    
    // Wait for PHY ready
    task automatic wait_phy_ready();
        @(posedge pclk);
        while (!PhyStatus) @(posedge pclk);
    endtask
    
    // Get current generation
    function automatic int get_generation();
        if (MAX_GEN <= 3) begin
            case (Rate)
                2'b00: return 1;
                2'b01: return 2;
                2'b10: return 3;
                default: return 3;
            endcase
        end else begin
            return RateGen + 1;
        end
    endfunction
    
    // Get current speed in GT/s
    function automatic real get_speed_gtps();
        case (get_generation())
            1: return 2.5;
            2: return 5.0;
            3: return 8.0;
            4: return 16.0;
            5: return 32.0;
            6: return 64.0;
            default: return 2.5;
        endcase
    endfunction
    
    // Calculate effective bandwidth in GB/s
    function automatic real get_bandwidth_gbps();
        real speed = get_speed_gtps();
        int width = Width;
        real encoding_overhead;
        
        // Encoding overhead
        if (get_generation() <= 2)
            encoding_overhead = 0.8;  // 8b/10b
        else
            encoding_overhead = 0.9846;  // 128b/130b
            
        return (speed * width * encoding_overhead) / 8.0;
    endfunction

    //=========================================================================
    // INITIALIZATION
    //=========================================================================
    
    // Initialize all signals to safe defaults
    initial begin
        for (int i = 0; i < NUM_LANES; i++) begin
            TxData[i]        = '0;
            TxDataK[i]       = '0;
            TxDataValid[i]   = 1'b0;
            TxStartBlock[i]  = 1'b0;
            TxSyncHeader[i]  = 2'b00;
            TxElecIdle[i]    = 1'b1;  // Start in electrical idle
            TxCompliance[i]  = 1'b0;
            TxMargin[i]      = 2'b00;
            TxSwing[i]       = 1'b0;
            TxDeemph[i]      = 1'b0;
            TxPreset[i]      = 6'h0;
            TxCoeff[i]       = 4'h0;
            TxEqCoeff[i]     = 18'h0;
            TxPattern[i]     = 2'b00;
            
            RxData[i]        = '0;
            RxDataK[i]       = '0;
            RxDataValid[i]   = 1'b0;
            RxStartBlock[i]  = 1'b0;
            RxSyncHeader[i]  = 2'b00;
            RxElecIdle[i]    = 1'b1;
            RxStatus[i]      = 3'b000;
            RxValid[i]       = 1'b0;
            RxPreset[i]      = 6'h0;
            RxEqCoeff[i]     = 18'h0;
            RxEqEval[i]      = 1'b0;
            RxEqInProg[i]    = 1'b0;
            RxPolarity[i]    = 1'b0;
        end
        
        PowerDown            = 2'b11;  // P2 initially
        Rate                 = 2'b00;  // Gen1
        RateGen              = 3'b000;
        PhyStatus            = 1'b0;
        PhyMode              = 1'b0;
        TxDetectRx_Loopback  = 1'b0;
        TxElecIdleIn         = 1'b1;
        RxEqTraining         = 1'b0;
        PipeReset            = 1'b0;
        Width                = 5'd1;
        PclkChangeAck        = 1'b0;
        PclkChangeOk         = 1'b1;
        
        for (int i = 0; i < NUM_LANES; i++) begin
            LaneMarginReq[i]     = 1'b0;
            LaneMarginAck[i]     = 1'b0;
            LaneMarginCmd[i]     = 8'h00;
            LaneMarginRsp[i]     = 8'h00;
        end
    end

endinterface : pcie_pipe_if

`endif // PCIE_PIPE_IF_SV
