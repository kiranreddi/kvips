//-----------------------------------------------------------------------------
// File: pcie_types_pkg.sv
// Description: PCIe Types and Constants Package
//              Defines all types, enums, and constants for PCIe VIP
//
// Copyright (c) KVIPS Project
// SPDX-License-Identifier: Apache-2.0
//-----------------------------------------------------------------------------

`ifndef PCIE_TYPES_PKG_SV
`define PCIE_TYPES_PKG_SV

`timescale 1ns/1ps

package pcie_types_pkg;
    timeunit 1ns;
    timeprecision 1ps;

    //=========================================================================
    // BASIC TYPES
    //=========================================================================
    
    typedef logic [7:0]   byte_t;
    typedef logic [15:0]  word_t;
    typedef logic [31:0]  dword_t;
    typedef logic [63:0]  qword_t;
    typedef logic [127:0] oword_t;
    
    typedef logic [15:0]  requester_id_t;  // Bus/Device/Function
    typedef logic [7:0]   tag_t;           // 8-bit tag (extended)
    typedef logic [9:0]   tag_10bit_t;     // 10-bit tag
    typedef logic [13:0]  tag_14bit_t;     // 14-bit tag (Gen6)

    //=========================================================================
    // GENERATION ENUM
    //=========================================================================
    
    typedef enum int {
        PCIE_GEN1 = 1,    // 2.5 GT/s
        PCIE_GEN2 = 2,    // 5.0 GT/s
        PCIE_GEN3 = 3,    // 8.0 GT/s
        PCIE_GEN4 = 4,    // 16.0 GT/s
        PCIE_GEN5 = 5,    // 32.0 GT/s
        PCIE_GEN6 = 6     // 64.0 GT/s
    } pcie_gen_e;

    //=========================================================================
    // LINK WIDTH ENUM
    //=========================================================================
    
    typedef enum int {
        PCIE_X1  = 1,
        PCIE_X2  = 2,
        PCIE_X4  = 4,
        PCIE_X8  = 8,
        PCIE_X16 = 16,
        PCIE_X32 = 32
    } pcie_width_e;

    //=========================================================================
    // AGENT MODE ENUM
    //=========================================================================
    
    typedef enum int {
        PCIE_RC,           // Root Complex
        PCIE_EP,           // Endpoint
        PCIE_SWITCH,       // Switch
        PCIE_BRIDGE,       // Bridge
        PCIE_MONITOR       // Passive Monitor
    } pcie_agent_mode_e;

    //=========================================================================
    // INTERFACE MODE ENUM
    //=========================================================================
    
    typedef enum int {
        PCIE_PIPE_MODE,    // PIPE interface
        PCIE_SERIAL_MODE   // Serial interface
    } pcie_interface_mode_e;

    //=========================================================================
    // LTSSM STATES
    //=========================================================================
    
    typedef enum int {
        // Detect substates
        LTSSM_DETECT_QUIET,
        LTSSM_DETECT_ACTIVE,
        
        // Polling substates
        LTSSM_POLLING_ACTIVE,
        LTSSM_POLLING_CONFIGURATION,
        LTSSM_POLLING_COMPLIANCE,
        LTSSM_POLLING_SPEED,
        
        // Configuration substates
        LTSSM_CONFIG_LINKWIDTH_START,
        LTSSM_CONFIG_LINKWIDTH_ACCEPT,
        LTSSM_CONFIG_LANENUM_WAIT,
        LTSSM_CONFIG_LANENUM_ACCEPT,
        LTSSM_CONFIG_COMPLETE,
        LTSSM_CONFIG_IDLE,
        
        // L0
        LTSSM_L0,
        
        // Recovery substates
        LTSSM_RECOVERY_RCVRLOCK,
        LTSSM_RECOVERY_RCVRCFG,
        LTSSM_RECOVERY_SPEED,
        LTSSM_RECOVERY_IDLE,
        LTSSM_RECOVERY_EQUALIZATION,
        
        // L0s substates
        LTSSM_L0S_ENTRY,
        LTSSM_L0S_IDLE,
        LTSSM_L0S_FTS,
        
        // L1 substates
        LTSSM_L1_ENTRY,
        LTSSM_L1_IDLE,
        
        // L2 substates
        LTSSM_L2_IDLE,
        LTSSM_L2_TRANSMIT_WAKE,
        
        // Other states
        LTSSM_DISABLED,
        LTSSM_LOOPBACK_ENTRY,
        LTSSM_LOOPBACK_ACTIVE,
        LTSSM_LOOPBACK_EXIT,
        LTSSM_HOT_RESET
    } ltssm_state_e;

    //=========================================================================
    // TRANSACTION TYPE ENUM
    //=========================================================================
    
    typedef enum int {
        PCIE_TLP,           // Transaction Layer Packet
        PCIE_DLLP,          // Data Link Layer Packet
        PCIE_ORDERED_SET    // Ordered Set (TS1, TS2, etc.)
    } pcie_trans_type_e;

    //=========================================================================
    // ORDERED SET TYPE ENUM
    //=========================================================================
    
    typedef enum int {
        OS_TS1,             // Training Sequence 1
        OS_TS2,             // Training Sequence 2
        OS_SKP,             // Skip Ordered Set
        OS_FTS,             // Fast Training Sequence
        OS_IDLE,            // Electrical Idle Ordered Set
        OS_EIEOS,           // Electrical Idle Exit Ordered Set
        OS_EIOS,            // Electrical Idle Ordered Set (Gen3+)
        OS_SDS              // Start of Data Stream
    } ordered_set_type_e;

    //=========================================================================
    // TLP TYPES
    //=========================================================================
    
    typedef enum logic [4:0] {
        // Memory requests
        TLP_MRD32         = 5'b00000,  // Memory Read 32-bit
        TLP_MRD64         = 5'b00001,  // Memory Read 64-bit
        TLP_MRDLK32       = 5'b00010,  // Memory Read Lock 32-bit
        TLP_MRDLK64       = 5'b00011,  // Memory Read Lock 64-bit
        TLP_MWR32         = 5'b00100,  // Memory Write 32-bit
        TLP_MWR64         = 5'b00101,  // Memory Write 64-bit
        
        // IO requests
        TLP_IORD          = 5'b00110,  // IO Read
        TLP_IOWR          = 5'b00111,  // IO Write
        
        // Configuration requests
        TLP_CFGRD0        = 5'b01000,  // Config Read Type 0
        TLP_CFGWR0        = 5'b01001,  // Config Write Type 0
        TLP_CFGRD1        = 5'b01010,  // Config Read Type 1
        TLP_CFGWR1        = 5'b01011,  // Config Write Type 1
        
        // Message requests
        TLP_MSG           = 5'b01100,  // Message
        TLP_MSGD          = 5'b01101,  // Message with Data
        
        // Completions
        TLP_CPL           = 5'b01110,  // Completion
        TLP_CPLD          = 5'b01111,  // Completion with Data
        TLP_CPLLK         = 5'b10000,  // Completion Locked
        TLP_CPLDLK        = 5'b10001,  // Completion Locked with Data
        
        // Atomic operations
        TLP_FETCH_ADD32   = 5'b10010,  // FetchAdd 32-bit
        TLP_FETCH_ADD64   = 5'b10011,  // FetchAdd 64-bit
        TLP_SWAP32        = 5'b10100,  // Swap 32-bit
        TLP_SWAP64        = 5'b10101,  // Swap 64-bit
        TLP_CAS32         = 5'b10110,  // CAS 32-bit
        TLP_CAS64         = 5'b10111   // CAS 64-bit
    } tlp_type_e;

    //=========================================================================
    // TLP FORMAT
    //=========================================================================
    
    typedef enum logic [1:0] {
        TLP_FMT_3DW_ND = 2'b00,   // 3 DW header, no data
        TLP_FMT_4DW_ND = 2'b01,   // 4 DW header, no data
        TLP_FMT_3DW_D  = 2'b10,   // 3 DW header, with data
        TLP_FMT_4DW_D  = 2'b11    // 4 DW header, with data
    } tlp_fmt_e;

    //=========================================================================
    // COMPLETION STATUS
    //=========================================================================
    
    typedef enum logic [2:0] {
        CPL_SC  = 3'b000,  // Successful Completion
        CPL_UR  = 3'b001,  // Unsupported Request
        CPL_CRS = 3'b010,  // Configuration Retry Status
        CPL_CA  = 3'b100   // Completer Abort
    } cpl_status_e;

    //=========================================================================
    // MESSAGE CODES
    //=========================================================================
    
    typedef enum logic [7:0] {
        // Interrupt messages
        MSG_ASSERT_INTA   = 8'h20,
        MSG_ASSERT_INTB   = 8'h21,
        MSG_ASSERT_INTC   = 8'h22,
        MSG_ASSERT_INTD   = 8'h23,
        MSG_DEASSERT_INTA = 8'h24,
        MSG_DEASSERT_INTB = 8'h25,
        MSG_DEASSERT_INTC = 8'h26,
        MSG_DEASSERT_INTD = 8'h27,
        
        // Power management
        MSG_PM_ACTIVE_STATE_NAK = 8'h14,
        MSG_PM_PME            = 8'h18,
        MSG_PME_TURN_OFF      = 8'h19,
        MSG_PME_TO_ACK        = 8'h1B,
        
        // Error messages
        MSG_ERR_COR           = 8'h30,
        MSG_ERR_NONFATAL      = 8'h31,
        MSG_ERR_FATAL         = 8'h33,
        
        // Attention
        MSG_ATTENTION_INDICATOR_OFF = 8'h40,
        MSG_ATTENTION_INDICATOR_ON  = 8'h41,
        MSG_ATTENTION_INDICATOR_BLINK = 8'h43,
        MSG_POWER_INDICATOR_ON      = 8'h45,
        MSG_POWER_INDICATOR_BLINK   = 8'h47,
        MSG_POWER_INDICATOR_OFF     = 8'h44,
        MSG_ATTENTION_BUTTON_PRESSED = 8'h48,
        
        // Slot
        MSG_SET_SLOT_POWER_LIMIT = 8'h50,
        
        // Vendor
        MSG_VENDOR_TYPE0 = 8'h7E,
        MSG_VENDOR_TYPE1 = 8'h7F,
        
        // LTR
        MSG_LTR = 8'h10
    } msg_code_e;

    //=========================================================================
    // MESSAGE ROUTING
    //=========================================================================
    
    typedef enum logic [2:0] {
        MSG_ROUTE_TO_RC           = 3'b000,
        MSG_ROUTE_BY_ADDR         = 3'b001,
        MSG_ROUTE_BY_ID           = 3'b010,
        MSG_ROUTE_FROM_RC         = 3'b011,
        MSG_ROUTE_LOCAL           = 3'b100,
        MSG_ROUTE_GATHER_TO_RC    = 3'b101
    } msg_routing_e;

    //=========================================================================
    // TRAFFIC CLASS
    //=========================================================================
    
    typedef logic [2:0] tc_t;
    
    localparam tc_t TC0 = 3'b000;
    localparam tc_t TC1 = 3'b001;
    localparam tc_t TC2 = 3'b010;
    localparam tc_t TC3 = 3'b011;
    localparam tc_t TC4 = 3'b100;
    localparam tc_t TC5 = 3'b101;
    localparam tc_t TC6 = 3'b110;
    localparam tc_t TC7 = 3'b111;

    //=========================================================================
    // DLLP TYPES
    //=========================================================================
    
    typedef enum logic [7:0] {
        DLLP_ACK           = 8'h00,
        DLLP_NAK           = 8'h10,
        DLLP_PM_ENTER_L1   = 8'h20,
        DLLP_PM_ENTER_L23  = 8'h21,
        DLLP_PM_AS_L0S     = 8'h23,
        DLLP_PM_REQ_L1     = 8'h24,
        DLLP_PM_REQ_ACK    = 8'h25,
        DLLP_VENDOR        = 8'h30,
        DLLP_FEATURE_ACK   = 8'h31,
        // Internal-only sentinel (not a real on-wire DLLP type)
        DLLP_NOP           = 8'hFF,
        DLLP_INITFC1_P     = 8'h40,
        DLLP_INITFC1_NP    = 8'h50,
        DLLP_INITFC1_CPL   = 8'h60,
        DLLP_INITFC2_P     = 8'h48,
        DLLP_INITFC2_NP    = 8'h58,
        DLLP_INITFC2_CPL   = 8'h68,
        DLLP_UPDATEFC_P    = 8'h80,
        DLLP_UPDATEFC_NP   = 8'h90,
        DLLP_UPDATEFC_CPL  = 8'hA0
    } dllp_type_e;

    //=========================================================================
    // POWER STATES
    //=========================================================================
    
    typedef enum logic [1:0] {
        PIPE_P0  = 2'b00,  // Active
        PIPE_P0S = 2'b01,  // Standby
        PIPE_P1  = 2'b10,  // Low power
        PIPE_P2  = 2'b11   // Very low power
    } pipe_power_e;
    
    typedef enum int {
        PM_D0,
        PM_D1,
        PM_D2,
        PM_D3HOT,
        PM_D3COLD
    } pm_state_e;

    //=========================================================================
    // FLOW CONTROL TYPES
    //=========================================================================
    
    typedef enum int {
        FC_POSTED,
        FC_NON_POSTED,
        FC_COMPLETION
    } fc_type_e;

    //=========================================================================
    // ERROR TYPES
    //=========================================================================
    
    typedef enum int {
        // Correctable errors
        ERR_RECEIVER_ERROR,
        ERR_BAD_TLP,
        ERR_BAD_DLLP,
        ERR_REPLAY_NUM_ROLLOVER,
        ERR_REPLAY_TIMER_TIMEOUT,
        ERR_ADVISORY_NONFATAL,
        ERR_CORRECTED_INTERNAL,
        ERR_HEADER_LOG_OVERFLOW,
        
        // Uncorrectable (Non-Fatal)
        ERR_POISONED_TLP,
        ERR_COMPLETION_TIMEOUT,
        ERR_COMPLETER_ABORT,
        ERR_UNEXPECTED_COMPLETION,
        ERR_RECEIVER_OVERFLOW,
        ERR_ACS_VIOLATION,
        ERR_UNCORRECTABLE_INTERNAL,
        ERR_MC_BLOCKED_TLP,
        ERR_ATOMIC_OP_EGRESS_BLOCKED,
        ERR_TLP_PREFIX_BLOCKED,
        ERR_POISONED_TLP_EGRESS_BLOCKED,
        
        // Uncorrectable (Fatal)
        ERR_DATA_LINK_PROTOCOL,
        ERR_SURPRISE_DOWN,
        ERR_FLOW_CONTROL_PROTOCOL,
        ERR_MALFORMED_TLP,
        ERR_ECRC_ERROR,
        ERR_UNSUPPORTED_REQUEST
    } pcie_error_e;

    //=========================================================================
    // TLP HEADER STRUCTURES
    //=========================================================================
    
    // Generic TLP header (DW0)
    typedef struct packed {
        logic [1:0]  fmt;          // Format
        logic [4:0]  tlp_type;     // Type
        logic        t9;           // Traffic Class (bit 9)
        logic [2:0]  tc;           // Traffic Class [2:0]
        logic        t8;           // Traffic Class (bit 8)
        logic        attr2;        // Attribute[2]
        logic        ln;           // Lightweight Notification
        logic        th;           // TLP Hints
        logic        td;           // TLP Digest (ECRC)
        logic        ep;           // Poisoned
        logic [1:0]  attr;         // Attribute[1:0]
        logic [1:0]  at;           // Address Type
        logic [9:0]  length;       // Length in DW
    } tlp_header_dw0_t;
    
    // Memory/IO request header
    // Note: contains a payload, so this cannot be a packed struct.
    typedef struct {
        tlp_header_dw0_t dw0;
        logic [15:0] requester_id;
        logic [7:0]  tag;
        logic [3:0]  last_be;
        logic [3:0]  first_be;
        logic [63:0] address;      // 64 or 32 bit depending on fmt
        logic [31:0] data[];       // Payload
    } tlp_mem_req_t;
    
    // Completion header
    // Note: contains a payload, so this cannot be a packed struct.
    typedef struct {
        tlp_header_dw0_t dw0;
        logic [15:0] completer_id;
        logic [2:0]  status;
        logic        bcm;          // Byte Count Modified
        logic [11:0] byte_count;
        logic [15:0] requester_id;
        logic [7:0]  tag;
        logic        r;            // Reserved
        logic [6:0]  lower_addr;
        logic [31:0] data[];       // Payload (if CplD)
    } tlp_cpl_t;
    
    // Config request header
    typedef struct packed {
        tlp_header_dw0_t dw0;
        logic [15:0] requester_id;
        logic [7:0]  tag;
        logic [3:0]  last_be;
        logic [3:0]  first_be;
        logic [7:0]  bus_num;
        logic [4:0]  device_num;
        logic [2:0]  function_num;
        logic [3:0]  reserved;
        logic [11:0] reg_num;      // Extended config space
    } tlp_cfg_req_t;
    
    // Message header
    typedef struct packed {
        tlp_header_dw0_t dw0;
        logic [15:0] requester_id;
        logic [7:0]  tag;
        logic [7:0]  msg_code;
        logic [63:0] address_or_data;  // Routing dependent
    } tlp_msg_t;

    //=========================================================================
    // FLOW CONTROL STRUCTURE
    //=========================================================================
    
    typedef struct {
        int posted_header_credits;
        int posted_data_credits;
        int non_posted_header_credits;
        int non_posted_data_credits;
        int completion_header_credits;
        int completion_data_credits;
    } fc_credits_t;
    
    // Infinite credits marker
    localparam int FC_INFINITE = -1;

    //=========================================================================
    // CONFIGURATION SPACE ADDRESSES
    //=========================================================================
    
    // Type 0 Configuration Header
    localparam int CFG_VENDOR_ID         = 12'h000;
    localparam int CFG_DEVICE_ID         = 12'h002;
    localparam int CFG_COMMAND           = 12'h004;
    localparam int CFG_STATUS            = 12'h006;
    localparam int CFG_REV_ID            = 12'h008;
    localparam int CFG_CLASS_CODE        = 12'h009;
    localparam int CFG_CACHE_LINE_SIZE   = 12'h00C;
    localparam int CFG_LATENCY_TIMER     = 12'h00D;
    localparam int CFG_HEADER_TYPE       = 12'h00E;
    localparam int CFG_BIST              = 12'h00F;
    localparam int CFG_BAR0              = 12'h010;
    localparam int CFG_BAR1              = 12'h014;
    localparam int CFG_BAR2              = 12'h018;
    localparam int CFG_BAR3              = 12'h01C;
    localparam int CFG_BAR4              = 12'h020;
    localparam int CFG_BAR5              = 12'h024;
    localparam int CFG_CARDBUS_CIS       = 12'h028;
    localparam int CFG_SUBSYS_VENDOR_ID  = 12'h02C;
    localparam int CFG_SUBSYS_ID         = 12'h02E;
    localparam int CFG_EXP_ROM_BASE      = 12'h030;
    localparam int CFG_CAP_PTR           = 12'h034;
    localparam int CFG_INT_LINE          = 12'h03C;
    localparam int CFG_INT_PIN           = 12'h03D;
    localparam int CFG_MIN_GNT           = 12'h03E;
    localparam int CFG_MAX_LAT           = 12'h03F;
    
    // Capability IDs
    localparam logic [7:0] CAP_ID_PM           = 8'h01;
    localparam logic [7:0] CAP_ID_AGP          = 8'h02;
    localparam logic [7:0] CAP_ID_VPD          = 8'h03;
    localparam logic [7:0] CAP_ID_SLOT_ID      = 8'h04;
    localparam logic [7:0] CAP_ID_MSI          = 8'h05;
    localparam logic [7:0] CAP_ID_HOT_SWAP     = 8'h06;
    localparam logic [7:0] CAP_ID_PCIX         = 8'h07;
    localparam logic [7:0] CAP_ID_HYPERTRANS   = 8'h08;
    localparam logic [7:0] CAP_ID_VENDOR       = 8'h09;
    localparam logic [7:0] CAP_ID_DEBUG        = 8'h0A;
    localparam logic [7:0] CAP_ID_CPCI_CRC     = 8'h0B;
    localparam logic [7:0] CAP_ID_HOT_PLUG     = 8'h0C;
    localparam logic [7:0] CAP_ID_BRIDGE_SVID  = 8'h0D;
    localparam logic [7:0] CAP_ID_AGP8X        = 8'h0E;
    localparam logic [7:0] CAP_ID_SECURE       = 8'h0F;
    localparam logic [7:0] CAP_ID_PCIE         = 8'h10;
    localparam logic [7:0] CAP_ID_MSIX         = 8'h11;
    localparam logic [7:0] CAP_ID_SATA         = 8'h12;
    localparam logic [7:0] CAP_ID_AF           = 8'h13;
    
    // Extended Capability IDs
    localparam logic [15:0] ECAP_ID_AER        = 16'h0001;
    localparam logic [15:0] ECAP_ID_VC         = 16'h0002;
    localparam logic [15:0] ECAP_ID_SERIAL     = 16'h0003;
    localparam logic [15:0] ECAP_ID_PWR_BUDGET = 16'h0004;
    localparam logic [15:0] ECAP_ID_RCLINK     = 16'h0005;
    localparam logic [15:0] ECAP_ID_RCINTLINK  = 16'h0006;
    localparam logic [15:0] ECAP_ID_RCEC_ASSOC = 16'h0007;
    localparam logic [15:0] ECAP_ID_MFVC       = 16'h0008;
    localparam logic [15:0] ECAP_ID_VC2        = 16'h0009;
    localparam logic [15:0] ECAP_ID_RCRB       = 16'h000A;
    localparam logic [15:0] ECAP_ID_VENDOR     = 16'h000B;
    localparam logic [15:0] ECAP_ID_CAC        = 16'h000C;
    localparam logic [15:0] ECAP_ID_ACS        = 16'h000D;
    localparam logic [15:0] ECAP_ID_ARI        = 16'h000E;
    localparam logic [15:0] ECAP_ID_ATS        = 16'h000F;
    localparam logic [15:0] ECAP_ID_SRIOV      = 16'h0010;
    localparam logic [15:0] ECAP_ID_MRIOV      = 16'h0011;
    localparam logic [15:0] ECAP_ID_MULTICAST  = 16'h0012;
    localparam logic [15:0] ECAP_ID_PAGE_REQ   = 16'h0013;
    localparam logic [15:0] ECAP_ID_RESIZABLE_BAR = 16'h0015;
    localparam logic [15:0] ECAP_ID_DPA        = 16'h0016;
    localparam logic [15:0] ECAP_ID_TPH        = 16'h0017;
    localparam logic [15:0] ECAP_ID_LTR        = 16'h0018;
    localparam logic [15:0] ECAP_ID_SECONDARY  = 16'h0019;
    localparam logic [15:0] ECAP_ID_PMUX       = 16'h001A;
    localparam logic [15:0] ECAP_ID_PASID      = 16'h001B;
    localparam logic [15:0] ECAP_ID_LNR        = 16'h001C;
    localparam logic [15:0] ECAP_ID_DPC        = 16'h001D;
    localparam logic [15:0] ECAP_ID_L1PM_SUBSTATES = 16'h001E;
    localparam logic [15:0] ECAP_ID_PTM        = 16'h001F;
    localparam logic [15:0] ECAP_ID_FRS        = 16'h0021;
    localparam logic [15:0] ECAP_ID_RTR        = 16'h0022;
    localparam logic [15:0] ECAP_ID_VF_REBAR   = 16'h0024;
    localparam logic [15:0] ECAP_ID_DL_FEATURE = 16'h0025;
    localparam logic [15:0] ECAP_ID_PL16_MARGINING = 16'h0027;
    localparam logic [15:0] ECAP_ID_IDE        = 16'h0030;

    //=========================================================================
    // CONSTANTS
    //=========================================================================
    
    // Max Payload Sizes
    localparam int MPS_128  = 128;
    localparam int MPS_256  = 256;
    localparam int MPS_512  = 512;
    localparam int MPS_1024 = 1024;
    localparam int MPS_2048 = 2048;
    localparam int MPS_4096 = 4096;
    
    // Max Read Request Sizes
    localparam int MRRS_128  = 128;
    localparam int MRRS_256  = 256;
    localparam int MRRS_512  = 512;
    localparam int MRRS_1024 = 1024;
    localparam int MRRS_2048 = 2048;
    localparam int MRRS_4096 = 4096;
    
    // Timeouts (in ns)
    localparam int TIMEOUT_COMPLETION = 50000000;  // 50 ms
    localparam int TIMEOUT_REPLAY     = 1000000;   // 1 ms
    
    // Special characters (8b/10b)
    localparam logic [7:0] K28_0 = 8'h1C;  // SKP
    localparam logic [7:0] K28_1 = 8'h3C;  // FTS
    localparam logic [7:0] K28_2 = 8'h5C;  // SDP
    localparam logic [7:0] K28_3 = 8'h7C;  // IDL
    localparam logic [7:0] K28_4 = 8'h9C;  // Reserved
    localparam logic [7:0] K28_5 = 8'hBC;  // COM
    localparam logic [7:0] K28_6 = 8'hDC;  // STP
    localparam logic [7:0] K28_7 = 8'hFC;  // EDB
    localparam logic [7:0] K27_7 = 8'hFB;  // STP
    localparam logic [7:0] K29_7 = 8'hFD;  // END
    localparam logic [7:0] K30_7 = 8'hFE;  // EDB
    localparam logic [7:0] K23_7 = 8'hF7;  // PAD

    //=========================================================================
    // UTILITY FUNCTIONS
    //=========================================================================
    
    // Get speed in GT/s
    function automatic real get_speed_gtps(pcie_gen_e gen);
        case (gen)
            PCIE_GEN1: return 2.5;
            PCIE_GEN2: return 5.0;
            PCIE_GEN3: return 8.0;
            PCIE_GEN4: return 16.0;
            PCIE_GEN5: return 32.0;
            PCIE_GEN6: return 64.0;
            default:   return 2.5;
        endcase
    endfunction
    
    // Get encoding overhead
    function automatic real get_encoding_overhead(pcie_gen_e gen);
        if (gen <= PCIE_GEN2)
            return 0.8;           // 8b/10b = 80%
        else if (gen <= PCIE_GEN5)
            return 128.0/130.0;   // 128b/130b = 98.46%
        else
            return 0.98;          // Gen6 FLIT (approximate)
    endfunction
    
    // Calculate theoretical bandwidth in GB/s
    function automatic real calc_bandwidth_gbps(pcie_gen_e gen, pcie_width_e width);
        real speed = get_speed_gtps(gen);
        real overhead = get_encoding_overhead(gen);
        return (speed * int'(width) * overhead) / 8.0;
    endfunction
    
    // Check if TLP type is memory request
    function automatic bit is_mem_request(tlp_type_e t);
        return (t inside {TLP_MRD32, TLP_MRD64, TLP_MRDLK32, TLP_MRDLK64,
                          TLP_MWR32, TLP_MWR64});
    endfunction
    
    // Check if TLP type is posted
    function automatic bit is_posted(tlp_type_e t);
        return (t inside {TLP_MWR32, TLP_MWR64, TLP_MSG, TLP_MSGD});
    endfunction
    
    // Check if TLP type is completion
    function automatic bit is_completion(tlp_type_e t);
        return (t inside {TLP_CPL, TLP_CPLD, TLP_CPLLK, TLP_CPLDLK});
    endfunction
    
    // Check if TLP type has data
    function automatic bit has_data(tlp_fmt_e fmt);
        return (fmt inside {TLP_FMT_3DW_D, TLP_FMT_4DW_D});
    endfunction
    
    // Check if address is 64-bit
    function automatic bit is_64bit_addr(tlp_fmt_e fmt);
        return (fmt inside {TLP_FMT_4DW_ND, TLP_FMT_4DW_D});
    endfunction

endpackage : pcie_types_pkg

`endif // PCIE_TYPES_PKG_SV
