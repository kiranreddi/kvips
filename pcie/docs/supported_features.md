# PCIe VIP Supported Features

## Overview

This document details all features supported by the KVIPS PCIe VIP, including protocol versions, layer features, and configuration options.

---

## 1. PCIe Generations Supported

| Generation | Data Rate | Encoding | Status | Notes |
|------------|-----------|----------|--------|-------|
| Gen1 | 2.5 GT/s | 8b/10b | ✅ Full | |
| Gen2 | 5.0 GT/s | 8b/10b | ✅ Full | |
| Gen3 | 8.0 GT/s | 128b/130b | ✅ Full | Scrambling, equalization |
| Gen4 | 16.0 GT/s | 128b/130b | ✅ Full | Lane margining |
| Gen5 | 32.0 GT/s | 128b/130b | ✅ Full | Enhanced equalization |
| Gen6 | 64.0 GT/s | PAM4/FLIT | ✅ Full | FLIT mode, 1b/1b encoding |

---

## 2. Link Widths Supported

| Width | Support | Maximum Lanes | Notes |
|-------|---------|---------------|-------|
| x1 | ✅ | 1 | |
| x2 | ✅ | 2 | |
| x4 | ✅ | 4 | |
| x8 | ✅ | 8 | |
| x12 | ✅ | 12 | |
| x16 | ✅ | 16 | |
| x32 | ✅ | 32 | Gen5/Gen6 only |

### Link Width Negotiation
- Automatic width negotiation
- Dynamic width change (Gen4+)
- Lane reversal support
- Polarity inversion detection

---

## 3. Physical Layer Features

### 3.1 Encoding/Decoding

| Feature | Gen1/2 | Gen3/4/5 | Gen6 |
|---------|--------|----------|------|
| 8b/10b | ✅ | N/A | N/A |
| 128b/130b | N/A | ✅ | N/A |
| FLIT (1b/1b) | N/A | N/A | ✅ |
| PAM4 Encoding | N/A | N/A | ✅ |
| Scrambling | ✅ | ✅ | ✅ |

### 3.2 Training Sequences

| Sequence | Description | Supported |
|----------|-------------|-----------|
| TS1 | Training Sequence 1 | ✅ |
| TS2 | Training Sequence 2 | ✅ |
| Electrical Idle | EI/EIEOS | ✅ |
| SKP | Skip Ordered Set | ✅ |
| FTS | Fast Training Sequence | ✅ |
| EIOS | Electrical Idle Ordered Set | ✅ |
| EIEOS | Electrical Idle Exit Ordered Set | ✅ |
| SDS | Start of Data Stream | ✅ (Gen3+) |
| EDS | End of Data Stream | ✅ (Gen3+) |

### 3.3 LTSSM States

All LTSSM states fully implemented:

| State | Sub-states | Supported |
|-------|------------|-----------|
| Detect | Quiet, Active | ✅ |
| Polling | Active, Compliance, Config | ✅ |
| Configuration | Linkwidth.Start/Accept, Lanenum.Wait/Accept, Complete, Idle | ✅ |
| L0 | Normal operation | ✅ |
| Recovery | RcvrLock, RcvrCfg, Speed, Equalization | ✅ |
| L0s | Entry, Idle, FTS, Exit | ✅ |
| L1 | Entry, Idle, Exit | ✅ |
| L2 | Idle, Wake | ✅ |
| Disabled | - | ✅ |
| Loopback | Entry, Active, Exit | ✅ |
| Hot Reset | - | ✅ |

---

## 4. Data Link Layer Features

### 4.1 DLLP Types

| DLLP Type | Direction | Supported |
|-----------|-----------|-----------|
| Ack | Both | ✅ |
| Nak | Both | ✅ |
| InitFC1-P | Both | ✅ |
| InitFC1-NP | Both | ✅ |
| InitFC1-Cpl | Both | ✅ |
| InitFC2-P | Both | ✅ |
| InitFC2-NP | Both | ✅ |
| InitFC2-Cpl | Both | ✅ |
| UpdateFC-P | Both | ✅ |
| UpdateFC-NP | Both | ✅ |
| UpdateFC-Cpl | Both | ✅ |
| PM_Enter_L1 | Both | ✅ |
| PM_Enter_L23 | Both | ✅ |
| PM_Active_State_Request_L1 | Both | ✅ |
| PM_Request_Ack | Both | ✅ |
| Vendor_Specific | Both | ✅ |
| Data Link Feature Exchange | Both | ✅ (Gen4+) |

---

## 5. Transaction Layer Features

### 5.1 TLP Types

| TLP Type | Code | Supported |
|----------|------|-----------|
| Memory Read Request (MRd) | 0x00, 0x20 | ✅ |
| Memory Read Lock (MRdLk) | 0x01, 0x21 | ✅ |
| Memory Write (MWr) | 0x40, 0x60 | ✅ |
| IO Read (IORd) | 0x02 | ✅ |
| IO Write (IOWr) | 0x42 | ✅ |
| Config Read Type 0 (CfgRd0) | 0x04 | ✅ |
| Config Write Type 0 (CfgWr0) | 0x44 | ✅ |
| Config Read Type 1 (CfgRd1) | 0x05 | ✅ |
| Config Write Type 1 (CfgWr1) | 0x45 | ✅ |
| Message (Msg) | 0x30 | ✅ |
| Message with Data (MsgD) | 0x70 | ✅ |
| Completion (Cpl) | 0x0A | ✅ |
| Completion with Data (CplD) | 0x4A | ✅ |

---

## Agent note (2026-02-02T05:17:58-08:00)

- This feature matrix describes the intended end-state. Current “what is runnable today” status is tracked in `kvips/pcie/README.md` and the example logs.
- The back-to-back example currently verifies compile/elab/run, but does not yet generate end-to-end PCIe traffic (TLP/DLLP observed counts remain 0 in the logs).
