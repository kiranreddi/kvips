# PCIe VIP Protocol Assertions (SVA)

## Overview

The KVIPS PCIe VIP includes comprehensive SystemVerilog Assertions (SVA) that verify protocol compliance across all layers: Physical Layer, Data Link Layer, and Transaction Layer.

---

## 1. Assertion Categories

### 1.1 Assertion Naming Convention

```
KVIPS_PCIE_<LAYER>_<SECTION>_<NUM>
```

Where:
- `LAYER`: PHY, DLL, TL
- `SECTION`: Spec section reference
- `NUM`: Assertion number

### 1.2 Runtime Control

```bash
# Disable all assertions
+KVIPS_PCIE_ASSERT_OFF

# Disable specific layer
+KVIPS_PCIE_ASSERT_PHY_OFF
+KVIPS_PCIE_ASSERT_DLL_OFF
+KVIPS_PCIE_ASSERT_TL_OFF

# Enable X/Z checks
+KVIPS_PCIE_ASSERT_KNOWN

# Enable verbose assertion messages
+KVIPS_PCIE_ASSERT_VERBOSE
```

---

## 2. Physical Layer Assertions

### 2.1 Training Sequence Assertions

| ID | Description | Spec Reference |
|----|-------------|----------------|
| KVIPS_PCIE_PHY_4_2_1 | TS1/TS2 must have valid symbol content | 4.2.1 |
| KVIPS_PCIE_PHY_4_2_2 | Electrical Idle must not be asserted during data transmission | 4.2.2 |
| KVIPS_PCIE_PHY_4_2_3 | SKP ordered sets must be sent within required interval | 4.2.3 |
| KVIPS_PCIE_PHY_4_2_4 | EIOS must precede Electrical Idle | 4.2.4 |
| KVIPS_PCIE_PHY_4_2_5 | EIEOS must follow Electrical Idle exit | 4.2.5 |

---

## 3. Data Link Layer Assertions

### 3.1 DLLP Assertions

| ID | Description | Spec Reference |
|----|-------------|----------------|
| KVIPS_PCIE_DLL_3_4_1 | DLLP CRC correctness | 3.4.1 |
| KVIPS_PCIE_DLL_3_4_2 | ACK DLLP sequence number validity | 3.4.2 |
| KVIPS_PCIE_DLL_3_4_3 | NAK DLLP timing and conditions | 3.4.3 |

---

## 4. Transaction Layer Assertions

### 4.1 TLP Format Assertions

| ID | Description | Spec Reference |
|----|-------------|----------------|
| KVIPS_PCIE_TL_2_2_1 | TLP header format/type encoding | 2.2.1 |
| KVIPS_PCIE_TL_2_2_2 | TLP length field accuracy | 2.2.2 |
| KVIPS_PCIE_TL_2_2_5 | Byte enable rules | 2.2.5 |

---

## Agent note (2026-02-02T05:17:58-08:00)

- The repository contains standalone assertion modules under `kvips/pcie/sv/assertions/`, but they are not currently bound/instantiated by `kvips/pcie/examples/uvm_back2back`.
