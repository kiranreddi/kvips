# PCIe VIP Integration Guide

## Table of Contents
1. [Overview](#1-overview)
2. [Prerequisites](#2-prerequisites)
3. [Directory Structure](#3-directory-structure)
4. [Interface Instantiation](#4-interface-instantiation)
5. [Environment Setup](#5-environment-setup)
6. [Agent Configuration](#6-agent-configuration)
7. [DUT Integration](#7-dut-integration)
8. [Back-to-Back Setup](#8-back-to-back-setup)
9. [Multi-Link Setup](#9-multi-link-setup)
10. [Scoreboards and Checkers](#10-scoreboards-and-checkers)
11. [LSF and Tool Setup](#11-lsf-and-tool-setup)
12. [Common Integration Patterns](#12-common-integration-patterns)

---

## 1. Overview

This guide walks through integrating the KVIPS PCIe VIP into your verification environment. Whether you're verifying an Endpoint (EP), Root Complex (RC), or Switch, this guide covers the necessary steps.

### Integration Scenarios

| Scenario | RC Agent | EP Agent | Description |
|----------|----------|----------|-------------|
| EP DUT Verification | VIP (Active) | DUT | Verify your EP with VIP RC |
| RC DUT Verification | DUT | VIP (Active) | Verify your RC with VIP EP |
| Switch DUT Verification | VIP (Active) | VIP (Active) | VIP on both ports |
| Back-to-Back (B2B) | VIP (Active) | VIP (Active) | No DUT, VIP validation |
| Passive Monitor | Monitor | Monitor | Observe existing link |

---

## 2. Prerequisites

### 2.1 Environment Setup

```bash
export KVIPS_HOME=/path/to/kvips
```

### 2.2 LSF Access for Tools

Many tools require LSF job submission:

```bash
source /tools/lsf/conf/profile.lsf
bsub -Ip -app gnrc -P boxsteru4 -Lp boxsteru4 -q interactive bash
```

---

## 3. Directory Structure

```
kvips/pcie/
├── sv/
│   ├── if/
│   ├── pkg/
│   ├── uvm/
│   └── assertions/
└── examples/
    └── uvm_back2back/
```

---

## 4. Interface Instantiation

### 4.1 PIPE Interface (PHY-MAC Boundary)

```systemverilog
pcie_pipe_if #(NUM_LANES, MAX_GEN, DATA_WIDTH) pcie (
  .pclk(pclk),
  .reset_n(reset_n)
);
```

---

## Agent note (2026-02-02T05:17:58-08:00)

- The example `uvm_back2back` currently instantiates a single PIPE interface and configures EP as `PCIE_MONITOR` to avoid multi-driving a single interface instance.
- Verified the example compile/elab/run on Questa/VCS/Xcelium via LSF interactive jobs in this environment.
