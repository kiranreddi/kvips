---
layout: default
title: VIP Catalog
permalink: /vips/
---

# Verification IP Catalog

<div class="container-narrow">
<p style="font-size: 1.25rem; color: var(--text-secondary); text-align: center; margin: 2rem 0;">
Explore our collection of professional-grade SystemVerilog UVM verification IPs, validated on leading EDA simulators.
</p>
</div>

---

## 🔌 Available VIPs

<div class="grid grid-2" style="margin: 2rem 0;">

<!-- AXI4 Full VIP -->
<div class="card">
  <div class="card-header">
    <div class="card-icon">🔌</div>
    <div>
      <h3 class="card-title" style="margin: 0;">AXI4 Full</h3>
      <div style="margin-top: 0.5rem;">
        <span class="badge badge-success">Stable v1.0</span>
        <span class="badge badge-primary">UVM 1.2</span>
      </div>
    </div>
  </div>
  <div class="card-body">
    <h4>AMBA AXI4 Full Protocol</h4>
    <p>Complete master/slave verification IP for AMBA AXI4 (full) with extensive protocol checking and built-in scoreboard.</p>
    
    <h5>Key Features:</h5>
    <ul>
      <li>Master & Slave agents with configurable memory</li>
      <li>All burst types: INCR, FIXED, WRAP</li>
      <li>Exclusive access with reservation tracking</li>
      <li>Pipelined outstanding transactions</li>
      <li>Error injection (SLVERR, DECERR)</li>
      <li>Comprehensive SVA protocol checkers</li>
      <li>Performance statistics</li>
    </ul>
    
    <h5>Validated On:</h5>
    <div style="display: flex; gap: 0.5rem; flex-wrap: wrap; margin-bottom: 1rem;">
      <span class="badge badge-info">Questa 2025.3_2</span>
      <span class="badge badge-info">VCS 2025.06_1</span>
      <span class="badge badge-info">Xcelium 25.03.007</span>
    </div>
    
    <div style="display: flex; gap: 0.5rem; margin-top: 1.5rem;">
      <a href="/docs/axi4-vip/" class="btn btn-primary" style="font-size: 0.875rem; padding: 0.5rem 1rem;">Documentation</a>
      <a href="/docs/getting-started/" class="btn btn-secondary" style="font-size: 0.875rem; padding: 0.5rem 1rem;">Quick Start</a>
    </div>
  </div>
</div>

<!-- APB VIP -->
<div class="card">
  <div class="card-header">
    <div class="card-icon">🔌</div>
    <div>
      <h3 class="card-title" style="margin: 0;">APB</h3>
      <div style="margin-top: 0.5rem;">
        <span class="badge badge-warning">Beta v0.1</span>
        <span class="badge badge-primary">UVM 1.2</span>
      </div>
    </div>
  </div>
  <div class="card-body">
    <h4>Advanced Peripheral Bus</h4>
    <p>Master/slave VIP for AMBA APB3/APB4, ideal for low-bandwidth peripheral and register access verification.</p>
    
    <h5>Key Features:</h5>
    <ul>
      <li>Single-image APB3/APB4 support (runtime switch)</li>
      <li>Configurable wait states</li>
      <li>Error response injection</li>
      <li>Protocol compliance checking</li>
      <li>Monitor coverage + optional transaction recording</li>
    </ul>
    
    <h5>Validated On:</h5>
    <div style="display: flex; gap: 0.5rem; flex-wrap: wrap; margin-bottom: 1rem;">
      <span class="badge badge-info">Questa 2025.3_2</span>
      <span class="badge badge-info">VCS 2025.06_1</span>
      <span class="badge badge-info">Xcelium 25.03.007</span>
    </div>

    <div style="display: flex; gap: 0.5rem; margin-top: 1.5rem;">
      <a href="/docs/apb-vip/" class="btn btn-primary" style="font-size: 0.875rem; padding: 0.5rem 1rem;">Documentation</a>
      <a href="/docs/getting-started/" class="btn btn-secondary" style="font-size: 0.875rem; padding: 0.5rem 1rem;">Quick Start</a>
    </div>
  </div>
</div>

</div>

---

## 🗺️ VIP Roadmap

<div class="container">

### Phase 1: Bus Protocols (In Progress)

<table>
<thead>
<tr>
<th>Protocol</th>
<th>Status</th>
<th>Target</th>
<th>Priority</th>
</tr>
</thead>
<tbody>
<tr>
<td><strong>AXI4 Full</strong></td>
<td><span class="badge badge-success">✅ Complete</span></td>
<td>v1.0</td>
<td>High</td>
</tr>
<tr>
<td><strong>APB</strong></td>
<td><span class="badge badge-warning">🧪 Beta</span></td>
<td>v0.1</td>
<td>High</td>
</tr>
<tr>
<td><strong>AHB</strong></td>
<td><span class="badge badge-warning">🧪 Beta</span></td>
<td>v0.1</td>
<td>Medium</td>
</tr>
<tr>
<td><strong>AXI-Lite</strong></td>
<td><span class="badge badge-warning">📋 Planned</span></td>
<td>Q2 2026</td>
<td>Medium</td>
</tr>
<tr>
<td><strong>AXI-Stream</strong></td>
<td><span class="badge badge-warning">📋 Planned</span></td>
<td>Q3 2026</td>
<td>Medium</td>
</tr>
</tbody>
</table>

### Phase 2: High-Speed Interfaces

<table>
<thead>
<tr>
<th>Protocol</th>
<th>Status</th>
<th>Target</th>
<th>Priority</th>
</tr>
</thead>
<tbody>
<tr>
<td><strong>PCIe</strong></td>
<td><span class="badge badge-warning">📋 Planned</span></td>
<td>Q4 2026</td>
<td>High</td>
</tr>
<tr>
<td><strong>USB 2.0</strong></td>
<td><span class="badge badge-warning">📋 Planned</span></td>
<td>Q4 2026</td>
<td>Medium</td>
</tr>
<tr>
<td><strong>USB 3.0</strong></td>
<td><span class="badge badge-warning">📋 Planned</span></td>
<td>2027</td>
<td>Low</td>
</tr>
<tr>
<td><strong>Ethernet MAC</strong></td>
<td><span class="badge badge-warning">📋 Planned</span></td>
<td>2027</td>
<td>Medium</td>
</tr>
</tbody>
</table>

### Phase 3: Peripheral Interfaces

<table>
<thead>
<tr>
<th>Protocol</th>
<th>Status</th>
<th>Target</th>
<th>Priority</th>
</tr>
</thead>
<tbody>
<tr>
<td><strong>I2C</strong></td>
<td><span class="badge badge-warning">📋 Planned</span></td>
<td>Q3 2026</td>
<td>Medium</td>
</tr>
<tr>
<td><strong>SPI</strong></td>
<td><span class="badge badge-warning">📋 Planned</span></td>
<td>Q3 2026</td>
<td>Medium</td>
</tr>
<tr>
<td><strong>UART</strong></td>
<td><span class="badge badge-warning">📋 Planned</span></td>
<td>Q3 2026</td>
<td>Low</td>
</tr>
<tr>
<td><strong>GPIO</strong></td>
<td><span class="badge badge-warning">📋 Planned</span></td>
<td>Q4 2026</td>
<td>Low</td>
</tr>
</tbody>
</table>

</div>

---

## 🎯 VIP Selection Guide

### Choose the Right VIP

<div class="grid grid-3" style="margin: 2rem 0;">

<div class="card">
<h3>🚀 High Performance</h3>
<p><strong>Recommended VIPs:</strong></p>
<ul>
<li>AXI4 Full (pipelined mode)</li>
<li>AXI-Stream (coming soon)</li>
<li>PCIe (coming soon)</li>
</ul>
<p style="margin-top: 1rem; font-size: 0.875rem; color: var(--text-secondary);">
For high-bandwidth data transfer and DMA operations
</p>
</div>

<div class="card">
<h3>📝 Register Access</h3>
<p><strong>Recommended VIPs:</strong></p>
<ul>
<li>APB (beta)</li>
<li>AXI-Lite (coming soon)</li>
<li>AHB (beta)</li>
</ul>
<p style="margin-top: 1rem; font-size: 0.875rem; color: var(--text-secondary);">
For configuration registers and low-bandwidth control
</p>
</div>

<div class="card">
<h3>🔌 Peripherals</h3>
<p><strong>Recommended VIPs:</strong></p>
<ul>
<li>I2C (coming soon)</li>
<li>SPI (coming soon)</li>
<li>UART (coming soon)</li>
</ul>
<p style="margin-top: 1rem; font-size: 0.875rem; color: var(--text-secondary);">
For sensor interfaces and debug communications
</p>
</div>

</div>

---

## 📊 Feature Comparison

<table>
<thead>
<tr>
<th>Feature</th>
<th>AXI4</th>
<th>APB</th>
<th>AHB</th>
<th>PCIe</th>
</tr>
</thead>
<tbody>
<tr>
<td><strong>Master Agent</strong></td>
<td>✅</td>
<td>✅</td>
<td>✅</td>
<td>📋</td>
</tr>
<tr>
<td><strong>Slave Agent</strong></td>
<td>✅</td>
<td>✅</td>
<td>✅</td>
<td>📋</td>
</tr>
<tr>
<td><strong>Monitor</strong></td>
<td>✅</td>
<td>✅</td>
<td>✅</td>
<td>📋</td>
</tr>
<tr>
<td><strong>Protocol Assertions</strong></td>
<td>✅</td>
<td>✅</td>
<td>✅</td>
<td>📋</td>
</tr>
<tr>
<td><strong>Scoreboard</strong></td>
<td>✅</td>
<td>✅</td>
<td>✅</td>
<td>📋</td>
</tr>
<tr>
<td><strong>Coverage</strong></td>
<td>✅</td>
<td>✅</td>
<td>✅</td>
<td>📋</td>
</tr>
<tr>
<td><strong>Error Injection</strong></td>
<td>✅</td>
<td>✅</td>
<td>✅</td>
<td>📋</td>
</tr>
<tr>
<td><strong>Performance Stats</strong></td>
<td>✅</td>
<td>✅</td>
<td>✅</td>
<td>📋</td>
</tr>
</tbody>
</table>

<p style="text-align: center; margin-top: 1rem; color: var(--text-secondary);">
✅ Available &nbsp;&nbsp;&nbsp; 📋 Planned
</p>

---

## 🤝 Contributing

Want to see a specific VIP? Interested in contributing?

<div class="grid grid-2" style="margin: 2rem 0;">

<div class="card" style="background: linear-gradient(135deg, #667eea 0%, #764ba2 100%); color: white;">
<h3 style="color: white;">Request a VIP</h3>
<p style="color: rgba(255,255,255,0.95);">
Have a specific protocol in mind? Open a feature request and help us prioritize development.
</p>
<a href="https://github.com/kiranreddi/kvips/issues/new?template=feature_request.md" class="btn btn-outline" style="margin-top: 1rem;">
Request Feature
</a>
</div>

<div class="card" style="background: linear-gradient(135deg, #f093fb 0%, #f5576c 100%); color: white;">
<h3 style="color: white;">Contribute Code</h3>
<p style="color: rgba(255,255,255,0.95);">
Help expand the library! Check our contribution guidelines and submit a pull request.
</p>
<a href="https://github.com/kiranreddi/kvips/blob/main/CONTRIBUTING.md" class="btn btn-outline" style="margin-top: 1rem;">
Contribution Guide
</a>
</div>

</div>

---

## 📚 Resources

<div class="grid grid-3" style="margin: 2rem 0;">

<div class="card">
<h4>📖 Documentation</h4>
<ul style="margin: 0;">
<li><a href="/docs/getting-started/">Getting Started</a></li>
<li><a href="/docs/best-practices/">Best Practices</a></li>
<li><a href="/docs/code-review/">Code Review</a></li>
</ul>
</div>

<div class="card">
<h4>💬 Community</h4>
<ul style="margin: 0;">
<li><a href="https://github.com/kiranreddi/kvips/discussions">Discussions</a></li>
<li><a href="https://github.com/kiranreddi/kvips/issues">Issues</a></li>
<li><a href="https://github.com/kiranreddi/kvips/pulls">Pull Requests</a></li>
</ul>
</div>

<div class="card">
<h4>🔧 Examples</h4>
<ul style="margin: 0;">
<li><a href="https://github.com/kiranreddi/kvips/tree/main/axi4/examples">AXI4 Examples</a></li>
<li><a href="/docs/examples/">Example Gallery</a></li>
<li><a href="/docs/tutorials/">Tutorials</a></li>
</ul>
</div>

</div>

---

<div style="text-align: center; margin: 3rem 0; padding: 2rem; background: var(--bg-secondary); border-radius: var(--radius-xl);">
<h3>Ready to Start Verification?</h3>
<p style="font-size: 1.125rem; color: var(--text-secondary); margin: 1rem 0;">
Download KVIPS and accelerate your verification efforts today!
</p>
<a href="/docs/getting-started/" class="btn btn-primary">Get Started</a>
</div>
