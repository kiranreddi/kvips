---
layout: default
title: KVIPS — Professional Verification IP Suite
description: Production-grade SystemVerilog UVM Verification IPs for AMBA AXI4, AHB, and APB protocols. Vendor-neutral, tested on Questa, VCS, Xcelium, and Verilator.
---

<!-- ============================== HERO ============================== -->
<section class="hero">
  <div class="hero-inner">
    <p class="hero-eyebrow">KVIPS — Verification IP Suite</p>
    <h1>Verification IP<br>that <span class="grad">ships silicon</span></h1>
    <p class="hero-sub">
      Enterprise-grade SystemVerilog UVM VIPs for AMBA AXI4, AHB, and APB.
      Production-ready regressions, built-in protocol checkers, and Verilator-compatible CI flows.
    </p>
    <div class="hero-metrics">
      <div class="hero-metric">
        <span class="hero-metric-val">3</span>
        <span class="hero-metric-lbl">Protocol VIPs</span>
      </div>
      <div class="hero-metric">
        <span class="hero-metric-val">4</span>
        <span class="hero-metric-lbl">EDA Tools</span>
      </div>
      <div class="hero-metric">
        <span class="hero-metric-val">50+</span>
        <span class="hero-metric-lbl">SV Source Files</span>
      </div>
      <div class="hero-metric">
        <span class="hero-metric-val">30+</span>
        <span class="hero-metric-lbl">Regression Tests</span>
      </div>
    </div>
    <div class="hero-actions">
      <a href="{{ '/docs/getting-started/' | relative_url }}" class="btn btn-primary btn-lg">Get Started</a>
      <a href="{{ '/docs/axi4-vip/' | relative_url }}" class="btn btn-outline btn-lg">AXI4 VIP Guide</a>
      <a href="https://github.com/kiranreddi/kvips" class="btn btn-outline btn-lg" target="_blank" rel="noopener">View on GitHub</a>
    </div>
  </div>
</section>

<!-- ============================== TOOL BAR ============================== -->
<section class="section--alt" style="padding:1.5rem 0">
  <div class="container text-center">
    <div class="tool-bar">
      <span class="tool-badge"><span class="dot dot-green"></span> Siemens Questa 2025.3</span>
      <span class="tool-badge"><span class="dot dot-blue"></span> Synopsys VCS 2025.06</span>
      <span class="tool-badge"><span class="dot dot-purple"></span> Cadence Xcelium 25.03</span>
      <span class="tool-badge"><span class="dot dot-gray"></span> Verilator 5.x</span>
    </div>
  </div>
</section>

<!-- ============================== FEATURES ============================== -->
<section class="section">
  <div class="container">
    <div class="section-header">
      <span class="section-tag">Why KVIPS</span>
      <h2>Built for Verification Engineers</h2>
      <p>Every VIP is designed for real silicon projects — comprehensive, configurable, and vendor-neutral.</p>
    </div>
    <div class="feature-grid">
      <div class="feature-card">
        <div class="feature-icon fi-blue">&#9889;</div>
        <h3>Production Ready</h3>
        <p>Tested and validated against leading EDA simulators with comprehensive CI-driven regression suites on every commit.</p>
      </div>
      <div class="feature-card">
        <div class="feature-icon fi-green">&#9745;</div>
        <h3>UVM 1.1d / 1.2 Compliant</h3>
        <p>Built on Accellera UVM with IEEE 1800 SystemVerilog. Seamlessly integrates with existing testbenches and methodologies.</p>
      </div>
      <div class="feature-card">
        <div class="feature-icon fi-purple">&#9881;</div>
        <h3>Highly Configurable</h3>
        <p>Extensive knobs for delay modeling, error injection, outstanding transactions, backpressure, and protocol-specific features.</p>
      </div>
      <div class="feature-card">
        <div class="feature-icon fi-amber">&#128202;</div>
        <h3>SVA Protocol Checkers</h3>
        <p>SystemVerilog Assertions for protocol compliance, plus optional scoreboards for byte-accurate data integrity verification.</p>
      </div>
      <div class="feature-card">
        <div class="feature-icon fi-cyan">&#128218;</div>
        <h3>Comprehensive Docs</h3>
        <p>Detailed user guides, architecture overviews, configuration references, and working back-to-back examples for each VIP.</p>
      </div>
      <div class="feature-card">
        <div class="feature-icon fi-pink">&#128275;</div>
        <h3>Vendor Neutral</h3>
        <p>No vendor lock-in. Pure SystemVerilog works on Questa, VCS, Xcelium, and Verilator without modification or licensing.</p>
      </div>
    </div>
  </div>
</section>

<!-- ============================== VIP CARDS ============================== -->
<section class="section section--alt">
  <div class="container">
    <div class="section-header">
      <span class="section-tag">VIP Catalog</span>
      <h2>Available Verification IPs</h2>
      <p>Each VIP includes master + slave agents, passive monitor, protocol assertions, scoreboard, sequences, and example testbenches.</p>
    </div>
    <div class="vip-grid">

      <!-- AXI4 -->
      <div class="vip-card">
        <div class="vip-card-head">
          <div class="proto-icon proto-axi4">AXI4</div>
          <div>
            <h3>AXI4 Full Protocol VIP</h3>
            <div class="badge-row">
              <span class="badge badge-green">Stable v1.0</span>
              <span class="badge badge-blue">AMBA 4.0</span>
            </div>
          </div>
        </div>
        <div class="vip-card-body">
          <p>Complete AMBA AXI4 (full) master &amp; slave agents with pipelined multi-outstanding transactions.</p>
          <ul>
            <li>INCR / FIXED / WRAP bursts (up to 256 beats)</li>
            <li>Exclusive access with per-ID reservation tracking</li>
            <li>Multiple outstanding transactions (pipelined mode)</li>
            <li>Error injection with configurable address ranges</li>
            <li>Comprehensive SVA — 4KB boundary, burst legality, handshake</li>
            <li>Byte-addressed scoreboard with WSTRB-aware checking</li>
            <li>Performance statistics — latency, stall cycles, throughput</li>
          </ul>
          <div class="vip-card-actions">
            <a href="{{ '/docs/axi4-vip/' | relative_url }}" class="btn btn-primary btn-sm">Documentation</a>
            <a href="{{ '/docs/getting-started/' | relative_url }}" class="btn btn-ghost btn-sm">Quick Start</a>
          </div>
        </div>
      </div>

      <!-- AHB -->
      <div class="vip-card">
        <div class="vip-card-head">
          <div class="proto-icon proto-ahb">AHB</div>
          <div>
            <h3>AHB-Lite / AHB Full VIP</h3>
            <div class="badge-row">
              <span class="badge badge-green">Stable v1.0</span>
              <span class="badge badge-blue">AMBA 3.0</span>
            </div>
          </div>
        </div>
        <div class="vip-card-body">
          <p>Single-image AHB VIP supporting both AHB-Lite and AHB Full, selectable at runtime.</p>
          <ul>
            <li>Master &amp; Slave agents with burst support (INCR / WRAP)</li>
            <li>Runtime AHB-Lite / AHB Full mode selection</li>
            <li>Configurable wait states and stall injection</li>
            <li>Two-cycle error response (AMBA-compliant)</li>
            <li>Variable HSIZE (byte to dword transfers)</li>
            <li>Protocol assertions, coverage, and scoreboard</li>
          </ul>
          <div class="vip-card-actions">
            <a href="{{ '/docs/ahb-vip/' | relative_url }}" class="btn btn-primary btn-sm">Documentation</a>
            <a href="{{ '/docs/getting-started/' | relative_url }}" class="btn btn-ghost btn-sm">Quick Start</a>
          </div>
        </div>
      </div>

      <!-- APB -->
      <div class="vip-card">
        <div class="vip-card-head">
          <div class="proto-icon proto-apb">APB</div>
          <div>
            <h3>APB3 / APB4 Protocol VIP</h3>
            <div class="badge-row">
              <span class="badge badge-green">Stable v1.0</span>
              <span class="badge badge-blue">AMBA 4.0</span>
            </div>
          </div>
        </div>
        <div class="vip-card-body">
          <p>Single-image APB VIP with runtime APB3/APB4 switching for register access testing.</p>
          <ul>
            <li>Master &amp; Slave agents with memory model</li>
            <li>Single-image APB3 / APB4 with runtime switch</li>
            <li>Configurable wait states (PREADY control)</li>
            <li>PPROT &amp; PSTRB support (APB4 features)</li>
            <li>Error injection (PSLVERR) with address ranges</li>
            <li>Protocol assertions, scoreboard, and coverage</li>
          </ul>
          <div class="vip-card-actions">
            <a href="{{ '/docs/apb-vip/' | relative_url }}" class="btn btn-primary btn-sm">Documentation</a>
            <a href="{{ '/docs/getting-started/' | relative_url }}" class="btn btn-ghost btn-sm">Quick Start</a>
          </div>
        </div>
      </div>

      <!-- Roadmap -->
      <div class="vip-card vip-card--muted">
        <div class="vip-card-head">
          <div class="proto-icon proto-soon">...</div>
          <div>
            <h3>More VIPs on the Roadmap</h3>
            <div class="badge-row">
              <span class="badge badge-amber">Planned</span>
            </div>
          </div>
        </div>
        <div class="vip-card-body">
          <p>Additional protocols under development:</p>
          <ul>
            <li>AXI4-Lite (Q2 2026)</li>
            <li>AXI4-Stream (Q3 2026)</li>
            <li>I2C / SPI / UART (Q3–Q4 2026)</li>
            <li>PCIe Gen3/4/5 (Q4 2026)</li>
            <li>USB 2.0 / 3.x (2027)</li>
          </ul>
          <p style="font-size:.8rem;color:var(--text-muted)">Contributions welcome! See the <a href="https://github.com/kiranreddi/kvips">GitHub repo</a>.</p>
        </div>
      </div>

    </div>
  </div>
</section>

<!-- ============================== ARCHITECTURE ============================== -->
<section class="section">
  <div class="container">
    <div class="section-header">
      <span class="section-tag">Architecture</span>
      <h2>Unified VIP Architecture</h2>
      <p>Every KVIPS VIP follows a consistent UVM architecture pattern for maximum reusability.</p>
    </div>
    <div class="arch-diagram">
      <pre>
  ┌─────────────────── UVM Environment ───────────────────┐
  │                                                        │
  │   ┌──── Master Agent ────┐   ┌──── Slave Agent ─────┐ │
  │   │  ┌──────────────┐    │   │    ┌──────────────┐   │ │
  │   │  │  Sequencer    │    │   │    │  Sequencer   │   │ │
  │   │  └──────┬───────┘    │   │    └──────┬───────┘   │ │
  │   │         │             │   │           │           │ │
  │   │  ┌──────▼───────┐    │   │    ┌──────▼───────┐   │ │
  │   │  │ Master Driver │    │   │    │ Slave Driver  │   │ │
  │   │  └──────┬───────┘    │   │    │ + Memory Model│   │ │
  │   │         │             │   │    └──────┬───────┘   │ │
  │   └─────────|─────────────┘   └───────────|───────────┘ │
  │             │                              │             │
  │   ┌─────── ▼ ─── Protocol Interface ───── ▼ ──────────┐ │
  │   │  clk, reset_n, VALID/READY channels, data buses   │ │
  │   │  ┌───────────────────────────────────────────────┐ │ │
  │   │  │         SVA Protocol Assertions               │ │ │
  │   │  └───────────────────────────────────────────────┘ │ │
  │   └───────────────────────────────────────────────────┘ │
  │             │                                           │
  │   ┌─────── ▼ ──────────┐                               │
  │   │   Passive Monitor   │──▶ Analysis Port              │
  │   │  + Coverage Model   │──▶ Transaction Logger         │
  │   └────────────────────┘──▶ Scoreboard                  │
  │                                                        │
  └────────────────────────────────────────────────────────┘
      </pre>
    </div>
  </div>
</section>

<!-- ============================== TECHNICAL HIGHLIGHTS ============================== -->
<section class="section section--alt">
  <div class="container">
    <div class="section-header">
      <span class="section-tag">Capabilities</span>
      <h2>Technical Highlights</h2>
    </div>
    <div class="highlight-grid">
      <div class="highlight-card">
        <h4>&#127918; Rich Sequence Library</h4>
        <ul>
          <li>Directed smoke &amp; single-beat sequences</li>
          <li>Constrained random burst generators</li>
          <li>Pipelined stress &amp; multi-outstanding</li>
          <li>Exclusive access, error injection, lane sweep</li>
          <li>Corner-case &amp; 4KB-boundary sequences</li>
        </ul>
      </div>
      <div class="highlight-card">
        <h4>&#128270; Debug &amp; Observability</h4>
        <ul>
          <li>Transaction-level tracing (+VIP_TRACE)</li>
          <li>UVM transaction recording (+VIP_TR)</li>
          <li>Performance statistics (+VIP_STATS)</li>
          <li>Runtime assertion enable/disable</li>
          <li>VCD / FSDB waveform auto-dump</li>
        </ul>
      </div>
      <div class="highlight-card">
        <h4>&#9881; Coverage Driven</h4>
        <ul>
          <li>Protocol feature covergroups</li>
          <li>Cross-coverage matrices (burst × size × len)</li>
          <li>Response type coverage</li>
          <li>Narrow transfer &amp; byte-lane coverage</li>
          <li>Outstanding transaction depth tracking</li>
        </ul>
      </div>
      <div class="highlight-card">
        <h4>&#128737; Protocol Assertions</h4>
        <ul>
          <li>VALID/READY handshake stability</li>
          <li>4KB address boundary (AXI4)</li>
          <li>Burst type legality &amp; alignment</li>
          <li>Exclusive access protocol rules</li>
          <li>X/Z propagation detection</li>
        </ul>
      </div>
    </div>
  </div>
</section>

<!-- ============================== QUICK START ============================== -->
<section class="section">
  <div class="container">
    <div class="section-header">
      <span class="section-tag">Quick Start</span>
      <h2>Up and Running in Minutes</h2>
      <p>Clone, compile, and run — choose your simulator.</p>
    </div>

    <div class="code-tabs">
      <div class="tab-bar" role="tablist">
        <button class="tab-btn active" data-tab="questa" role="tab">Siemens Questa</button>
        <button class="tab-btn" data-tab="vcs" role="tab">Synopsys VCS</button>
        <button class="tab-btn" data-tab="xcelium" role="tab">Cadence Xcelium</button>
        <button class="tab-btn" data-tab="verilator" role="tab">Verilator</button>
      </div>
      <div class="tab-panel active" data-tab="questa" role="tabpanel">
        <pre><code># Clone the repository
git clone https://github.com/kiranreddi/kvips.git && cd kvips

# Run AXI4 smoke test on Questa
cd axi4/examples/uvm_back2back/sim
./run_questa.sh +UVM_TESTNAME=axi4_b2b_test

# Run full AXI4 regression
cd ../..
make regress-questa USE_LSF=1</code></pre>
      </div>
      <div class="tab-panel" data-tab="vcs" role="tabpanel">
        <pre><code># Clone the repository
git clone https://github.com/kiranreddi/kvips.git && cd kvips

# Run AXI4 smoke test on VCS
cd axi4/examples/uvm_back2back/sim
./run_vcs.sh +UVM_TESTNAME=axi4_b2b_test</code></pre>
      </div>
      <div class="tab-panel" data-tab="xcelium" role="tabpanel">
        <pre><code># Clone the repository
git clone https://github.com/kiranreddi/kvips.git && cd kvips

# Run AXI4 smoke test on Xcelium
cd axi4/examples/uvm_back2back/sim
./run_xcelium.sh +UVM_TESTNAME=axi4_b2b_test</code></pre>
      </div>
      <div class="tab-panel" data-tab="verilator" role="tabpanel">
        <pre><code># Clone the repository
git clone https://github.com/kiranreddi/kvips.git && cd kvips

# Run APB regression on Verilator (no commercial license needed)
cd apb/examples
make verilator TEST=apb_b2b_smoke_test

# Run AXI4 regression on Verilator
cd ../../axi4/examples
make verilator TEST=axi4_b2b_test</code></pre>
      </div>
    </div>
  </div>
</section>

<!-- ============================== INTEGRATION EXAMPLE ============================== -->
<section class="section section--alt">
  <div class="container-narrow">
    <div class="section-header">
      <span class="section-tag">Integration</span>
      <h2>Simple UVM Integration</h2>
      <p>Connect a KVIPS AXI4 VIP to your DUT in a few lines of SystemVerilog.</p>
    </div>
    <div class="code-block">
      <pre><code>// 1. Instantiate the parameterized interface
axi4_if #(.ADDR_W(32), .DATA_W(64), .ID_W(4)) axi_if (.aclk(clk), .areset_n(rst_n));

// 2. Configure agent
axi4_agent_cfg mst_cfg = new("mst_cfg");
mst_cfg.is_master = 1;
mst_cfg.vif       = axi_if;
mst_cfg.pipelined = 1;              // enable multi-outstanding
mst_cfg.max_outstanding_reads = 8;

// 3. Build environment
axi4_env_cfg env_cfg = new("env_cfg");
env_cfg.agent_cfgs.push_back(mst_cfg);
uvm_config_db#(axi4_env_cfg)::set(this, "env", "cfg", env_cfg);

// 4. Start your sequence
axi4_write_readback_seq#(32,64,4,1) seq = new("wrbk");
seq.num_txns  = 100;
seq.start_addr = 32'h0000_1000;
seq.start(env.agents[0].sqr);</code></pre>
    </div>
  </div>
</section>

<!-- ============================== COMPARISON TABLE ============================== -->
<section class="section">
  <div class="container">
    <div class="section-header">
      <span class="section-tag">Feature Matrix</span>
      <h2>VIP Feature Comparison</h2>
    </div>
    <div style="overflow-x:auto">
      <table class="comparison-table">
        <thead>
          <tr>
            <th>Feature</th>
            <th>AXI4 VIP</th>
            <th>AHB VIP</th>
            <th>APB VIP</th>
          </tr>
        </thead>
        <tbody>
          <tr><td>Master Agent</td><td class="check">&#10003;</td><td class="check">&#10003;</td><td class="check">&#10003;</td></tr>
          <tr><td>Slave Agent + Memory Model</td><td class="check">&#10003;</td><td class="check">&#10003;</td><td class="check">&#10003;</td></tr>
          <tr><td>Passive Monitor + Coverage</td><td class="check">&#10003;</td><td class="check">&#10003;</td><td class="check">&#10003;</td></tr>
          <tr><td>SVA Protocol Assertions</td><td class="check">&#10003;</td><td class="check">&#10003;</td><td class="check">&#10003;</td></tr>
          <tr><td>Scoreboard</td><td class="check">&#10003;</td><td class="check">&#10003;</td><td class="check">&#10003;</td></tr>
          <tr><td>Transaction Logger</td><td class="check">&#10003;</td><td class="check">&#10003;</td><td class="check">&#10003;</td></tr>
          <tr><td>Pipelined / Multi-Outstanding</td><td class="check">&#10003;</td><td>N/A</td><td>N/A</td></tr>
          <tr><td>Exclusive Access</td><td class="check">&#10003;</td><td>N/A</td><td>N/A</td></tr>
          <tr><td>Burst Support</td><td class="check">&#10003; INCR/FIXED/WRAP</td><td class="check">&#10003; INCR/WRAP</td><td>N/A</td></tr>
          <tr><td>Error Injection</td><td class="check">&#10003;</td><td class="check">&#10003;</td><td class="check">&#10003;</td></tr>
          <tr><td>Configurable Delays / Backpressure</td><td class="check">&#10003;</td><td class="check">&#10003;</td><td class="check">&#10003;</td></tr>
          <tr><td>Performance Statistics</td><td class="check">&#10003;</td><td class="planned">Planned</td><td class="planned">Planned</td></tr>
          <tr><td>Verilator CI Regression</td><td class="check">&#10003;</td><td class="check">&#10003;</td><td class="check">&#10003;</td></tr>
        </tbody>
      </table>
    </div>
  </div>
</section>

<!-- ============================== STATS ============================== -->
<section class="section section--alt">
  <div class="container text-center">
    <div class="section-header">
      <span class="section-tag">By the Numbers</span>
      <h2>Project Metrics</h2>
    </div>
    <div class="stats-grid">
      <div class="stat-card">
        <div class="stat-value">3</div>
        <div class="stat-label">Protocol VIPs</div>
      </div>
      <div class="stat-card">
        <div class="stat-value">50+</div>
        <div class="stat-label">Source Files</div>
      </div>
      <div class="stat-card">
        <div class="stat-value">30+</div>
        <div class="stat-label">Regression Tests</div>
      </div>
      <div class="stat-card">
        <div class="stat-value">4</div>
        <div class="stat-label">Simulators</div>
      </div>
    </div>
  </div>
</section>

<!-- ============================== CTA ============================== -->
<section class="section">
  <div class="container">
    <div class="cta-banner">
      <h2>Launch your verification stack in minutes</h2>
      <p>Curated quick starts, clean APIs, and battle-hardened regressions — ready for production silicon projects.</p>
      <div class="cta-actions">
        <a href="{{ '/docs/getting-started/' | relative_url }}" class="btn btn-primary btn-lg">Get Started Now</a>
        <a href="{{ '/docs/axi4-vip/' | relative_url }}" class="btn btn-outline btn-lg">Explore AXI4 VIP</a>
      </div>
    </div>
  </div>
</section>
