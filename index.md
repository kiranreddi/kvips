---
layout: default
title: KVIPS - Premium Verification IP Library
description: Industry-grade SystemVerilog UVM Verification IP Library. Protocol VIPs tested with Siemens Questa, Synopsys VCS, and Cadence Xcelium.
---

<!-- Hero Section -->
<section class="hero">
    <div class="hero-content">
        <h1 class="hero-title">🚀 Premium Verification IP Library</h1>
        <p class="hero-subtitle">Industry-grade SystemVerilog UVM verification components for modern semiconductor design verification</p>
        <div class="hero-buttons">
            <a href="{{ '/pages/docs/getting-started' | relative_url }}" class="btn btn-primary">Get Started</a>
            <a href="{{ '/pages/docs/axi4-vip' | relative_url }}" class="btn btn-outline">Browse VIPs</a>
            <a href="https://github.com/kiranreddi/kvips" class="btn btn-secondary" target="_blank" rel="noopener">View on GitHub</a>
        </div>
    </div>
</section>

<!-- Tool Support Badges -->
<section class="section-padding bg-secondary">
    <div class="container text-center">
        <h3 class="section-subtitle">Validated on Leading EDA Tools</h3>
        <div class="badge-container">
            <span class="badge badge-primary">Siemens Questa 2025.3_2</span>
            <span class="badge badge-info">Synopsys VCS 2025.06_1</span>
            <span class="badge badge-success">Cadence Xcelium 25.03.007</span>
        </div>
    </div>
</section>

<!-- Features Section -->
<section class="section-padding">
    <div class="container">
        <h2 class="section-title">Why Choose KVIPS?</h2>
        <div class="feature-grid">
            <div class="feature-item">
                <div class="feature-icon">⚡</div>
                <h3 class="feature-title">Production Ready</h3>
                <p class="feature-description">Extensively tested and validated against industry-leading EDA simulators. Each VIP includes comprehensive regression suites.</p>
            </div>
            <div class="feature-item">
                <div class="feature-icon">🎯</div>
                <h3 class="feature-title">UVM Compliant</h3>
                <p class="feature-description">Built on Accellera UVM 1.1d/1.2 standards with IEEE 1800 SystemVerilog. Seamlessly integrates with your existing testbenches.</p>
            </div>
            <div class="feature-item">
                <div class="feature-icon">🔧</div>
                <h3 class="feature-title">Highly Configurable</h3>
                <p class="feature-description">Extensive configuration knobs for delay modeling, error injection, outstanding transactions, and protocol-specific features.</p>
            </div>
            <div class="feature-item">
                <div class="feature-icon">📊</div>
                <h3 class="feature-title">Built-in Checkers</h3>
                <p class="feature-description">SystemVerilog Assertions (SVA) for protocol compliance, plus optional scoreboards for data integrity verification.</p>
            </div>
            <div class="feature-item">
                <div class="feature-icon">📚</div>
                <h3 class="feature-title">Comprehensive Docs</h3>
                <p class="feature-description">Detailed user guides, API references, integration guides, and working examples for rapid deployment.</p>
            </div>
            <div class="feature-item">
                <div class="feature-icon">🔓</div>
                <h3 class="feature-title">Vendor Neutral</h3>
                <p class="feature-description">No vendor lock-in. Pure SystemVerilog implementation works across Questa, VCS, and Xcelium without modification.</p>
            </div>
        </div>
    </div>
</section>

<!-- Available VIPs -->
<section class="section-padding bg-secondary">
    <div class="container">
        <h2 class="section-title">Available Verification IPs</h2>
        
        <div class="vip-grid">
            <!-- AXI4 VIP Card -->
            <div class="vip-card">
                <div class="vip-card-header">
                    <div class="vip-icon">🔌</div>
                    <div>
                        <h3 class="vip-title">AXI4 Full</h3>
                        <div class="badge-group">
                            <span class="badge badge-success">Stable</span>
                            <span class="badge badge-gray">v1.0</span>
                        </div>
                    </div>
                </div>
                <div class="vip-card-body">
                    <p class="vip-description"><strong>AMBA AXI4 Full Protocol VIP</strong></p>
                    <ul class="vip-features">
                        <li>Master & Slave agents with configurable memory model</li>
                        <li>INCR/FIXED/WRAP bursts (up to 256 beats)</li>
                        <li>Exclusive access support with reservation tracking</li>
                        <li>Multiple outstanding transactions (pipelined mode)</li>
                        <li>Configurable delays, backpressure, error injection</li>
                        <li>Comprehensive SVA protocol checkers</li>
                        <li>Built-in scoreboard for data verification</li>
                    </ul>
                    <div class="vip-actions">
                        <a href="{{ '/pages/docs/axi4-vip' | relative_url }}" class="btn btn-primary btn-sm">Documentation</a>
                        <a href="{{ '/pages/docs/getting-started' | relative_url }}" class="btn btn-secondary btn-sm">Quick Start</a>
                    </div>
                </div>
            </div>

            <!-- Placeholder for Future VIPs -->
            <div class="vip-card vip-card-coming-soon">
                <div class="vip-card-header">
                    <div class="vip-icon vip-icon-disabled">🚧</div>
                    <div>
                        <h3 class="vip-title">More VIPs Coming Soon</h3>
                        <span class="badge badge-warning">In Development</span>
                    </div>
                </div>
                <div class="vip-card-body">
                    <p class="vip-description"><strong>Roadmap:</strong></p>
                    <ul class="vip-features">
                        <li>APB (Advanced Peripheral Bus)</li>
                        <li>AHB (Advanced High-performance Bus)</li>
                        <li>PCIe (PCI Express)</li>
                        <li>USB 2.0 / 3.0</li>
                        <li>Ethernet (MAC/PHY)</li>
                        <li>I2C, SPI, UART</li>
                    </ul>
                    <p class="contribution-note">
                        Contributions welcome! Check our <a href="https://github.com/kiranreddi/kvips/blob/main/CONTRIBUTING.md" target="_blank" rel="noopener">contribution guidelines</a>.
                    </p>
                </div>
            </div>
        </div>
    </div>
</section>

<!-- Technical Highlights -->
<section class="section-padding">
    <div class="container">
        <h2 class="section-title">Technical Highlights</h2>
        
        <div class="highlight-grid">
            <div class="highlight-card">
                <h4 class="highlight-title">🎮 Flexible Sequencing</h4>
                <p class="highlight-intro">Rich library of pre-built sequences including:</p>
                <ul class="highlight-list">
                    <li>Basic directed sequences</li>
                    <li>Constrained random sequences</li>
                    <li>Stress & corner-case sequences</li>
                    <li>Protocol-specific sequences</li>
                </ul>
            </div>

            <div class="highlight-card">
                <h4 class="highlight-title">🔍 Debug & Observability</h4>
                <p class="highlight-intro">Comprehensive debug capabilities:</p>
                <ul class="highlight-list">
                    <li>Transaction-level tracing</li>
                    <li>UVM transaction recording</li>
                    <li>Performance statistics</li>
                    <li>Runtime assertion control</li>
                </ul>
            </div>

            <div class="highlight-card">
                <h4 class="highlight-title">⚙️ Coverage Driven</h4>
                <p class="highlight-intro">Built-in functional coverage:</p>
                <ul class="highlight-list">
                    <li>Protocol feature coverage</li>
                    <li>Cross-coverage matrices</li>
                    <li>Transition coverage</li>
                    <li>Corner case tracking</li>
                </ul>
            </div>
        </div>
    </div>
</section>

<!-- Quick Start Example -->
<section class="section-padding bg-secondary">
    <div class="container">
        <h2 class="section-title">Quick Start Example</h2>
        <p class="section-subtitle">Get up and running in minutes with KVIPS</p>

        <div class="code-tabs">
            <div class="tab-buttons">
                <button class="tab-button active" data-tab="questa">Questa</button>
                <button class="tab-button" data-tab="vcs">VCS</button>
                <button class="tab-button" data-tab="xcelium">Xcelium</button>
            </div>

            <div class="tab-content active" data-tab="questa">
                <div class="code-block">
                    <pre><code class="language-bash"># Clone the repository
git clone https://github.com/kiranreddi/kvips.git
cd kvips

# Run AXI4 example on Questa
cd axi4/examples/uvm_back2back/sim
./run_questa.sh +UVM_TESTNAME=axi4_b2b_test

# Run full regression
./regress_questa_ignrc.sh</code></pre>
                </div>
            </div>

            <div class="tab-content" data-tab="vcs">
                <div class="code-block">
                    <pre><code class="language-bash"># Clone the repository
git clone https://github.com/kiranreddi/kvips.git
cd kvips

# Run AXI4 example on VCS
cd axi4/examples/uvm_back2back/sim
./run_vcs.sh +UVM_TESTNAME=axi4_b2b_test</code></pre>
                </div>
            </div>

            <div class="tab-content" data-tab="xcelium">
                <div class="code-block">
                    <pre><code class="language-bash"># Clone the repository
git clone https://github.com/kiranreddi/kvips.git
cd kvips

# Run AXI4 example on Xcelium
cd axi4/examples/uvm_back2back/sim
./run_xcelium.sh +UVM_TESTNAME=axi4_b2b_test</code></pre>
                </div>
            </div>
        </div>
    </div>
</section>

<!-- Integration Example -->
<section class="section-padding">
    <div class="container-narrow">
        <h2 class="section-title">Simple Integration</h2>

        <div class="code-block">
            <pre><code class="language-systemverilog">// Instantiate AXI4 interface
axi4_if #(
    .ADDR_W(32),
    .DATA_W(64),
    .ID_W(4)
) axi_if (
    .aclk(clk),
    .areset_n(rst_n)
);

// Configure and create agents
axi4_env_cfg cfg = new("cfg");
axi4_agent_cfg mst_cfg = new("mst_cfg");
mst_cfg.is_master = 1;
mst_cfg.vif = axi_if;
cfg.agent_cfgs.push_back(mst_cfg);

// Create environment
axi4_env env = axi4_env::type_id::create("env", this);
uvm_config_db#(axi4_env_cfg)::set(this, "env", "cfg", cfg);

// Start sequences
axi4_basic_write_seq seq = new("seq");
seq.start(env.get_master_sequencer(0));</code></pre>
        </div>
    </div>
</section>

<!-- Statistics -->
<section class="section-padding bg-secondary">
    <div class="container text-center">
        <h2 class="section-title">By the Numbers</h2>
        <div class="stats-grid">
            <div class="stat-item">
                <div class="stat-number stat-primary">1+</div>
                <div class="stat-label">Protocol VIPs</div>
            </div>
            <div class="stat-item">
                <div class="stat-number stat-secondary">3</div>
                <div class="stat-label">EDA Tools</div>
            </div>
            <div class="stat-item">
                <div class="stat-number stat-accent">100%</div>
                <div class="stat-label">UVM Compliant</div>
            </div>
            <div class="stat-item">
                <div class="stat-number stat-info">∞</div>
                <div class="stat-label">No Vendor Lock-in</div>
            </div>
        </div>
    </div>
</section>

<!-- Call to Action -->
<section class="section-padding">
    <div class="container">
        <div class="cta-box">
            <h2 class="cta-title">Ready to Accelerate Your Verification?</h2>
            <p class="cta-subtitle">Start using KVIPS today and experience professional-grade verification IPs.</p>
            <div class="cta-buttons">
                <a href="{{ '/pages/docs/getting-started' | relative_url }}" class="btn btn-primary btn-lg">Get Started Now</a>
                <a href="{{ '/pages/docs' | relative_url }}" class="btn btn-outline btn-lg">Read the Docs</a>
            </div>
        </div>
    </div>
</section>
