---
layout: default
title: FAQ - Frequently Asked Questions
permalink: /docs/faq/
---

# Frequently Asked Questions

Quick answers to common questions about KVIPS.

---

## General Questions

<details>
<summary><strong>What is KVIPS?</strong></summary>
<p>
KVIPS (K's Verification IP Suite) is a vendor-neutral, open-source library of SystemVerilog UVM verification components for protocol verification. It provides production-ready VIPs that work across multiple simulators.
</p>
</details>

<details>
<summary><strong>Is KVIPS free to use?</strong></summary>
<p>
Yes! KVIPS is released under the MIT License, which allows free use in both commercial and non-commercial projects. See the <a href="https://github.com/kiranreddi/kvips/blob/main/LICENSE">LICENSE</a> file for full details.
</p>
</details>

<details>
<summary><strong>Which simulators are supported?</strong></summary>
<p>
KVIPS is validated on:
<ul>
<li>Siemens Questa 2025.3_2</li>
<li>Synopsys VCS 2025.06_1</li>
<li>Cadence Xcelium 25.03.007</li>
</ul>
Older versions may also work but are not officially validated.
</p>
</details>

<details>
<summary><strong>Can I contribute to KVIPS?</strong></summary>
<p>
Absolutely! We welcome contributions. Please see our <a href="https://github.com/kiranreddi/kvips/blob/main/CONTRIBUTING.md">Contributing Guide</a> for details on how to get started.
</p>
</details>

---

## Technical Questions

<details>
<summary><strong>Do I need to know UVM to use KVIPS?</strong></summary>
<p>
Yes, KVIPS assumes basic familiarity with UVM methodology. If you're new to UVM, we recommend:
<ul>
<li><a href="https://www.accellera.org/downloads/standards/uvm">UVM 1.2 User Guide</a></li>
<li>Online UVM tutorials</li>
<li>Our <a href="/docs/getting-started/">Getting Started Guide</a></li>
</ul>
</p>
</details>

<details>
<summary><strong>How do I integrate KVIPS into my existing testbench?</strong></summary>
<p>
See our <a href="/docs/getting-started/">Getting Started Guide</a> and <a href="/docs/axi4/integration/">Integration Guide</a> for step-by-step instructions. The basic steps are:
<ol>
<li>Add KVIPS to your compilation</li>
<li>Instantiate the interface in your top module</li>
<li>Configure and create agents in your environment</li>
<li>Start sequences on the sequencers</li>
</ol>
</p>
</details>

<details>
<summary><strong>Can I use multiple VIPs together?</strong></summary>
<p>
Yes! KVIPS VIPs are designed to work together. You can instantiate multiple agents (same or different protocols) in your environment. See the multi-agent examples in the documentation.
</p>
</details>

<details>
<summary><strong>Does KVIPS support constrained random testing?</strong></summary>
<p>
Yes, all transaction classes use SystemVerilog constraints for randomization. You can:
<ul>
<li>Use built-in constraints</li>
<li>Add custom constraints via `uvm_do_with`</li>
<li>Extend transaction classes with additional constraints</li>
<li>Create custom sequences with specific randomization profiles</li>
</ul>
</p>
</details>

---

## AXI4 Specific

<details>
<summary><strong>What AXI4 features are supported?</strong></summary>
<p>
The AXI4 VIP supports:
<ul>
<li>All burst types (INCR, FIXED, WRAP)</li>
<li>Burst lengths up to 256 (INCR) or 16 (FIXED/WRAP)</li>
<li>All data widths (8, 16, 32, 64, 128, 256, 512, 1024 bits)</li>
<li>Exclusive accesses</li>
<li>Multiple outstanding transactions</li>
<li>Error responses (SLVERR, DECERR)</li>
<li>Protocol assertions (SVA)</li>
<li>Built-in scoreboard</li>
</ul>
</p>
</details>

<details>
<summary><strong>How do I enable pipelined/outstanding transactions?</strong></summary>
<p>
Configure the master agent:
```systemverilog
cfg.master_pipelined = 1;
cfg.max_outstanding_writes = 16;
cfg.max_outstanding_reads = 16;
```
Or use runtime plusarg: `+VIP_PIPE +VIP_MAX_OUTS=16`
</p>
</details>

<details>
<summary><strong>How do I inject errors?</strong></summary>
<p>
Configure the slave agent:
```systemverilog
cfg.slave_err_enable = 1;
cfg.slave_err_start = 32'hF000;
cfg.slave_err_end = 32'hFFFF;
cfg.slave_err_resp = AXI4_RESP_SLVERR;
cfg.slave_err_on_write = 1;
cfg.slave_err_on_read = 1;
```
Now accesses to 0xF000-0xFFFF will return SLVERR.
</p>
</details>

<details>
<summary><strong>Can I disable assertions at runtime?</strong></summary>
<p>
Yes, use these plusargs:
<ul>
<li>`+KVIPS_AXI4_ASSERT_OFF` - Disable all assertions</li>
<li>`+KVIPS_AXI4_ASSERT_BURST_OFF` - Disable burst legality checks</li>
<li>`+KVIPS_AXI4_ASSERT_EXCL_OFF` - Disable exclusive access checks</li>
<li>`+KVIPS_AXI4_ASSERT_KNOWN` - Enable X/Z checks</li>
</ul>
</p>
</details>

---

## Debugging

<details>
<summary><strong>How do I enable debug tracing?</strong></summary>
<p>
Use any of these methods:
<ul>
<li>Plusarg: `+VIP_TRACE`</li>
<li>Config: `cfg.trace_enable = 1;`</li>
<li>UVM verbosity: `+UVM_VERBOSITY=UVM_HIGH`</li>
<li>Component-specific: `+uvm_set_verbosity=*driver*,UVM_DEBUG`</li>
</ul>
</p>
</details>

<details>
<summary><strong>How do I dump waveforms?</strong></summary>
<p>
Use the plusarg `+KVIPS_WAVES` to enable wave dumping from the demo top:
<ul>
<li>Default: VCD (`kvips_axi4_b2b.vcd`)</li>
<li>Optional: FSDB when compiled with `FSDB` and the required Verdi/Novas PLI (see `axi4/examples/uvm_back2back/sim/run_questa_fsdb.sh`)</li>
</ul>
</p>
</details>

<details>
<summary><strong>My simulation hangs. What should I check?</strong></summary>
<p>
Common causes:
<ol>
<li><strong>Missing handshakes:</strong> Ensure VALID/READY signals are driven</li>
<li><strong>Clock/reset:</strong> Verify clock is toggling and reset is released</li>
<li><strong>Configuration:</strong> Check agent is configured as active</li>
<li><strong>Deadlock:</strong> Enable trace to see what's waiting</li>
<li><strong>Timeout:</strong> Add timeout logic in your test</li>
</ol>
</p>
</details>

<details>
<summary><strong>I'm getting UVM_ERROR. How do I debug?</strong></summary>
<p>
Steps to debug:
<ol>
<li>Read the error message carefully - it often points to the issue</li>
<li>Enable VIP trace: `+VIP_TRACE`</li>
<li>Check the line number and file in the error</li>
<li>Look for recent transaction activity before the error</li>
<li>Check assertions - they may have caught a protocol violation</li>
<li>Use waveforms to see signal-level activity</li>
</ol>
</p>
</details>

---

## Performance

<details>
<summary><strong>How can I speed up my simulation?</strong></summary>
<p>
Performance tips:
<ul>
<li>Disable assertions: `+KVIPS_AXI4_ASSERT_OFF`</li>
<li>Reduce verbosity: `+UVM_VERBOSITY=UVM_LOW`</li>
<li>Disable scoreboard if not needed: `+KVIPS_AXI4_SB_OFF`</li>
<li>Use pipelined mode for throughput</li>
<li>Minimize inter-transaction gaps</li>
<li>Don't dump waveforms unless debugging</li>
<li>Use sparse memory models</li>
</ul>
</p>
</details>

<details>
<summary><strong>How much memory does KVIPS use?</strong></summary>
<p>
Memory usage depends on:
<ul>
<li>Number of agents instantiated</li>
<li>Memory model size (if using slave memory)</li>
<li>Outstanding transaction limits</li>
<li>Scoreboard history depth</li>
</ul>
Typical usage is 100-500MB for a moderate testbench. Use sparse memory (associative arrays) for large address spaces.
</p>
</details>

---

## Compatibility

<details>
<summary><strong>Does KVIPS work with older simulator versions?</strong></summary>
<p>
Possibly, but not officially validated. We test on the versions listed above. Older versions may work if they support:
<ul>
<li>SystemVerilog IEEE 1800-2012 or later</li>
<li>UVM 1.1d or 1.2</li>
<li>Parameterized classes</li>
<li>SystemVerilog Assertions (SVA)</li>
</ul>
</p>
</details>

<details>
<summary><strong>Can I use KVIPS with cocotb?</strong></summary>
<p>
Not yet, but it's on the roadmap! We plan to add cocotb entry points for Python-based verification. Follow the <a href="https://github.com/kiranreddi/kvips">repository</a> for updates.
</p>
</details>

<details>
<summary><strong>Does KVIPS support formal verification?</strong></summary>
<p>
The SVA assertions can be used with formal tools for property verification. Full FPV testbenches are planned for future releases.
</p>
</details>

---

## Licensing & Support

<details>
<summary><strong>Can I use KVIPS in a commercial product?</strong></summary>
<p>
Yes! The MIT License allows commercial use. You can:
<ul>
<li>Use KVIPS in commercial verification projects</li>
<li>Modify and extend the code</li>
<li>Distribute your modifications (optional)</li>
</ul>
The only requirement is to include the original license notice.
</p>
</details>

<details>
<summary><strong>How do I get support?</strong></summary>
<p>
Multiple support channels:
<ul>
<li><strong>Documentation:</strong> Check our comprehensive docs</li>
<li><strong>GitHub Issues:</strong> <a href="https://github.com/kiranreddi/kvips/issues">Report bugs or request features</a></li>
<li><strong>Discussions:</strong> <a href="https://github.com/kiranreddi/kvips/discussions">Ask questions</a></li>
<li><strong>Email:</strong> For private inquiries</li>
</ul>
</p>
</details>

<details>
<summary><strong>Do you offer commercial support?</strong></summary>
<p>
We currently offer community support through GitHub. For commercial support inquiries (training, custom development, consulting), please contact us directly.
</p>
</details>

---

## Still have questions?

<div style="text-align: center; margin: 3rem 0; padding: 2rem; background: var(--bg-secondary); border-radius: var(--radius-xl);">
<p style="font-size: 1.125rem; margin-bottom: 1rem;">
Can't find what you're looking for?
</p>
<div style="display: flex; gap: 1rem; justify-content: center; flex-wrap: wrap;">
<a href="https://github.com/kiranreddi/kvips/discussions" class="btn btn-primary">Ask on Discussions</a>
<a href="https://github.com/kiranreddi/kvips/issues/new" class="btn btn-secondary">Open an Issue</a>
</div>
</div>
