# AXI4 coverage and replay targets

The monitor's counters and covergroups provide observability, but they are not
a closure claim by themselves. The portable closure target for this VIP is
the requirement matrix in [`axi4_spec_coverage.md`](axi4_spec_coverage.md) plus
a passing simulator result for every listed directed test.

The replay input format is simulator-neutral. Validate the checked-in sample:

```sh
python3 axi4/tools/axi4_csv_replay.py \
  axi4/examples/uvm_back2back/replay/sample.csv
python3 axi4/tools/axi4_csv_replay.py --json \
  axi4/examples/uvm_back2back/replay/sample.csv
```

Each CSV row is one transaction. `beats` is the number of transfers (not the
AXI `AxLEN` encoding), `size` is the AXI size exponent, and write `data_hex`
and `strb_hex` vectors use `|` between beats. The validator checks burst
limits, WRAP alignment, 4KB boundaries, field widths, and write-vector length.
It does not replace a protocol checker or simulator replay sequence.

## Closure dimensions

| Dimension | Required evidence | Current status |
|---|---|---|
| Channel handshakes and stability | Assertions plus backpressure tests | Covered for the supplied Full master/slave pair |
| Burst legality | SVA and directed INCR/FIXED/WRAP tests | Covered for generated legal traffic |
| Byte lanes and strobes | Strobe, unaligned, and narrow tests | Covered for the configured bus width |
| IDs and responses | Same-ID, cross-ID, B/R checker, and exclusive tests | Covered for the single-interface model; exhaustive permutations remain open |
| Reset and timeout | Pipelined/non-pipelined reset and timeout recovery tests | Covered for configured driver paths |
| Sideband policy | Configurable allow-mask checker and directed test | Covered as environment policy, not universal cache/QoS semantics |
| AXI4-Lite | Separate interface and three-simulator loopback | Basic standalone example; no Full-agent-equivalent Lite UVM package |
| Toggle/formal/traffic closure | Tool-specific coverage database and formal proof | Not claimed by this vendor-neutral repository |
