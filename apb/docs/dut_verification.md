# APB4 RTL-DUT verification milestone

The APB4 DUT example connects the KVIPS master to a real signal-level RTL
device under test.  It is separate from the APB master/slave back-to-back
demo and is intended to prove that the VIP drives and checks an executable
responder.

```text
KVIPS APB master agent
        |
   apb_if + APB SVA + monitor
        |
apb_ram_slave (byte-addressed RTL DUT)
        |
KVIPS scoreboard and transaction checks
```

The DUT supports APB4 `PSTRB` masked writes, captures `PPROT`, inserts a
configured number of wait cycles, initializes its memory on reset, returns
`PSLVERR` for unmapped byte lanes, and drives read data from the same byte
array that writes update.  No force statements, DPI, or simulator-encrypted
code are used.

## Executed tests

| Test | Checks |
|---|---|
| `apb_dut_smoke_test` | Deterministic writes and readback |
| `apb_dut_back_to_back_test` | Continuous transfers with `PSEL` retained |
| `apb_dut_apb4_strobe_test` | Directed `PSTRB` byte masking and readback |
| `apb_dut_pprot_test` | APB4 protection attribute variation |
| `apb_dut_wait_state_test` | Explicit wait-cycle count and stable controls |
| `apb_dut_boundary_test` | Last mapped 32-bit word at the memory boundary |
| `apb_dut_error_test` | Unmapped write/read `PSLVERR` checks |
| `apb_dut_stress_test` | Randomized APB4 reads, writes, strobes, and protection |

The commercial regression gate requires each test to produce nonzero monitor
write/read counts, matching scoreboard counts, zero read mismatches, and no
UVM or simulator errors.  The error test additionally requires an observed
nonzero `PSLVERR` count; other tests require zero errors.

Run with LSF and the requested commercial tools:

```bash
make -C apb/examples regress-rtl-questa USE_LSF=1 \
  LSF_BSUB='bsub -Ip -P boxsteru4 -q interactive'
make -C apb/examples regress-rtl-vcs USE_LSF=1 \
  LSF_BSUB='bsub -Ip -P boxsteru4 -q interactive'
make -C apb/examples regress-rtl-xcelium USE_LSF=1 \
  LSF_BSUB='bsub -Ip -P boxsteru4 -q interactive'
```

GitHub Actions runs the Verilator DUT list separately.  Per-test logs and
`regress.log` are written under
`apb/examples/uvm_dut/sim/out/<sim>/`.  Verilator remains a CI-only lint and
regression path; it is not part of the local commercial-simulator evidence.

## Remaining boundaries

This is a focused single-device APB4 target.  It does not claim coverage of
interconnect arbitration, multiple independently selected slaves, or an
external open-source master.  Those are the next integration milestones.
