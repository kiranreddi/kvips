# AMBA AHB coverage review

This is an implementation review, not an Arm compliance certification. The
scope is the AHB/AHB-Lite protocol family; PCIe and unrelated protocols are out
of scope.

The review follows Arm's [AMBA system architecture overview](https://www.arm.com/architecture/system-architectures/amba)
and the [AMBA 5 AHB extensions](https://developer.arm.com/community/arm-community-blogs/b/architectures-and-processors-blog/posts/new-amba-specification-extends-security-to-embedded-design-amba-5-ahb5),
including the pipelined transfer model, `HTRANS`, `HREADY/HREADYOUT`, `HRESP`,
fixed/incrementing/wrapping bursts, BUSY, and the AHB5 `HNONSEC` sideband.

## Coverage matrix

| Protocol area | KVIPS status | Evidence / boundary |
|---|---|---|
| Address/control then data phase | Covered | Master/slave back-to-back environment and monitor reconstruction |
| `IDLE`, `NONSEQ`, `SEQ` | Covered | Driver and directed/random sequences |
| BUSY between burst beats | Covered for generated single-master traffic | `ahb_busy_test`; strict assertion switch is runtime controlled |
| `HREADY` wait states and stability | Covered | `ahb_wait_state_test`; SVA stability properties |
| `HRESP=OKAY/ERROR` | Covered | Smoke, error response, scoreboard response filtering |
| AHB Full `RETRY/SPLIT` encoding/timing | Directed model covered | `ahb_full_retry_test`, `ahb_full_split_test`; no interconnect `HSPLITx` ownership |
| SINGLE / INCR4/8/16 | Covered | Directed burst tests and random stress |
| WRAP4/8/16 | Covered for legal generated starts | Wrap test; driver checks span alignment and 1KB boundary |
| Transfer alignment and bus-width legality | Covered on master stimulus and optional strict SVA | `ahb_cfg.legal_transfer()`, `ahb_legality_test`, and `+KVIPS_AHB_ASSERT_STRICT_ON`; external illegal-traffic injection remains a negative-DUT test |
| 1KB burst boundary rule | Covered at exact boundary | `ahb_boundary_test`; broader negative assertion coverage remains pending |
| `HSIZE` up to configured data width | Covered | Sequence size selection and monitor coverage |
| `HPROT` transport and policy | Covered | Transaction metadata plus `ahb_security_policy` callback; `ahb_security_policy_test` proves deny/allow behavior |
| AHB5 `HNONSEC` transport | Covered | Interface, driver, monitor, transaction metadata; BUSY test drives non-secure traffic |
| Configurable byte-lane endianness | Covered in reference memory | `ahb_big_endian_test`; little-endian remains the default |
| `HMASTLOCK/HMASTER` fabric semantics | Partial | Signals and transaction metadata are transported; no multi-master scheduler/arbitration |
| `HSEL` decode / multiple slaves | Partial | Single-slave example; configurable decode hooks are not a full interconnect |
| Reset during traffic | Covered in example | `ahb_reset_recovery_test` flushes master/slave state |
| Formal, toggle, and certification closure | Not claimed | Requires a project-specific DUT, constraints, and coverage plan |

## Remaining work, in priority order

1. Add a multi-master arbiter/interconnect example with `HMASTER`, lock, and
   `HSPLITx` routing.
2. Add a multi-slave interconnect example with explicit per-slave `HSEL` and
   address-map routing; the current cfg decode hook is intentionally single
   responder.
3. Add a negative-DUT harness that intentionally violates burst length and
   1KB rules and checks the strict SVA failures without treating them as normal
   regression failures.
4. Wire complete UVM transaction recording and simulator-independent replay.
