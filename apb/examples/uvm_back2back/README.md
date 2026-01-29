# APB (APB3/APB4) UVM Back-to-Back Example

This example instantiates the KVIPS APB VIP in a self-contained UVM testbench:

- APB **master agent** drives transactions
- APB **slave agent** responds with a simple memory model + configurable wait-states/error injection
- Monitor + scoreboard validate read data against prior writes

## Run

From `kvips/apb/examples`:

```bash
make -C kvips/apb/examples list-tests
make -C kvips/apb/examples questa TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB4'
make -C kvips/apb/examples questa-waves TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB4'
make -C kvips/apb/examples vcs TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB4'
make -C kvips/apb/examples vcs TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB3'
make -C kvips/apb/examples xcelium TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB4'
```

LSF:

```bash
source /tools/lsf/conf/profile.lsf
make -C kvips/apb/examples questa  USE_LSF=1 TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB4'
make -C kvips/apb/examples vcs    USE_LSF=1 TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB4'
make -C kvips/apb/examples xcelium USE_LSF=1 TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB4'
```

## Waves

- Enable wave dumping: `+KVIPS_WAVES`
- Questa FSDB run: `make -C kvips/apb/examples questa-waves ...` (requires Verdi/Novas PLI)

## Protocol mode switch

- APB3: `+APB_PROTOCOL=APB3` (PSTRB/PPROT ignored/forced by master)
- APB4: `+APB_PROTOCOL=APB4`
