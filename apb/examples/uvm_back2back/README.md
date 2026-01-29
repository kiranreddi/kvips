# APB (APB3/APB4) UVM Back-to-Back Example

This example instantiates the KVIPS APB VIP in a self-contained UVM testbench:

- APB **master agent** drives transactions
- APB **slave agent** responds with a simple memory model + configurable wait-states/error injection
- Monitor + scoreboard validate read data against prior writes

## Run

From `kvips/apb/examples`:

```bash
make -C kvips/apb/examples list-tests
make -C kvips/apb/examples vcs TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB4'
make -C kvips/apb/examples vcs TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB3'
```

LSF:

```bash
module load lsf
make -C kvips/apb/examples vcs USE_LSF=1 TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB4'
```

## Protocol mode switch

- APB3: `+APB_PROTOCOL=APB3` (PSTRB/PPROT ignored/forced by master)
- APB4: `+APB_PROTOCOL=APB4`

