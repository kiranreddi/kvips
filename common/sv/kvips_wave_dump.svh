//------------------------------------------------------------------------------
// KVIPS Wave Dump Helpers
//------------------------------------------------------------------------------
// Usage (in your top initial block):
// - `include "kvips_wave_dump.svh"
// - `KVIPS_MAYBE_ENABLE_WAVES("waves")
//
// Controls:
// - Enable: +KVIPS_WAVES
// - FSDB requires compile-time `FSDB` define and the appropriate FSDB PLI
//   setup for your simulator (commonly via Verdi).
//------------------------------------------------------------------------------

`ifndef KVIPS_WAVE_DUMP_SVH
`define KVIPS_WAVE_DUMP_SVH

`define KVIPS_MAYBE_ENABLE_WAVES(BASENAME) \
  if ($test$plusargs("KVIPS_WAVES")) begin \
    `ifdef FSDB \
      $fsdbDumpfile({BASENAME,".fsdb"}); \
      $fsdbDumpvars(0); \
    `else \
      $dumpfile({BASENAME,".vcd"}); \
      $dumpvars(0); \
    `endif \
  end

`endif // KVIPS_WAVE_DUMP_SVH
