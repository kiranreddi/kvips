#ifndef KVIPS_COCOTB_DPI_H
#define KVIPS_COCOTB_DPI_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define KVIPS_DPI_RING_SIZE 1024

typedef struct {
  uint8_t  proto;
  uint8_t  write;
  uint8_t  pad0;
  uint8_t  pad1;
  uint32_t resp;
  uint32_t strb;
  uint32_t len;
  uint32_t id;
  uint64_t addr;
  uint64_t data;
} kvips_dpi_mon_event_t;

typedef struct {
  uint32_t status;
  uint32_t pad;
  uint64_t d0;
  uint64_t d1;
  uint64_t d2;
  uint64_t d3;
} kvips_dpi_rsp_t;

/* Called from SystemVerilog (import "DPI-C") when a monitor txn completes. */
void kvips_dpi_mon_push(
  int proto,
  int write,
  long long addr,
  long long data,
  int resp,
  int strb,
  int len,
  int id
);

/* Called from SystemVerilog when a bridge command completes. */
void kvips_dpi_rsp_push(
  int status,
  long long d0,
  long long d1,
  long long d2,
  long long d3
);

/* Called from SystemVerilog for bridge lifecycle breadcrumbs. */
void kvips_dpi_log(const char* msg);

/* Python/ctypes accessors (same process as the Verilator+cocotb sim). */
int kvips_dpi_mon_pop(kvips_dpi_mon_event_t* out);
int kvips_dpi_mon_pending(void);
uint64_t kvips_dpi_mon_total(void);

int kvips_dpi_rsp_pop(kvips_dpi_rsp_t* out);
int kvips_dpi_rsp_pending(void);

void kvips_dpi_reset(void);

#ifdef __cplusplus
}
#endif

#endif /* KVIPS_COCOTB_DPI_H */
