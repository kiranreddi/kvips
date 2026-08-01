//------------------------------------------------------------------------------
// KVIPS cocotb DPI — monitor ring buffer, response mailbox, logging
// Linked into the Verilator/cocotb simulation; Python reads via ctypes.
//------------------------------------------------------------------------------
#include "kvips_cocotb_dpi.h"

#include <stdio.h>
#include <string.h>

static kvips_dpi_mon_event_t g_ring[KVIPS_DPI_RING_SIZE];
static volatile unsigned g_head = 0;
static volatile unsigned g_tail = 0;
static volatile uint64_t g_total = 0;
static volatile int g_overflow = 0;

static kvips_dpi_rsp_t g_rsp_ring[KVIPS_DPI_RING_SIZE];
static volatile unsigned g_rsp_head = 0;
static volatile unsigned g_rsp_tail = 0;

void kvips_dpi_reset(void) {
  g_head = 0;
  g_tail = 0;
  g_total = 0;
  g_overflow = 0;
  memset((void*)g_ring, 0, sizeof(g_ring));
  g_rsp_head = 0;
  g_rsp_tail = 0;
  memset((void*)g_rsp_ring, 0, sizeof(g_rsp_ring));
}

void kvips_dpi_log(const char* msg) {
  if (msg == NULL) {
    return;
  }
  fprintf(stderr, "[KVIPS-DPI] %s\n", msg);
  fflush(stderr);
}

void kvips_dpi_mon_push(
  int proto,
  int write,
  long long addr,
  long long data,
  int resp,
  int strb,
  int len,
  int id
) {
  unsigned next = (g_head + 1u) % KVIPS_DPI_RING_SIZE;
  if (next == g_tail) {
    g_overflow = 1;
    return;
  }
  g_ring[g_head].proto = (uint8_t)proto;
  g_ring[g_head].write = (uint8_t)(write ? 1 : 0);
  g_ring[g_head].resp = (uint32_t)resp;
  g_ring[g_head].strb = (uint32_t)strb;
  g_ring[g_head].len = (uint32_t)len;
  g_ring[g_head].id = (uint32_t)id;
  g_ring[g_head].addr = (uint64_t)addr;
  g_ring[g_head].data = (uint64_t)data;
  g_head = next;
  g_total++;
}

int kvips_dpi_mon_pending(void) {
  return (g_head != g_tail) ? 1 : 0;
}

int kvips_dpi_mon_pop(kvips_dpi_mon_event_t* out) {
  if (out == NULL) {
    return 0;
  }
  if (g_head == g_tail) {
    return 0;
  }
  *out = g_ring[g_tail];
  g_tail = (g_tail + 1u) % KVIPS_DPI_RING_SIZE;
  return 1;
}

uint64_t kvips_dpi_mon_total(void) {
  return g_total;
}

void kvips_dpi_rsp_push(
  int status,
  long long d0,
  long long d1,
  long long d2,
  long long d3
) {
  unsigned next = (g_rsp_head + 1u) % KVIPS_DPI_RING_SIZE;
  if (next == g_rsp_tail) {
    /* Drop oldest to keep latest response available. */
    g_rsp_tail = (g_rsp_tail + 1u) % KVIPS_DPI_RING_SIZE;
  }
  g_rsp_ring[g_rsp_head].status = (uint32_t)status;
  g_rsp_ring[g_rsp_head].pad = 0;
  g_rsp_ring[g_rsp_head].d0 = (uint64_t)d0;
  g_rsp_ring[g_rsp_head].d1 = (uint64_t)d1;
  g_rsp_ring[g_rsp_head].d2 = (uint64_t)d2;
  g_rsp_ring[g_rsp_head].d3 = (uint64_t)d3;
  g_rsp_head = next;
}

int kvips_dpi_rsp_pending(void) {
  return (g_rsp_head != g_rsp_tail) ? 1 : 0;
}

int kvips_dpi_rsp_pop(kvips_dpi_rsp_t* out) {
  if (out == NULL) {
    return 0;
  }
  if (g_rsp_head == g_rsp_tail) {
    return 0;
  }
  *out = g_rsp_ring[g_rsp_tail];
  g_rsp_tail = (g_rsp_tail + 1u) % KVIPS_DPI_RING_SIZE;
  return 1;
}
