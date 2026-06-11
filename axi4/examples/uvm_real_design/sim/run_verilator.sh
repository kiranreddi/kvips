#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && git rev-parse --show-toplevel)"
OUT="${ROOT}/axi4/examples/uvm_real_design/sim/out/verilator"
mkdir -p "${OUT}"

ORIG_FILELIST="${ROOT}/axi4/examples/uvm_real_design/sim/filelist.f"
ABS_FILELIST="${OUT}/filelist.abs.f"

# shellcheck disable=SC1091
source "${ROOT}/scripts/ensure-verilator-uvm.sh"

make_abs_filelist() {
  local in="$1"
  local out="$2"
  : >"${out}"
  while IFS= read -r line || [[ -n "${line}" ]]; do
    case "${line}" in
      ""|\#*)
        printf '%s\n' "${line}" >>"${out}"
        ;;
      +incdir+*)
        p="${line#'+incdir+'}"
        if [[ "${p}" = /* ]]; then
          printf '%s\n' "${line}" >>"${out}"
        else
          printf '+incdir+%s\n' "${ROOT}/${p}" >>"${out}"
        fi
        ;;
      +*|-*)
        printf '%s\n' "${line}" >>"${out}"
        ;;
      *)
        if [[ "${line}" = /* ]]; then
          printf '%s\n' "${line}" >>"${out}"
        else
          printf '%s\n' "${ROOT}/${line}" >>"${out}"
        fi
        ;;
    esac
  done <"${in}"
}

if [[ ! -f "${ORIG_FILELIST}" ]]; then
  echo "ERROR: missing filelist: ${ORIG_FILELIST}"
  exit 2
fi

ensure_verilator_uvm
if [[ ! -d "${UVM_HOME}" ]]; then
  echo "ERROR: UVM_HOME not found: ${UVM_HOME}" >&2
  exit 2
fi

make_abs_filelist "${ORIG_FILELIST}" "${ABS_FILELIST}"

VERILATOR_BIN="${VERILATOR_BIN:-verilator}"
if ! command -v "${VERILATOR_BIN}" >/dev/null 2>&1; then
  echo "ERROR: '${VERILATOR_BIN}' not found on PATH." >&2
  exit 127
fi

cd "${OUT}"

REUSE_BUILD="${VERILATOR_REUSE_BUILD:-0}"
if [[ "${REUSE_BUILD}" != "1" ]]; then
  rm -rf obj_dir *.log 2>/dev/null || true
fi

JOBS="${VERILATOR_JOBS:-1}"
STACK_CFLAGS="-Wno-deprecated-declarations"
if [[ "$(uname -s)" == "Darwin" ]]; then
  STACK_CHECK_HEADER="${OUT}/verilator_no_stack_check.h"
  cat >"${STACK_CHECK_HEADER}" <<'EOF'
#include <sys/resource.h>
#define getrlimit(resource, rlim) (-1)
EOF
  STACK_CFLAGS="${STACK_CFLAGS} -include ${STACK_CHECK_HEADER}"
fi

BIN="${OUT}/obj_dir/Vtop"
if [[ "${REUSE_BUILD}" != "1" || ! -x "${BIN}" ]]; then
  ${VERILATOR_BIN} -sv --language 1800-2017 -Wno-fatal -Wno-PKGNODECL -Wno-UNDRIVEN -Wno-TIMESCALEMOD -Wno-SYNCASYNCNET -Wno-MISINDENT -Wno-WIDTHTRUNC -Wno-WIDTHEXPAND -Wno-CASTCONST -Wno-REALCVT -Wno-CONSTRAINTIGN -Wno-SELRANGE --bbox-unsup --no-unlimited-stack --timing --binary -j "${JOBS}" \
    -CFLAGS "${STACK_CFLAGS}" \
    --top-module top \
    +incdir+"${UVM_HOME}" \
    +define+UVM_NO_DPI \
    +define+UVM_USE_PROCESS_CONTAINER \
    "${UVM_HOME}/uvm_pkg.sv" \
    -f "${ABS_FILELIST}" \
    -o Vtop 2>&1 | tee "${OUT}/compile.log"
fi

if [[ ! -x "${BIN}" ]]; then
  echo "ERROR: Vtop not produced; see ${OUT}/compile.log" >&2
  exit 2
fi

EXTRA_ARGS=("$@")
HAVE_TESTNAME=0
HAVE_VERBOSITY=0
HAVE_NO_RELNOTES=0
for a in "${EXTRA_ARGS[@]}"; do
  [[ "$a" == +UVM_TESTNAME=* ]] && HAVE_TESTNAME=1
  [[ "$a" == +UVM_VERBOSITY=* ]] && HAVE_VERBOSITY=1
  [[ "$a" == +UVM_NO_RELNOTES ]] && HAVE_NO_RELNOTES=1
done
[[ "$HAVE_TESTNAME" -eq 0 ]] && EXTRA_ARGS+=("+UVM_TESTNAME=axi4_dut_smoke_test")
[[ "$HAVE_VERBOSITY" -eq 0 ]] && EXTRA_ARGS+=("+UVM_VERBOSITY=UVM_LOW")
[[ "$HAVE_NO_RELNOTES" -eq 0 ]] && EXTRA_ARGS+=("+UVM_NO_RELNOTES")

"${BIN}" "${EXTRA_ARGS[@]}" | tee "${OUT}/run.log"
