#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && git rev-parse --show-toplevel)"
OUT="${ROOT}/ahb/examples/uvm_back2back/sim/out/verilator"
mkdir -p "${OUT}"

ORIG_FILELIST="${ROOT}/ahb/examples/uvm_back2back/sim/filelist.f"
ABS_FILELIST="${OUT}/filelist.abs.f"

UVM_TARBALL_URL="https://www.accellera.org/images/downloads/standards/uvm/Accellera-1800.2-2017-1.0.tar.gz"
UVM_BASE="${ROOT}/third_party/uvm"
UVM_SRC_DEFAULT="${UVM_BASE}/1800.2-2017-1.0/src"

VERILATOR_UVM_URL="${VERILATOR_UVM_URL:-https://github.com/verilator/uvm/archive/refs/heads/master.tar.gz}"
VERILATOR_UVM_BASE="${ROOT}/third_party/uvm_verilator"
VERILATOR_UVM_SRC_DEFAULT="${VERILATOR_UVM_BASE}/uvm-master/src"

apply_verilator_uvm_patch() {
  local patch_file="${ROOT}/common/uvm/verilator_uvm.patch"
  if [[ -f "${patch_file}" ]]; then
    (cd "${VERILATOR_UVM_BASE}" && patch -p1 --forward < "${patch_file}")
  fi
}

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

ensure_uvm() {
  if [[ -n "${UVM_HOME:-}" ]]; then
    return 0
  fi
  if [[ "${UVM_USE_VERILATOR:-1}" == "1" ]]; then
    if [[ -d "${VERILATOR_UVM_SRC_DEFAULT}" ]]; then
      export UVM_HOME="${VERILATOR_UVM_SRC_DEFAULT}"
      apply_verilator_uvm_patch
      return 0
    fi
    mkdir -p "${VERILATOR_UVM_BASE}"
    local vtarball="${VERILATOR_UVM_BASE}/uvm-master.tar.gz"
    if [[ ! -f "${vtarball}" ]]; then
      echo "Downloading Verilator UVM from ${VERILATOR_UVM_URL}" >&2
      curl -L -o "${vtarball}" "${VERILATOR_UVM_URL}"
    fi
    echo "Extracting Verilator UVM into ${VERILATOR_UVM_BASE}" >&2
    tar -xvzf "${vtarball}" -C "${VERILATOR_UVM_BASE}"
    export UVM_HOME="${VERILATOR_UVM_SRC_DEFAULT}"
    apply_verilator_uvm_patch
    return 0
  fi
  if [[ -d "${UVM_SRC_DEFAULT}" ]]; then
    export UVM_HOME="${UVM_SRC_DEFAULT}"
    return 0
  fi

  mkdir -p "${UVM_BASE}"
  local tarball="${UVM_BASE}/Accellera-1800.2-2017-1.0.tar.gz"
  if [[ ! -f "${tarball}" ]]; then
    echo "Downloading UVM from ${UVM_TARBALL_URL}" >&2
    curl -L -o "${tarball}" "${UVM_TARBALL_URL}"
  fi
  echo "Extracting UVM into ${UVM_BASE}" >&2
  tar -xvzf "${tarball}" -C "${UVM_BASE}"
  export UVM_HOME="${UVM_SRC_DEFAULT}"
}

if [[ ! -f "${ORIG_FILELIST}" ]]; then
  echo "ERROR: missing filelist: ${ORIG_FILELIST}"
  exit 2
fi

ensure_uvm
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

BIN="${OUT}/obj_dir/Vtop"
if [[ "${REUSE_BUILD}" != "1" || ! -x "${BIN}" ]]; then
  ${VERILATOR_BIN} -sv --language 1800-2017 -Wno-fatal -Wno-PKGNODECL -Wno-UNDRIVEN -Wno-TIMESCALEMOD -Wno-SYNCASYNCNET -Wno-MISINDENT -Wno-WIDTHTRUNC -Wno-WIDTHEXPAND -Wno-CASTCONST -Wno-REALCVT -Wno-CONSTRAINTIGN -Wno-SELRANGE --timing --binary -j "${JOBS}" \
    +define+UVM_USE_PROCESS_CONTAINER \
    -CFLAGS "-Wno-deprecated-declarations" \
    --top-module top \
    +incdir+"${UVM_HOME}" \
    +define+UVM_NO_DPI \
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
for a in "${EXTRA_ARGS[@]}"; do
  [[ "$a" == +UVM_TESTNAME=* ]] && HAVE_TESTNAME=1
  [[ "$a" == +UVM_VERBOSITY=* ]] && HAVE_VERBOSITY=1
done
[[ "$HAVE_TESTNAME" -eq 0 ]] && EXTRA_ARGS+=("+UVM_TESTNAME=ahb_smoke_test")
[[ "$HAVE_VERBOSITY" -eq 0 ]] && EXTRA_ARGS+=("+UVM_VERBOSITY=UVM_LOW")

"${BIN}" "${EXTRA_ARGS[@]}" | tee "${OUT}/run.log"
