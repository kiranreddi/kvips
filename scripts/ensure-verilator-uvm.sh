#!/usr/bin/env bash
# Shared Verilator UVM bootstrap. Requires ROOT (repo top) to be set by caller.

: "${ROOT:?ROOT must be set to the repository root}"

UVM_TARBALL_URL="${UVM_TARBALL_URL:-https://www.accellera.org/images/downloads/standards/uvm/Accellera-1800.2-2017-1.0.tar.gz}"
UVM_BASE="${ROOT}/third_party/uvm"
UVM_SRC_DEFAULT="${UVM_BASE}/1800.2-2017-1.0/src"

VERILATOR_UVM_COMMIT_FILE="${ROOT}/.github/verilator-uvm-commit"
VERILATOR_UVM_COMMIT="${VERILATOR_UVM_COMMIT:-$(tr -d '[:space:]' < "${VERILATOR_UVM_COMMIT_FILE}")}"
VERILATOR_UVM_BASE="${ROOT}/third_party/uvm_verilator"
VERILATOR_UVM_DIR="uvm-master"
VERILATOR_UVM_SRC_DEFAULT="${VERILATOR_UVM_BASE}/${VERILATOR_UVM_DIR}/src"
VERILATOR_UVM_URL="${VERILATOR_UVM_URL:-https://github.com/verilator/uvm/archive/${VERILATOR_UVM_COMMIT}.tar.gz}"
VERILATOR_UVM_TARBALL="${VERILATOR_UVM_BASE}/uvm-${VERILATOR_UVM_COMMIT}.tar.gz"

apply_verilator_uvm_patch() {
  local seq_patch_file="${ROOT}/common/uvm/verilator_uvm.patch"
  local relnotes_patch_file="${ROOT}/common/uvm/verilator_uvm_relnotes.patch"
  local seq_target="${VERILATOR_UVM_BASE}/${VERILATOR_UVM_DIR}/src/tlm1/uvm_sqr_connections.svh"
  local root_target="${VERILATOR_UVM_BASE}/${VERILATOR_UVM_DIR}/src/base/uvm_root.svh"
  if [[ -f "${seq_patch_file}" && -f "${seq_target}" ]] && ! grep -q "local IMP m_imp;" "${seq_target}"; then
    (cd "${VERILATOR_UVM_BASE}" && patch -s -p1 -N < "${seq_patch_file}")
  fi
  if [[ -f "${relnotes_patch_file}" && -f "${root_target}" ]] && ! grep -q '\$test\$plusargs("UVM_NO_RELNOTES")' "${root_target}"; then
    (cd "${VERILATOR_UVM_BASE}" && patch -s -p1 -N < "${relnotes_patch_file}")
  fi
}

normalize_verilator_uvm_tree() {
  local extracted
  extracted="$(tar -tzf "${VERILATOR_UVM_TARBALL}" | head -1 | cut -d/ -f1)"
  if [[ -n "${extracted}" && "${extracted}" != "${VERILATOR_UVM_DIR}" ]]; then
    rm -rf "${VERILATOR_UVM_BASE}/${VERILATOR_UVM_DIR}"
    mv "${VERILATOR_UVM_BASE}/${extracted}" "${VERILATOR_UVM_BASE}/${VERILATOR_UVM_DIR}"
  fi
}

ensure_verilator_uvm() {
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
    if [[ ! -f "${VERILATOR_UVM_TARBALL}" ]]; then
      echo "Downloading Verilator UVM (${VERILATOR_UVM_COMMIT}) from ${VERILATOR_UVM_URL}" >&2
      curl -L -o "${VERILATOR_UVM_TARBALL}" "${VERILATOR_UVM_URL}"
    fi
    echo "Extracting Verilator UVM into ${VERILATOR_UVM_BASE}" >&2
    tar -xzf "${VERILATOR_UVM_TARBALL}" -C "${VERILATOR_UVM_BASE}"
    normalize_verilator_uvm_tree
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
  tar -xzf "${tarball}" -C "${UVM_BASE}"
  export UVM_HOME="${UVM_SRC_DEFAULT}"
}
