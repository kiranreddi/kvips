#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../../.." && pwd)"
TESTS_FILE="${ROOT}/ahb/examples/uvm_back2back/sim/tests_questa.list"
SEED_BASE="${SEED_BASE:-1001}"

if ! command -v vcs >/dev/null 2>&1; then
  source /usr/share/Modules/init/bash
  module load vcs/2025.06_1
fi

run_log_has_issue() {
  local log="$1"
  grep -Eq 'UVM_ERROR[[:space:]]*:[[:space:]]*[1-9]|UVM_FATAL[[:space:]]*:[[:space:]]*[1-9]|Errors: [1-9]' "${log}"
}

while IFS= read -r test_name || [[ -n "${test_name}" ]]; do
  [[ -z "${test_name}" || "${test_name}" == \#* ]] && continue
  plusargs="${PLUSARGS:-}"
  case "${test_name}" in
    ahb_full_retry_test|ahb_full_split_test)
      plusargs="${plusargs} +AHB_MODE=AHB_FULL"
      ;;
  esac
  echo "=== ${test_name} (VCS) ==="
  make -s -C "${ROOT}/ahb/examples" vcs TEST="${test_name}" \
    SEED="${SEED_BASE}" UVM_VERBOSITY="${UVM_VERBOSITY:-UVM_LOW}" \
    PLUSARGS="${plusargs}"
  if run_log_has_issue "${ROOT}/ahb/examples/uvm_back2back/sim/out/vcs/run.log"; then
    echo "FAIL: ${test_name} (VCS reported a nonzero UVM/simulator error count)" >&2
    exit 1
  fi
done < "${TESTS_FILE}"
