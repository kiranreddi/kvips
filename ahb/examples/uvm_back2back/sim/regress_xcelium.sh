#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../../.." && pwd)"
TESTS_FILE="${ROOT}/ahb/examples/uvm_back2back/sim/tests_questa.list"
SEED_BASE="${SEED_BASE:-1001}"

if ! command -v xrun >/dev/null 2>&1; then
  source /usr/share/Modules/init/bash
  module load xcelium/25.03.007
fi

while IFS= read -r test_name || [[ -n "${test_name}" ]]; do
  [[ -z "${test_name}" || "${test_name}" == \#* ]] && continue
  plusargs="${PLUSARGS:-}"
  case "${test_name}" in
    ahb_full_retry_test|ahb_full_split_test)
      plusargs="${plusargs} +AHB_MODE=AHB_FULL"
      ;;
  esac
  echo "=== ${test_name} (Xcelium) ==="
  make -s -C "${ROOT}/ahb/examples" xcelium TEST="${test_name}" \
    SEED="${SEED_BASE}" UVM_VERBOSITY="${UVM_VERBOSITY:-UVM_LOW}" \
    PLUSARGS="${plusargs}"
done < "${TESTS_FILE}"
