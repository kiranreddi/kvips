#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && git rev-parse --show-toplevel)"
if [[ -x /opt/verilator-5.048/bin/verilator ]]; then
  export PATH="/opt/verilator-5.048/bin:${PATH}"
fi
VENV="${ROOT}/.venv-cocotb"
if [[ ! -x "${VENV}/bin/python" ]]; then
  python3 -m venv "${VENV}"
  # shellcheck disable=SC1091
  source "${VENV}/bin/activate"
  python -m pip install --upgrade pip
  python -m pip install 'cocotb==1.9.2'
else
  # shellcheck disable=SC1091
  source "${VENV}/bin/activate"
fi
exec python3 "${ROOT}/scripts/run_cocotb_verilator.py" --protocol apb "$@"
