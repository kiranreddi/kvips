#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../../../.." && pwd)"
SIM_DIR="${ROOT}/kvips/axi4/examples/uvm_back2back/sim"
OUT_DIR="${ROOT}/kvips/axi4/examples/uvm_back2back/sim/out/fsdbreport"
mkdir -p "${OUT_DIR}"

usage() {
  cat <<'EOF'
Usage:
  run_fsdbreport_lsf.sh <fsdb_path> [--bt <time>] [--et <time>] [--cfg <cfgfile>] [--out <outfile>]

Notes:
  - Intended to run via LSF (tools live on grid nodes).
  - Loads verdi/2023.03_sp2 if module is available.
EOF
}

if [[ $# -lt 1 ]]; then
  usage
  exit 2
fi

FSDB="$1"
shift

BT=""
ET=""
CFG="${SIM_DIR}/fsdbreport_axi4.cfg"
OUT="${OUT_DIR}/kvips_axi4_b2b.txt"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --bt) BT="$2"; shift 2 ;;
    --et) ET="$2"; shift 2 ;;
    --cfg) CFG="$2"; shift 2 ;;
    --out) OUT="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "ERROR: unknown arg: $1"; usage; exit 2 ;;
  esac
done

if [[ -r /usr/share/Modules/init/bash ]]; then
  # shellcheck disable=SC1091
  source /usr/share/Modules/init/bash
fi
if command -v module >/dev/null 2>&1; then
  module load verdi/2023.03_sp2 >/dev/null 2>&1 || true
fi

if ! command -v fsdbreport >/dev/null 2>&1; then
  echo "ERROR: fsdbreport not found on PATH (need Verdi module)."
  echo "PATH=${PATH}"
  exit 127
fi

TMP_CFG="${OUT}.cfg"
{
  [[ -n "${BT}" ]] && echo "-bt ${BT}"
  [[ -n "${ET}" ]] && echo "-et ${ET}"
  cat "${CFG}"
} > "${TMP_CFG}"

fsdbreport "${FSDB}" -f "${TMP_CFG}" -o "${OUT}"

if [[ -f "${OUT}" ]]; then
  echo "WROTE: ${OUT}"
else
  echo "ERROR: fsdbreport did not create output: ${OUT}"
  exit 3
fi
