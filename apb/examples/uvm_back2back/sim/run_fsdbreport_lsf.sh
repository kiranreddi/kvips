#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "${HERE}/../../../../.." && pwd)"

FSDB="${1:-}"
shift || true

if [[ -z "${FSDB}" ]]; then
  echo "ERROR: FSDB path required"
  exit 2
fi
if [[ ! -f "${FSDB}" ]]; then
  echo "ERROR: FSDB not found: ${FSDB}"
  exit 2
fi

if [[ -r /usr/share/Modules/init/bash ]]; then
  # shellcheck disable=SC1091
  source /usr/share/Modules/init/bash
fi
if command -v module >/dev/null 2>&1; then
  module load verdi/2023.03_sp2 >/dev/null 2>&1 || true
fi
if ! command -v fsdbreport >/dev/null 2>&1; then
  echo "ERROR: fsdbreport not found on PATH (need Verdi)."
  exit 127
fi

CFG="${HERE}/fsdbreport_apb.cfg"
if [[ ! -f "${CFG}" ]]; then
  echo "ERROR: missing cfg: ${CFG}"
  exit 2
fi

TMP_CFG="$(mktemp /tmp/kvips_apb_fsdbreport.XXXXXX)"
trap 'rm -f "${TMP_CFG}"' EXIT
cp "${CFG}" "${TMP_CFG}"

OUT_DIR="$(cd "$(dirname "${FSDB}")" && pwd)"
OUT_TXT="${OUT_DIR}/fsdbreport_$(date +%Y%m%d_%H%M%S).txt"

echo "INFO: fsdbreport ${FSDB} -> ${OUT_TXT}"
fsdbreport "${FSDB}" -f "${TMP_CFG}" -o "${OUT_TXT}" "$@"
echo "DONE: ${OUT_TXT}"

