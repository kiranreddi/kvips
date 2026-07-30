#!/usr/bin/env python3
"""Validate and canonicalize portable AXI4 transaction replay CSV files.

The tool intentionally does not depend on a simulator. It is useful for
reviewing captured stimulus before translating it into a sequence or a
vendor-specific transaction database. A transaction is one row; write data
and strobes are pipe-separated beat vectors.
"""

import argparse
import csv
import json
import sys
from pathlib import Path
from typing import Dict, List


REQUIRED = {
    "is_write", "id", "addr", "beats", "size", "burst", "lock", "cache",
    "prot", "qos", "region", "data_hex", "strb_hex",
}
BURST_LIMITS = {"INCR": 256, "FIXED": 16, "WRAP": 16}
WRAP_BEATS = {2, 4, 8, 16}


def number(value: str, field: str, row: int) -> int:
    try:
        return int(value.strip(), 0)
    except ValueError as exc:
        raise ValueError(f"row {row}: {field} is not an integer: {value!r}") from exc


def vector(value: str, field: str, row: int) -> List[int]:
    if not value.strip():
        return []
    return [number(item, field, row) for item in value.replace(";", "|").split("|")]


def validate_row(raw: Dict[str, str], row: int) -> Dict[str, object]:
    is_write = number(raw["is_write"], "is_write", row)
    if is_write not in (0, 1):
        raise ValueError(f"row {row}: is_write must be 0 or 1")
    txn: Dict[str, object] = {
        "is_write": bool(is_write),
        "id": number(raw["id"], "id", row),
        "addr": number(raw["addr"], "addr", row),
        "beats": number(raw["beats"], "beats", row),
        "size": number(raw["size"], "size", row),
        "burst": raw["burst"].strip().upper(),
        "lock": number(raw["lock"], "lock", row),
        "cache": number(raw["cache"], "cache", row),
        "prot": number(raw["prot"], "prot", row),
        "qos": number(raw["qos"], "qos", row),
        "region": number(raw["region"], "region", row),
        "data": vector(raw["data_hex"], "data_hex", row),
        "strb": vector(raw["strb_hex"], "strb_hex", row),
    }
    beats = int(txn["beats"])
    size = int(txn["size"])
    addr = int(txn["addr"])
    burst = str(txn["burst"])
    if burst not in BURST_LIMITS:
        raise ValueError(f"row {row}: burst must be INCR, FIXED, or WRAP")
    if beats < 1 or beats > BURST_LIMITS[burst]:
        raise ValueError(f"row {row}: illegal {burst} beat count {beats}")
    if size < 0 or size > 6:
        raise ValueError(f"row {row}: size exponent must be in [0, 6]")
    transfer_bytes = 1 << size
    if burst == "WRAP" and beats not in WRAP_BEATS:
        raise ValueError(f"row {row}: WRAP beats must be 2, 4, 8, or 16")
    if burst == "WRAP" and addr % (beats * transfer_bytes):
        raise ValueError(f"row {row}: WRAP address is not aligned to the wrap span")
    if (addr & 0xFFF) + beats * transfer_bytes > 0x1000:
        raise ValueError(f"row {row}: transfer crosses a 4KB boundary")
    if int(txn["id"]) < 0:
        raise ValueError(f"row {row}: id must be non-negative")
    for field, limit in (("cache", 0xF), ("prot", 0x7), ("qos", 0xF), ("region", 0xF)):
        if not 0 <= int(txn[field]) <= limit:
            raise ValueError(f"row {row}: {field} is outside its AXI field width")
    if bool(txn["is_write"]):
        if len(txn["data"]) != beats:
            raise ValueError(f"row {row}: write data vector must contain {beats} beats")
        if len(txn["strb"]) != beats:
            raise ValueError(f"row {row}: write strobe vector must contain {beats} beats")
    elif txn["data"] or txn["strb"]:
        raise ValueError(f"row {row}: read rows must leave data_hex and strb_hex empty")
    return txn


def load(path: Path) -> List[Dict[str, object]]:
    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream)
        fields = set(reader.fieldnames or ())
        missing = sorted(REQUIRED - fields)
        if missing:
            raise ValueError(f"missing required CSV columns: {', '.join(missing)}")
        return [validate_row(row, index) for index, row in enumerate(reader, start=2)]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("csv", type=Path, help="transaction replay CSV")
    parser.add_argument("--json", action="store_true", help="emit canonical JSON")
    args = parser.parse_args()
    try:
        transactions = load(args.csv)
    except (OSError, ValueError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2
    writes = sum(bool(txn["is_write"]) for txn in transactions)
    reads = len(transactions) - writes
    beats = sum(int(txn["beats"]) for txn in transactions)
    if args.json:
        print(json.dumps(transactions, indent=2, sort_keys=True))
    else:
        print(f"AXI4 replay valid: transactions={len(transactions)} writes={writes} reads={reads} beats={beats}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
