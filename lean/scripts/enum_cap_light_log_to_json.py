#!/usr/bin/env python3
"""
enum_cap_light_log_to_json.py — Extract per-cell records from the
verbose log of `enum_cap_light.py` and emit a structured JSON
certificate.

Used when the main enumeration run is interrupted before its
in-process JSON dump: we recover the per-cell data already written
to the log and ship a partial-but-honest certificate.

Two log line formats:

* completed cell:
    `  K=A w=B sizes=[k1, ..., kK] nfree=N  masks=...  accepted=...
       balanced=...  T.TTs`
* skipped cell:
    `  K=A w=B sizes=[k1, ..., kK] masks=... SKIPPED`

The script accepts a path to the log and a destination JSON path
and writes a certificate matching the schema of `enum_cap_light.py`.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
import time


COMPLETED_RE = re.compile(
    r"^\s*K=(?P<K>\d+) w=(?P<w>\d+) sizes=(?P<sizes>\[[^\]]*\])\s+"
    r"nfree=\s*(?P<nfree>\d+)\s+masks=\s*(?P<masks>\d+)\s+"
    r"accepted=\s*(?P<accepted>\d+)\s+balanced=\s*(?P<balanced>\d+)\s+"
    r"(?P<elapsed>[\d.]+)s\s*(?:\*COUNTER\*)?\s*$"
)

SKIPPED_RE = re.compile(
    r"^\s*K=(?P<K>\d+) w=(?P<w>\d+) sizes=(?P<sizes>\[[^\]]*\])\s+"
    r"masks=(?P<masks>\d+)\s+SKIPPED\s*$"
)


def parse_log(log_path: str) -> list[dict]:
    out: list[dict] = []
    with open(log_path) as f:
        for line in f:
            m = COMPLETED_RE.match(line)
            if m:
                sizes = json.loads(m.group("sizes"))
                K = int(m.group("K"))
                w = int(m.group("w"))
                entry = {
                    "K": K,
                    "w": w,
                    "band_sizes": sizes,
                    "n": sum(sizes),
                    "nfree": int(m.group("nfree")),
                    "masks_total": int(m.group("masks")),
                    "accepted": int(m.group("accepted")),
                    "balanced": int(m.group("balanced")),
                    "counterexamples": [],
                    "elapsed_s": float(m.group("elapsed")),
                }
                # The log does not preserve full counterexample
                # detail; the verbose printer flags *COUNTER* on
                # cells where balanced < accepted. Re-derive:
                if entry["accepted"] != entry["balanced"]:
                    entry["counterexamples"] = [{
                        "_recovered_from_log": True,
                        "delta": entry["accepted"] - entry["balanced"],
                    }]
                out.append(entry)
                continue
            m = SKIPPED_RE.match(line)
            if m:
                sizes = json.loads(m.group("sizes"))
                K = int(m.group("K"))
                w = int(m.group("w"))
                masks_total = int(m.group("masks"))
                out.append({
                    "K": K,
                    "w": w,
                    "band_sizes": sizes,
                    "n": sum(sizes),
                    "masks_total": masks_total,
                    "skipped": True,
                    "reason": "masks exceeds max_masks (recovered from log)",
                })
                continue
    return out


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--log", required=True,
                   help="Path to enum_cap_light.py verbose log.")
    p.add_argument("--output", required=True,
                   help="Path to write JSON certificate.")
    p.add_argument("--max-masks", type=int, default=1 << 25,
                   help="Original --max-masks value (for the cert "
                        "metadata only).")
    p.add_argument("--note", type=str, default="",
                   help="Free-text note appended to cert metadata.")
    args = p.parse_args(argv)

    per_cell = parse_log(args.log)
    accepted_total = sum(c.get("accepted", 0) for c in per_cell)
    balanced_total = sum(c.get("balanced", 0) for c in per_cell)
    counterexamples = sum(1 for c in per_cell if c.get("counterexamples"))
    cells_skipped = sum(1 for c in per_cell if c.get("skipped"))

    cert = {
        "description": "mg-be48 — Case3Witness cap-LIGHT enumeration certificate (recovered from log)",
        "script": "enum_cap_light.py (per-cell) + enum_cap_light_log_to_json.py (aggregation)",
        "scope": (
            "All (β, LB) where β is a width-≤3 non-chain finite poset and "
            "LB : LayeredDecomposition β satisfies caps 2-5 + L1a (band "
            "size ≤ 3) of Step8.Case3Witness, with cap 1 (Injective band) "
            "DROPPED. Bands may be non-singleton. K ≤ 2w+2 ⇒ K ≤ 10 for "
            "w ≤ 4; |β| ≤ 3K ≤ 30."
        ),
        "filters": {
            "require_width3": True,
            "require_non_chain": True,
            "require_closure_canonical": True,
            "max_band_size": 3,
            "max_masks": args.max_masks,
        },
        "note": args.note,
        "per_cell": per_cell,
        "summary": {
            "cells_total": len(per_cell),
            "cells_skipped": cells_skipped,
            "accepted_total": accepted_total,
            "balanced_total": balanced_total,
            "counterexample_cells": counterexamples,
        },
        "status": (
            "fail" if counterexamples > 0
            else ("amber" if cells_skipped > 0 else "pass")
        ),
        "recovered_from_log": True,
        "log_path": args.log,
    }
    os.makedirs(os.path.dirname(args.output) or ".", exist_ok=True)
    with open(args.output, "w") as f:
        json.dump(cert, f, indent=2, default=str)
    print(f"Wrote {args.output}")
    print(
        f"Cells: {len(per_cell)}  skipped: {cells_skipped}  "
        f"accepted: {accepted_total}  balanced: {balanced_total}  "
        f"counterexample_cells: {counterexamples}  status: {cert['status']}"
    )
    return 0 if counterexamples == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
