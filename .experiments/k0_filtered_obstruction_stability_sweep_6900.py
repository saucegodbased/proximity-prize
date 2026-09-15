#!/usr/bin/env python3
"""Sweep when the complete passive-face connecting obstruction vanishes.

This is a small exact mechanism discriminator.  It deliberately omits the
row-packet tests from ``k0_eps0_filtered_obstruction_gate_6900.py`` and only
computes the three ranks defining

    rank(delta) = rank(full) - rank(old) - rank(top).

The question is whether the m6 L8 strictness event is isolated or the start
of a stable large-passive-cap chamber relevant to the target L/m ratio.
"""

from __future__ import annotations

from dataclasses import asdict, replace
import gc
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

sys.path.insert(0, ".experiments")
import k0_eps0_filtered_obstruction_gate_6900 as Gate  # noqa: E402
import k0_first_positive_passive_universal_falsifier_6900 as Old  # noqa: E402


CAP = 4_200_000_000
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
if soft < 0 or soft > CAP:
    resource.setrlimit(resource.RLIMIT_AS, (CAP, hard))


def analyze(profile, receipt, name):
    nxt = replace(profile, L=profile.L + 1)
    old = tuple(Old.K0.support(profile))
    old_set = set(old)
    face = tuple(q for q in Old.K0.support(nxt) if q not in old_set)
    assert all(sum(q[1:]) == nxt.L for q in face)
    old_columns = tuple(Gate.contact_column(nxt, receipt, q) for q in old)
    face_columns = tuple(Gate.contact_column(nxt, receipt, q) for q in face)
    Gate.flattened_raw_column.cache_clear()
    rows = tuple(sorted(set().union(
        *(set(column) for column in old_columns + face_columns)), key=repr))
    top_rows = tuple(row for row in rows if Gate.passive_degree(row) == nxt.L)
    lower_rows = tuple(row for row in rows if Gate.passive_degree(row) < nxt.L)
    rank_old = Gate.exact_rank(old_columns, lower_rows, name + " old")
    rank_top = Gate.exact_rank(face_columns, top_rows, name + " top")
    rank_full = Gate.exact_rank(old_columns + face_columns, rows, name + " full")
    obstruction = rank_full - rank_old - rank_top
    result = {
        "name": name,
        "old_profile": tuple(asdict(profile).values()),
        "columns_old_face": (len(old), len(face)),
        "rows_lower_top": (len(lower_rows), len(top_rows)),
        "ranks_old_top_full": (rank_old, rank_top, rank_full),
        "top_kernel": len(face) - rank_top,
        "obstruction_rank": obstruction,
        "all_top_kernel_lifts": obstruction == 0,
    }
    del old_columns, face_columns
    gc.collect()
    return result


def main():
    started = time.monotonic()
    specifications = (
        # The known RED-to-GREEN transition, continued by one cap.
        (Old.K0.Profile(6, 2, 4, 4, 2, 1, 6, 4, 0, 1), 101,
         "random", "mid", "minimal", "arbitrary", "alternating", 2),
        (Old.K0.Profile(6, 2, 4, 4, 2, 1, 6, 5, 0, 1), 101,
         "random", "mid", "minimal", "arbitrary", "alternating", 2),
        (Old.K0.Profile(6, 2, 4, 4, 2, 1, 6, 6, 0, 1), 101,
         "random", "mid", "minimal", "arbitrary", "alternating", 2),
        # The known GREEN chamber and its immediate predecessor/successor.
        (Old.K0.Profile(11, 5, 8, 6, 2, 1, 8, 7, 0, 1), 101,
         "random", "mid", "minimal", "arbitrary", "alternating", 2),
        (Old.K0.Profile(11, 5, 8, 6, 2, 1, 8, 8, 0, 1), 101,
         "random", "mid", "minimal", "arbitrary", "alternating", 2),
        (Old.K0.Profile(11, 5, 8, 6, 2, 1, 8, 9, 0, 1), 101,
         "random", "mid", "minimal", "arbitrary", "alternating", 2),
    )
    cases = []
    for profile, prime, agreement, candidate, tangent, off, errors, tag in specifications:
        receipt = Old.make_custom_receipt(
            profile, prime, 0, agreement, candidate, tangent, off, errors, tag)
        cases.append(analyze(
            profile, receipt, f"m{profile.m}_L{profile.L}_to_{profile.L + 1}"))
    payload = {
        "scope": "exact complete-face filtered obstruction stability sweep",
        "field": 101,
        "cases": cases,
        "scope_guard": (
            "Finite arbitrary-error-direction controls only.  Obstruction "
            "zero in these controls is not a target strictness theorem."
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    payload["runtime"] = {
        "seconds": round(time.monotonic() - started, 3),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "address_space_cap_bytes": CAP,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
