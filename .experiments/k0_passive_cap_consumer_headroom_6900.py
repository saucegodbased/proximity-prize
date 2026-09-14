#!/usr/bin/env python3
"""Exact arithmetic for buying passive-cap headroom in the k0 m47 source.

This reuses the literal accepted source/rank formulas and the exact-stratum
52-chart consumer polynomial.  It proves no boundary rank statement; its
purpose is to determine whether L=3757 is a hard protocol ceiling or merely
the first source-positive cap.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import resource
import sys
import time

sys.path.insert(0, ".experiments")
from higher6810_secondjet_retarget_exact import (  # noqa: E402
    coefficient_count,
    relaxed_rank_bound,
)


N = 262_144
G = 180_413
M = 47
B = 16
U = 64
K = 0
N0 = 1
STRATA = N - G + 1
ALLOWANCE = 254_684_620_614_660_120


def chart_cost(passive_cap: int) -> int:
    return 588 * U**4 + 1560 * U**3 * passive_cap


def source_receipt(curvature_cap: int, passive_cap: int) -> dict[str, int]:
    columns = coefficient_count(
        G, M, passive_cap, B, curvature_cap, U, K, N0)
    local_rank = relaxed_rank_bound(M, passive_cap, B, curvature_cap, U)
    return {
        "curvature_cap": curvature_cap,
        "passive_cap": passive_cap,
        "columns": columns,
        "one_node_rank_bound": local_rank,
        "all_node_rank_bound": N * local_rank,
        "source_margin": columns - N * local_rank,
        "one_stratum_chart_cost": chart_cost(passive_cap),
        "all_strata_chart_cost": STRATA * chart_cost(passive_cap),
        "consumer_slack": ALLOWANCE - STRATA * chart_cost(passive_cap),
    }


def main() -> None:
    started = time.monotonic()
    per_cap_consumer_increment = STRATA * 1560 * U**3
    maximum_passive_cap = (
        ALLOWANCE - 1 - STRATA * 588 * U**4
    ) // per_cap_consumer_increment
    assert maximum_passive_cap == 7595
    assert STRATA * chart_cost(maximum_passive_cap) < ALLOWANCE
    assert STRATA * chart_cost(maximum_passive_cap + 1) >= ALLOWANCE

    receipts = (
        source_receipt(8, 3756),
        source_receipt(8, 3757),
        source_receipt(8, 3758),
        source_receipt(8, maximum_passive_cap),
        source_receipt(7, 3788),
        source_receipt(7, maximum_passive_cap),
        source_receipt(6, 5107),
        source_receipt(6, maximum_passive_cap),
    )
    expected_margins = (
        -20_717_799,
        2_371_080,
        25_459_959,
        88_617_488_682,
        479_478,
        86_148_077_430,
        12_113_822,
        40_160_156_246,
    )
    assert tuple(row["source_margin"] for row in receipts) == expected_margins

    payload = {
        "scope": (
            "exact k0 m47 source/rank and exact-stratum chart-consumer "
            "arithmetic; no normal-rank or caller theorem"
        ),
        "target_N_g_m_B_U_sRange": (N, G, M, B, U, (6, 8)),
        "strata_and_allowance": (STRATA, ALLOWANCE),
        "consumer_increment_per_added_passive_layer":
            per_cap_consumer_increment,
        "strict_maximum_passive_cap_under_this_consumer":
            maximum_passive_cap,
        "extra_layers_beyond_3757": maximum_passive_cap - 3757,
        "receipts": receipts,
        "interpretation": (
            "L=3757 is the first source-positive s=8 cap, not the maximum "
            "cap allowed by the exact-stratum chart ledger. Extra passive "
            "layers are arithmetically affordable, but a source/caller "
            "audit and a uniform relative-separation theorem are still "
            "required before retargeting production."
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    payload["runtime"] = {
        "seconds": round(time.monotonic() - started, 6),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
