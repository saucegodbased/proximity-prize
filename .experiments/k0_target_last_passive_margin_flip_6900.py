#!/usr/bin/env python3
"""Exact target k0 source-margin ladder in the final passive layers.

This uses the literal integer transcriptions of the accepted
``SecondJetRelaxedGlobalCounts.coefficientCount`` and
``SecondJetRelaxedCounts.rankBound`` formulas.  It performs no field
computation and materializes no source matrix.
"""

from __future__ import annotations

import hashlib
import json
import sys

sys.path.insert(0, ".experiments")
import higher6810_secondjet_retarget_exact as Target  # noqa: E402


N = 262_144
G = 180_413
M = 47
B = 16
S = 8
U = 64


def row(passive_cap: int) -> dict[str, int]:
    columns = Target.coefficient_count(G, M, passive_cap, B, S, U, 0, 1)
    local_rank = Target.relaxed_rank_bound(M, passive_cap, B, S, U)
    return {
        "passive_cap": passive_cap,
        "source_columns": columns,
        "one_node_rank_bound": local_rank,
        "all_node_rank_budget": N * local_rank,
        "source_margin": columns - N * local_rank,
    }


def main() -> None:
    rows = tuple(row(cap) for cap in range(3748, 3758))
    assert tuple(item["source_margin"] for item in rows) == (
        -205_428_831,
        -182_339_952,
        -159_251_073,
        -136_162_194,
        -113_073_315,
        -89_984_436,
        -66_895_557,
        -43_806_678,
        -20_717_799,
        2_371_080,
    )
    assert all(item["source_margin"] < 0 for item in rows[:-1])
    assert rows[-1]["source_margin"] > 0

    before = rows[-2]
    after = rows[-1]
    last_layer_columns = after["source_columns"] - before["source_columns"]
    last_layer_local_rank = (
        after["one_node_rank_bound"] - before["one_node_rank_bound"]
    )
    last_layer_all_node_rank = N * last_layer_local_rank
    last_layer_net_margin = last_layer_columns - last_layer_all_node_rank
    assert (last_layer_columns, last_layer_local_rank,
            last_layer_all_node_rank, last_layer_net_margin) == (
        17_434_693_359,
        66_420,
        17_411_604_480,
        23_088_879,
    )
    assert before == {
        "passive_cap": 3756,
        "source_columns": 65_044_354_424_601,
        "one_node_rank_bound": 248_124_600,
        "all_node_rank_budget": 65_044_375_142_400,
        "source_margin": -20_717_799,
    }
    assert after == {
        "passive_cap": 3757,
        "source_columns": 65_061_789_117_960,
        "one_node_rank_bound": 248_191_020,
        "all_node_rank_budget": 65_061_786_746_880,
        "source_margin": 2_371_080,
    }

    payload = {
        "scope": "lower-6900 k0 final passive-cap margin ladder",
        "parameters_n_g_m_B_s_U_k_n0": (N, G, M, B, S, U, 0, 1),
        "rows": rows,
        "last_layer": {
            "new_source_columns": last_layer_columns,
            "new_one_node_rank_bound": last_layer_local_rank,
            "new_all_node_rank_budget": last_layer_all_node_rank,
            "net_margin_improvement": last_layer_net_margin,
        },
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
