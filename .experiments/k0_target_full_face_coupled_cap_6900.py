#!/usr/bin/env python3
"""Exact target full-face dimension versus the coupled weighted rank cap.

The raw-1 associated face is too small for its bivariate Hermite cap.  This
script adds the derivative shapes honestly.  For every raw-S cap ``sCap`` it
counts:

* the global cap-L/cap-(L-1) face with all legal raw-R and Y shapes;
* the exact-degree face of the local relaxed source;
* the exact-degree part of the explicit independent weighted contact kernel;
* their difference, an honest coupled one-node associated rank cap.

The weighted vectors are homogeneous in passive degree (formalized in the
companion Lean file), so their face count may be subtracted before multiplying
the coupled cap by the number of nodes.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import resource
import sys
import time

sys.path.insert(0, ".experiments")
import higher6810_secondjet_retarget_exact as Target  # noqa: E402


N = 262_144
W = 131_071
G = 180_413
M = 47
B = 16
S = 8
U = 64
L = 3_757
D = M * G


def global_face_exact_s(h: int) -> int:
    answer = 0
    for r in range(B - 2 * h + 1):
        for y in range(U - h - r + 1):
            width = D - (W - 2) * h - (W - 1) * r - W * y
            assert width > 0
            answer += width
    return answer


def local_source_face(s_cap: int) -> int:
    """Slope in L of the closed local source count."""
    return sum(
        1
        for outer in range(M)
        for h in range(s_cap + 1)
        for y in range(outer + 1)
        for r in range(B - 2 * h + 1)
        if h + y + r <= U
    )


def local_weighted_kernel_face(s_cap: int) -> int:
    """Slope in L of the explicit weighted kernel Block count."""
    answer = 0
    for outer in range(M):
        for h in range(s_cap + 1):
            q = Target.q_value(M, s_cap, outer, h)
            if not (q <= outer and max(M - outer, 0) + 2 * h <= B):
                continue
            answer += sum(
                1
                for y in range(outer - q + 1)
                for r in range(max(B - 2 * h - q, 0) + 1)
                if h + q + y + r <= U
            )
    return answer


def cumulative_row(s_cap: int) -> dict[str, int]:
    global_face = sum(global_face_exact_s(h) for h in range(s_cap + 1))
    local_source = local_source_face(s_cap)
    local_kernel = local_weighted_kernel_face(s_cap)
    coupled_cap = local_source - local_kernel
    return {
        "raw_S_cap": s_cap,
        "global_face_columns": global_face,
        "local_face_source_dimension": local_source,
        "homogeneous_weighted_kernel_face_dimension": local_kernel,
        "coupled_one_node_associated_rank_cap": coupled_cap,
        "all_node_associated_rank_cap": N * coupled_cap,
        "global_face_minus_all_node_cap": global_face - N * coupled_cap,
    }


def main() -> None:
    started = time.monotonic()
    rows = tuple(cumulative_row(s_cap) for s_cap in range(S + 1))
    assert tuple(row["global_face_minus_all_node_cap"] for row in rows) == (
        -72_401_997, -93_031_377, -81_942_429,
        -55_257_276, -25_165_875, 73_983,
        16_136_673, 22_628_736, 23_088_879,
    )
    assert tuple(row["coupled_one_node_associated_rank_cap"] for row in rows) == (
        14_280, 26_695, 37_329, 46_250, 53_510,
        59_145, 63_175, 65_604, 66_420,
    )
    final = rows[-1]
    assert final == {
        "raw_S_cap": 8,
        "global_face_columns": 17_434_693_359,
        "local_face_source_dimension": 91_368,
        "homogeneous_weighted_kernel_face_dimension": 24_948,
        "coupled_one_node_associated_rank_cap": 66_420,
        "all_node_associated_rank_cap": 17_411_604_480,
        "global_face_minus_all_node_cap": 23_088_879,
    }
    assert final["global_face_columns"] == (
        Target.coefficient_count(G, M, L, B, S, U, 0, 1) -
        Target.coefficient_count(G, M, L - 1, B, S, U, 0, 1))
    assert final["coupled_one_node_associated_rank_cap"] == (
        Target.relaxed_rank_bound(M, L, B, S, U) -
        Target.relaxed_rank_bound(M, L - 1, B, S, U))

    raw_one_columns = sum(D - W * y for y in range(U + 1))
    raw_one_cap = M * (M + 1) // 2
    assert (raw_one_columns, raw_one_cap,
            raw_one_columns - N * raw_one_cap) == (
                278_534_035, 1_128, -17_164_397)
    first_positive = next(row for row in rows
                          if row["global_face_minus_all_node_cap"] > 0)
    assert first_positive["raw_S_cap"] == 5

    stable = {
        "scope": "lower-6900 target full last-face coupled associated cap",
        "parameters_n_w_g_m_B_s_U_L": (N, W, G, M, B, S, U, L),
        "raw_one_control": {
            "columns": raw_one_columns,
            "one_node_bivariate_Hermite_cap": raw_one_cap,
            "global_minus_all_node_cap": raw_one_columns - N * raw_one_cap,
        },
        "cumulative_raw_S_cap_rows": rows,
        "first_positive_coupled_certificate_raw_S_cap": 5,
        "full_face": final,
        "verdict": (
            "GREEN associated-grade dimension certificate: the full face "
            "exceeds the honest coupled weighted cap by 23,088,879. Raw-S "
            "layers through 4 remain short; including raw-S=5 is the first "
            "positive cumulative certificate. This does not prove filtered "
            "strictness or liftability through the complete old contact map."
        ),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    payload = {
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "runtime": {
            "seconds": round(time.monotonic() - started, 6),
            "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        },
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
