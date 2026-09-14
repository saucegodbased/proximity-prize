#!/usr/bin/env python3
"""Exact Full187 width receipt for the pure, slope, curvature companions.

This uses the intended retained-bad direction Q=Xi_E^2, whose degree is
2(N-g), rather than the pessimistic generic bound deg Q<=g-1.  It checks all
61 centered-value expansion layers for the raw R/S companions and also the
Q'/Q'' correction branches in the fully centered derivatives.  This is only
a source-legality/contact-shape receipt, not a connecting-rank theorem.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import resource
import time


N = 262_144
G = 180_413
E = N - G
W = 131_071
M = 60
D = M * G
J = 82
L = 2703
QDEG = 2 * E


def raw_gap(f: int, r: int, s: int) -> int:
    """D minus maximal weighted cost of R^r S^s V^m at Y-degree f."""
    return (D - ((M - f) * QDEG + W * f
                 + (W - 1) * r + (W - 2) * s))


def derivative_correction_gap(f: int, derivative_order: int) -> int:
    """Gap for Q^(m-f) Q^(derivative_order) Z V^f.

    Here ``Q^(derivative_order)`` means the ordinary derivative, not a power;
    its degree is bounded by QDEG-derivative_order.
    """
    q_derivative_degree = QDEG - derivative_order
    return D - ((M - f) * QDEG + q_derivative_degree + W * f)


def layer_receipt(name, gaps):
    assert len(gaps) == M + 1
    minimum = min(gaps)
    minimizing_layers = tuple(index for index, gap in enumerate(gaps)
                              if gap == minimum)
    assert minimum > 0
    return {
        "name": name,
        "minimum_D_minus_weighted_cost": minimum,
        "minimum_strict_integer_slack": minimum - 1,
        "minimizing_Y_degrees": minimizing_layers,
        "first_last_gap": (gaps[0], gaps[-1]),
        "all_61_layers_strictly_legal": True,
    }


def main():
    started = time.monotonic()
    assert (E, QDEG, D, G - QDEG, QDEG - W) == (
        81_731, 163_462, 10_824_780, 16_951, 32_391)
    assert M + (J + 1 - M) == J + 1 == 83 <= L

    pure = tuple(raw_gap(f, 0, 0) for f in range(M + 1))
    raw_r = tuple(raw_gap(f, 1, 0) for f in range(M + 1))
    raw_s = tuple(raw_gap(f, 0, 1) for f in range(M + 1))
    q_prime = tuple(derivative_correction_gap(f, 1)
                    for f in range(M + 1))
    q_second = tuple(derivative_correction_gap(f, 2)
                     for f in range(M + 1))

    rows = (
        layer_receipt("V^60 Z^23", pure),
        layer_receipt("R V^60 Z^22", raw_r),
        layer_receipt("S V^60 Z^22", raw_s),
        layer_receipt("Q' Z V^60 Z^22 branch", q_prime),
        layer_receipt("Q'' Z V^60 Z^22 branch", q_second),
    )
    expected_minimum_gaps = (1_017_060, 885_990, 885_991, 853_599, 853_600)
    assert tuple(row["minimum_D_minus_weighted_cost"] for row in rows) == (
        expected_minimum_gaps)
    assert all(row["minimizing_Y_degrees"] == (0,) for row in rows)

    # Fully centered derivatives V1=R-Q'Z and V2=S-Q''Z are legal because
    # both branches are legal.  This assertion is only linear-subspace
    # membership; it says nothing about their connecting images.
    fully_centered = {
        "V1_definition": "R-Q'Z",
        "V2_definition": "S-Q''Z",
        "V1_V60_Z22_worst_strict_slack": min(
            min(raw_r), min(q_prime)) - 1,
        "V2_V60_Z22_worst_strict_slack": min(
            min(raw_s), min(q_second)) - 1,
    }
    assert fully_centered == {
        "V1_definition": "R-Q'Z",
        "V2_definition": "S-Q''Z",
        "V1_V60_Z22_worst_strict_slack": 853_598,
        "V2_V60_Z22_worst_strict_slack": 853_599,
    }

    maximum_raw_derivative_degree = max(
        degree for degree in range(J + 1)
        if raw_gap(0, degree, 0) > 0)
    assert maximum_raw_derivative_degree == 7

    stable = {
        "scope": (
            "Full187 exact arithmetic source-width receipt for three centered "
            "first-shell companions under Q=Xi_E^2; no rank/confluence claim"
        ),
        "parameters_N_g_e_w_m_D_J_L_degQ": (
            N, G, E, W, M, D, J, L, QDEG),
        "identities": {
            "g_minus_degQ": G - QDEG,
            "degQ_minus_w": QDEG - W,
            "raw_gap_formula": (
                "60*(g-degQ)+f*(degQ-w)-(w-1)r-(w-2)s"
            ),
            "combined_shell_grade": J + 1,
            "pure_seed_exponent": J + 1 - M,
            "slope_or_curvature_seed_exponent": J - M,
        },
        "layer_receipts": rows,
        "fully_centered_derivative_receipt": fully_centered,
        "largest_raw_pure_derivative_degree_licensed_by_width_at_f0": (
            maximum_raw_derivative_degree),
        "shapes_in_conservative103": ((0, 0), (1, 0), (0, 1)),
        "decision": "GREEN_SOURCE_LEGALITY_ONLY_FOR_PURE_R_S_COMPANIONS",
        "scope_guard": (
            "This proves neither coefficientwise containment of F0..F3 nor "
            "global safe103 recurrence/confluence."
        ),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    print(json.dumps({
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "runtime_receipt": {
            "elapsed_seconds": round(time.monotonic() - started, 6),
            "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            "external_memory_cap_bytes": 4 * 1024**3,
        },
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
