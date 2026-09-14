#!/usr/bin/env python3
"""Exact positive-Hasse collision blocks on the Full187 terminal frontier.

For one active-grade-82 source stream indexed by ``(r,s)``, take the
top-passive contact term (no remaining ``u0`` factor) with choices
``(f,aE,cS)``.  Its q=0 output can also be reached from the tapered source
stream ``(r-j,s+j)`` by replacing ``j`` curvature choices with slope choices
and taking coefficient-Hasse order ``q=j``.  This executable enumerates every
structured q=0 origin and checks the row identity, exact finite-field scalar,
and strict half-open X-window alignment of those collisions.

It is a symbolic combinatorial audit, not a packet-lift or confluence claim.
"""

from __future__ import annotations

from collections import Counter
import hashlib
import json
from math import factorial
from pathlib import Path
import resource

import full187_terminal_contact_hermite_budget_6900 as B


P = 2_130_706_433
N = B.N
W = B.W
G = B.G
M = B.M
D = B.D
J = B.J
SLOPE = B.SLOPE
CURVATURE = B.CURVATURE


def terminal_width(r: int, s: int) -> int:
    return B.coefficient_width(J - r - s, r, s)


def lower_width(f: int, r: int, s: int) -> int:
    return B.coefficient_width(f, r, s)


def local_scalar(f: int, a_e: int, c_s: int) -> int:
    """Multinomial coefficient times (-1/2)^cS, modulo the target prime."""
    r_choices = f - a_e - c_s
    assert min(a_e, c_s, r_choices) >= 0
    multinomial = (
        factorial(f)
        // (factorial(a_e) * factorial(c_s) * factorial(r_choices))
    )
    return (multinomial % P) * pow(-pow(2, -1, P) % P, c_s, P) % P


def output_row(r: int, s: int, f: int, a_e: int, c_s: int, q: int):
    y = J - r - s
    h = y - f
    return (
        q + f - a_e + c_s,
        a_e,
        f - a_e - c_s + r,
        s + c_s,
        h,
    )


def collision_family(r: int, s: int, f: int, a_e: int, c_s: int):
    """All tapered streams whose positive Hasse term hits the q=0 row."""
    base_row = output_row(r, s, f, a_e, c_s, 0)
    base_scalar = local_scalar(f, a_e, c_s)
    assert base_scalar
    collisions = []
    for j in range(c_s + 1):
        shifted_r = r - j
        shifted_s = s + j
        if shifted_r < 0 or shifted_s > CURVATURE:
            continue
        shifted_c = c_s - j
        shifted_row = output_row(
            shifted_r, shifted_s, f, a_e, shifted_c, j)
        assert shifted_row == base_row
        shifted_scalar = local_scalar(f, a_e, shifted_c)
        ratio = shifted_scalar * pow(base_scalar, -1, P) % P
        base_width = terminal_width(r, s)
        shifted_width = terminal_width(shifted_r, shifted_s)
        assert shifted_width == base_width + j
        # Hasse_j maps deg < base_width+j to deg < base_width.
        assert shifted_width - j == base_width
        collisions.append({
            "j": j,
            "source_r_s": (shifted_r, shifted_s),
            "source_width": shifted_width,
            "coefficient_Hasse_order": j,
            "relative_scalar_mod_p": ratio,
            "post_Hasse_output_width": shifted_width - j,
        })
    assert collisions and collisions[0]["j"] == 0
    assert collisions[0]["relative_scalar_mod_p"] == 1
    return base_row, tuple(collisions)


def structured_origins():
    rows = []
    for s in range(CURVATURE + 1):
        for r in range(SLOPE - s + 1):
            y = J - r - s
            for f in range(M):
                assert f <= y
                for a_e in range(f + 1):
                    for c_s in range(f - a_e + 1):
                        weight = f + 2 * a_e + c_s
                        if weight >= M:
                            continue
                        depth = M - weight
                        margin = lower_width(f, r, s) - G * depth
                        if margin >= 0:
                            continue
                        row, collisions = collision_family(
                            r, s, f, a_e, c_s)
                        rows.append({
                            "source_r_s": (r, s),
                            "terminal_y": y,
                            "f_aE_cS": (f, a_e, c_s),
                            "extra_charge": 2 * a_e + c_s,
                            "contact_weight": weight,
                            "agreement_Hermite_margin": margin,
                            "q0_output_T_E_R_S_h": row,
                            "collision_count": len(collisions),
                            "collisions": collisions,
                        })
    assert len(rows) == 72_850
    return tuple(rows)


def main() -> None:
    rows = structured_origins()
    by_charge = Counter(row["extra_charge"] for row in rows)
    assert by_charge == Counter({
        0: 6397, 1: 5536, 2: 9555, 3: 7928, 4: 9846, 5: 7716,
        6: 8019, 7: 5808, 8: 5148, 9: 3223, 10: 2299, 11: 990,
        12: 352, 13: 33,
    })

    charge13 = tuple(row for row in rows if row["extra_charge"] == 13)
    assert len(charge13) == 33
    charge13_types = Counter(row["f_aE_cS"] for row in charge13)
    assert charge13_types == Counter({(7, 6, 1): 11,
                                      (8, 5, 3): 11,
                                      (8, 6, 1): 11})
    assert {sum(row["source_r_s"]) for row in charge13} == {21}

    # Fix the s=0 member of each family.  These are the exact relative
    # coefficients of the A/B/C tapered differential operators.
    charge13_operator_rows = {}
    labels = {(7, 6, 1): "A", (8, 5, 3): "B", (8, 6, 1): "C"}
    for row in charge13:
        if row["source_r_s"][1] != 0:
            continue
        label = labels[row["f_aE_cS"]]
        charge13_operator_rows[label] = tuple(
            collision["relative_scalar_mod_p"]
            for collision in row["collisions"])
    assert charge13_operator_rows == {
        "A": (1, (-2) % P),
        "B": (1, (-6) % P, 12, (-8) % P),
        "C": (1, (-1) % P),
    }

    collision_lengths = Counter(row["collision_count"] for row in rows)
    charge_summaries = []
    for charge in sorted(by_charge):
        selected = tuple(row for row in rows
                         if row["extra_charge"] == charge)
        charge_summaries.append({
            "extra_charge": charge,
            "q0_structured_origin_count": len(selected),
            "distinct_transition_types_f_aE_cS": len({
                row["f_aE_cS"] for row in selected}),
            "constant_r_plus_s_lines": tuple(sorted({
                sum(row["source_r_s"]) for row in selected})),
            "collision_length_histogram": tuple(sorted(Counter(
                row["collision_count"] for row in selected).items())),
        })

    stable = {
        "scope": (
            "exact positive-Hasse same-row collision families for all 72850 "
            "agreement-Hermite-structured q0 terminal origins; no packet or "
            "confluence claim"),
        "target_p_N_w_g_m_D_J_slope_curvature": (
            P, N, W, G, M, D, J, SLOPE, CURVATURE),
        "structured_origin_count": len(rows),
        "global_collision_length_histogram": tuple(
            sorted(collision_lengths.items())),
        "every_family_upper_unitriangular": True,
        "every_diagonal_scalar_nonzero_mod_target_prime": True,
        "every_Hasse_j_taper_identity_checked": True,
        "charge_summaries": tuple(charge_summaries),
        "charge13": {
            "origin_count": len(charge13),
            "transition_types": tuple(sorted(charge13_types.items())),
            "only_source_line_r_plus_s": 21,
            "relative_operator_coefficients_A_B_C": charge13_operator_rows,
            "principal_scalars_A_B_C": (
                603_758_703, 693_269_975, 642_373_467),
            "warning": (
                "B is a Hasse-binomial operator with coefficients "
                "(1,-6,12,-8), not the ordinary composition cube of the "
                "first-Hasse operator."),
        },
        "consequence": (
            "Each selected q0 row family can be pivoted coefficientwise on "
            "its tapered source line without a strict-window loss. The same "
            "source line feeds many other row families, so this does not "
            "make the three charge13 outputs independent or prove packet "
            "containment."),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    print(json.dumps({
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
