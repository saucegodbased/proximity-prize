#!/usr/bin/env python3
"""Exact two-row cross-slope confluence gate for the Full187 second fringe.

This gate does *not* claim closure of the whole Full187 tail.  It answers the
small local question left open by the isolated (r,s)=(11,10) order-basis
experiment: once physical rows with the same target key are aggregated, do
the adjacent q=0 terminal-neighbour coefficients remove the 7797-dimensional
isolated defect?

All arithmetic and provenance are literal.  In particular, terminal terms
remain in the same brackets as their correction terms.  The two controls are
the actual q=0 node values of P59^(10,10) and P59^(9,10), not invented free
rows.  Their widths exceed N, so arbitrary all-node q=0 prescriptions are
legal.  Choosing canonical interpolation sections may induce higher jets;
these are retained as the off-diagonal operator K below rather than assumed
zero.
"""

from __future__ import annotations

from collections import Counter
from math import comb, factorial
import hashlib
import json
from pathlib import Path
import resource


P = 2_130_706_433
N = 262_144
W = 131_071
G = 180_413
M = 60
D = M * G
J = 82
L = 2_703
TERMINAL_Z = L - J
SLOPE = 21
CURVATURE = 10
INV2 = pow(2, -1, P)

ROW1 = (59, 0, 69, 10, 2624)
ROW2 = (59, 0, 68, 10, 2625)


def shapes():
    return tuple((r, s) for s in range(CURVATURE + 1)
                 for r in range(SLOPE - s + 1))


def correction_width(k: int, r: int, s: int) -> int:
    return D - W * k - (W - 1) * r - (W - 2) * s


def terminal_width(r: int, s: int) -> int:
    return correction_width(J - r - s, r, s)


def local_scalar(f: int, a_e: int, c_s: int) -> int:
    """Coefficient of E^aE R^(f-aE-cS) S^cS in contactY^f."""
    b = f - a_e - c_s
    assert min(a_e, c_s, b) >= 0
    multinomial = factorial(f) // (
        factorial(a_e) * factorial(c_s) * factorial(b))
    return multinomial * pow(-INV2 % P, c_s, P) % P


def row_of(r: int, s: int, z: int, f: int, h: int,
           a_e: int, c_s: int, q: int):
    b = f - a_e - c_s
    return (q + f - a_e + c_s, a_e, b + r, s + c_s, z + h)


def exact_target_provenance(target):
    """Invert the literal source expansion for one target monomial row.

    A source Y^k selects f copies of contactY, h copies of frozen U, and
    rem=k-f-h copies of u0.  Its coefficient is

      multinomial(k; f,h,rem) * local_scalar(f,aE,cS).

    The target tuple determines aE,cS,q,h, so this enumerates every physical
    Full187 source without a brute-force expansion.
    """
    target_t, target_e, target_r, target_s, target_z = target
    answer = []
    for r, s in shapes():
        sources = [("C", J - r - s, TERMINAL_Z)]
        sources.extend(("P", k, L - k - r - s) for k in range(M))
        for kind, k, z in sources:
            h = target_z - z
            if h < 0:
                continue
            for f in range(min(k, M - 1) + 1):
                a_e = target_e
                c_s = target_s - s
                b = f - a_e - c_s
                q = target_t - f + a_e - c_s
                rem = k - f - h
                if min(a_e, c_s, b, q, rem) < 0:
                    continue
                if b + r != target_r:
                    continue
                if f + 2 * a_e + c_s + q >= M:
                    continue
                assert row_of(r, s, z, f, h, a_e, c_s, q) == target
                scalar = (
                    comb(k, f) * comb(k - f, h)
                    * local_scalar(f, a_e, c_s)
                ) % P
                assert scalar != 0
                answer.append({
                    "kind": kind,
                    "r": r,
                    "s": s,
                    "source_y_or_k": k,
                    "contact_f": f,
                    "u_power_h": h,
                    "u0_power": rem,
                    "aE": a_e,
                    "cS": c_s,
                    "coefficient_hasse_q": q,
                    "coefficient_width": (
                        terminal_width(r, s) if kind == "C"
                        else correction_width(k, r, s)),
                    "scalar_mod_p_before_Uh_Hq": scalar,
                })
    return tuple(sorted(answer, key=lambda x: (
        x["s"], x["r"], x["kind"], x["source_y_or_k"])))


EXPECTED_ROW1_SIGNATURES = (
    ("C", 12, 9, 61, 58, 3, 0, 0, 1, 0, 76988, 2129662723),
    ("P", 12, 9, 58, 58, 0, 0, 0, 1, 0, 470201, 2130706404),
    ("P", 12, 9, 59, 58, 1, 0, 0, 1, 0, 339130, 2130704722),
    ("C", 10, 10, 62, 59, 3, 0, 0, 0, 0, 76988, 37820),
    ("P", 10, 10, 59, 59, 0, 0, 0, 0, 0, 470201, 1),
    ("C", 11, 10, 61, 58, 3, 0, 0, 0, 1, 76989, 35990),
    ("P", 11, 10, 58, 58, 0, 0, 0, 0, 1, 470202, 1),
    ("P", 11, 10, 59, 58, 1, 0, 0, 0, 1, 339131, 59),
)

EXPECTED_ROW2_SIGNATURES = (
    ("C", 13, 8, 61, 57, 4, 0, 0, 2, 0, 76987, 208220145),
    ("P", 13, 8, 57, 57, 0, 0, 0, 2, 0, 601271, 399),
    ("P", 13, 8, 58, 57, 1, 0, 0, 2, 0, 470200, 23142),
    ("P", 13, 8, 59, 57, 2, 0, 0, 2, 0, 339129, 682689),
    ("C", 11, 9, 62, 58, 4, 0, 0, 1, 0, 76987, 2114528928),
    ("P", 11, 9, 58, 58, 0, 0, 0, 1, 0, 601271, 2130706404),
    ("P", 11, 9, 59, 58, 1, 0, 0, 1, 0, 470200, 2130704722),
    ("C", 12, 9, 61, 57, 4, 0, 0, 1, 1, 76988, 1050480349),
    ("P", 12, 9, 57, 57, 0, 0, 0, 1, 1, 601272, 1065353188),
    ("P", 12, 9, 58, 57, 1, 0, 0, 1, 1, 470201, 2130704780),
    ("P", 12, 9, 59, 57, 2, 0, 0, 1, 1, 339130, 1065304453),
    ("C", 9, 10, 63, 59, 4, 0, 0, 0, 0, 76987, 595665),
    ("P", 9, 10, 59, 59, 0, 0, 0, 0, 0, 601271, 1),
    ("C", 10, 10, 62, 58, 4, 0, 0, 0, 1, 76988, 557845),
    ("P", 10, 10, 58, 58, 0, 0, 0, 0, 1, 601272, 1),
    ("P", 10, 10, 59, 58, 1, 0, 0, 0, 1, 470201, 59),
    ("C", 11, 10, 61, 57, 4, 0, 0, 0, 2, 76989, 521855),
    ("P", 11, 10, 57, 57, 0, 0, 0, 0, 2, 601273, 1),
    ("P", 11, 10, 58, 57, 1, 0, 0, 0, 2, 470202, 58),
    ("P", 11, 10, 59, 57, 2, 0, 0, 0, 2, 339131, 1711),
)


def signature(term):
    return (
        term["kind"], term["r"], term["s"], term["source_y_or_k"],
        term["contact_f"], term["u_power_h"], term["u0_power"],
        term["aE"], term["cS"], term["coefficient_hasse_q"],
        term["coefficient_width"], term["scalar_mod_p_before_Uh_Hq"],
    )


def pivot_tail_audit(r: int, s: int, z: int, principal, next_row=None):
    """Count every structural output of one P59 coefficient polynomial.

    The chosen q=0 node values determine higher coefficient Hasse jets under
    any fixed interpolation section, so q>0 outputs are retained.  The key
    triangular fact is independent of that section: every nonprincipal
    u0-free output has strictly larger passive Z.
    """
    k = 59
    counts = Counter()
    u0free_rows = set()
    minimum_later_z = None
    for f in range(k + 1):
        h_free = k - f
        for a_e in range(f + 1):
            for c_s in range(f - a_e + 1):
                base = f + 2 * a_e + c_s
                if base >= M:
                    continue
                q_count = M - base

                # h<h_free leaves a positive u0 power.  Count all q without
                # materialising the much larger error-tail row multiset.
                counts["positive_u0_occurrences"] += h_free * q_count

                # h=h_free is the agreement-visible top diagonal.
                h = h_free
                for q in range(q_count):
                    row = row_of(r, s, z, f, h, a_e, c_s, q)
                    u0free_rows.add(row)
                    if row == principal:
                        counts["principal_occurrences"] += 1
                    elif next_row is not None and row == next_row:
                        counts["next_named_row_occurrences"] += 1
                    else:
                        counts["later_u0free_occurrences"] += 1
                        minimum_later_z = (
                            row[-1] if minimum_later_z is None
                            else min(minimum_later_z, row[-1]))

    assert counts["principal_occurrences"] == 1
    assert all(row == principal or row[-1] > principal[-1]
               for row in u0free_rows)
    if next_row is not None:
        assert counts["next_named_row_occurrences"] == 1
    return {
        "source_r_s_k_z": (r, s, k, z),
        "counts": tuple(sorted(counts.items())),
        "distinct_u0free_target_rows": len(u0free_rows),
        "minimum_nonprincipal_u0free_Z": minimum_later_z,
        "all_nonprincipal_u0free_outputs_strictly_later_in_Z": True,
    }


def main():
    row1 = exact_target_provenance(ROW1)
    row2 = exact_target_provenance(ROW2)
    assert tuple(map(signature, row1)) == EXPECTED_ROW1_SIGNATURES
    assert tuple(map(signature, row2)) == EXPECTED_ROW2_SIGNATURES
    assert all(term["u0_power"] == 0 for term in row1 + row2)

    # The exact adjacent q=0 pivots have scalar one and legal all-node width.
    pivot20 = next(term for term in row1 if
                   term["kind"] == "P" and term["r"] == 10
                   and term["s"] == 10 and term["source_y_or_k"] == 59)
    pivot19 = next(term for term in row2 if
                   term["kind"] == "P" and term["r"] == 9
                   and term["s"] == 10 and term["source_y_or_k"] == 59)
    assert pivot20["scalar_mod_p_before_Uh_Hq"] == 1
    assert pivot19["scalar_mod_p_before_Uh_Hq"] == 1
    assert pivot20["coefficient_width"] == 470_201 > N
    assert pivot19["coefficient_width"] == 601_271 > 2 * N

    # At N nodes the expanded control matrix is [[I,0],[K,I]].  K is the
    # *actual* deterministic operator induced by the chosen interpolation
    # section and all correlated d20 descendants (including H1(P59^20)); it
    # is not set to zero or promoted to a free variable.  Unit diagonal gives
    # the exact inverse x20=-b1, x19=-b2-K*x20 for every K and fixed terminal
    # data.  Hence rank=2N over the target field without constructing K.
    expanded_system = {
        "node_block_matrix": "[[I_N,0],[K_actual,I_N]]",
        "terminal_correlations_retained": (
            "b1 contains C(62,59) U^3 C20 and every other same-key term; "
            "b2 contains C(63,59) U^4 C19, the full correlated d20 q1 "
            "bracket, and every other same-key term"),
        "section": "x20=-b1; x19=-b2-K_actual*x20",
        "determinant": 1,
        "rank": 2 * N,
        "cokernel_dimension": 0,
        "isolated_defect_removed": 7_797,
    }

    tails20 = pivot_tail_audit(10, 10, L - 59 - 10 - 10,
                               ROW1, ROW2)
    tails19 = pivot_tail_audit(9, 10, L - 59 - 9 - 10, ROW2)

    stable = {
        "scope": (
            "exact aggregation and section of the two named Full187 "
            "second-fringe physical target rows; later passive-Z and "
            "positive-u0 tails are audited but not closed"),
        "target_p_N_W_G_M_D_J_L": (P, N, W, G, M, D, J, L),
        "target_rows": (ROW1, ROW2),
        "same_key_provenance_counts": (len(row1), len(row2)),
        "row1_provenance": row1,
        "row2_provenance": row2,
        "expanded_target_p_system": expanded_system,
        "pivot_tail_audits": (tails20, tails19),
        "decision": "GREEN_TWO_PRINCIPAL_ROWS_UNITRIANGULAR",
        "interpretation": (
            "The 7797 defect is an artefact of isolating stream (11,10): "
            "the adjacent complete q=0 P59 coefficients give independent "
            "unit pivots after physical same-key aggregation.  This kills "
            "only that two-row principal obstruction.  A full proof still "
            "must solve the strictly later-Z u0-free tails and the positive-"
            "u0 connecting tails, including the enumerated curvature "
            "diagonals (12,9), (13,8), and (11,9)."),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    output = {
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
