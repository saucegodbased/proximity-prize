#!/usr/bin/env python3
"""Exact target-field bypass of the first Full187 Hermite-slide obstruction.

The direct ``y=8`` correction cannot prescribe the all-node coefficient
Hasse jet of order 26: its strict X window is smaller than ``27*N``.  This
audit never asks for that jet.  Instead it replaces one unit of Hasse order
by one unit of Y-contact order and one unit of source R exponent.

For each terminal charge-13 stream ``s`` and ``k=1,...,9`` use the legal
source layer

  P[k,s](X) Y^(8+k) R^(21-s-k) S^s Z^2674.

Its complete depth-26 all-node Hermite section is prescribed to have only
jet ``26-k`` nonzero.  The nonzero jet is a binomial multiple of
``U1^53 H_26(C_s)``.  The nine resulting contact scalars are the ninth
finite difference of a polynomial of degree ``aE+cS <= 8``, so they cancel
all 495 original ``f=8,q=26`` provenance terms exactly.

The script also classifies, rather than discards, every other contact term.
At prescribed jets the same-Z full-node residual starts only in the strict
next contact-degree filtration ``aE+cS >= 9``.  Other top terms have larger
passive Z, and non-top terms contain U0 and are error-node-only.  Uncontrolled
jets q>=26 are similarly classified.  Boundary tails remain part of the
source map.  This is a quotient step, not a four-packet lift.
"""

from __future__ import annotations

from collections import Counter
import hashlib
import json
from math import comb, factorial
from pathlib import Path
import resource


P = 2_130_706_433
N = 262_144
W = 131_071
G = 180_413
ERRORS = N - G
M = 60
D = M * G
J = 82
L = 2_703
SLOPE = 21
CURVATURE = 10
ORIGINAL_Y = 61
ORIGINAL_Z = 2_621
CORRECTION_Z = 2_674
ORIGINAL_F = 8
ORIGINAL_Q = 26
DIFFERENCE_ORDER = 9

assert P == 1 + 8_128 * N
assert P % 2 == 1


def width(y: int, r: int, s: int) -> int:
    return D - W * y - (W - 1) * r - (W - 2) * s


def row(y: int, r: int, s: int, z: int, f: int, h: int,
        a_e: int, c_s: int, q: int) -> tuple[int, ...]:
    assert min(y, r, s, z, f, h, a_e, c_s, q) >= 0
    assert f <= y and h <= y - f and a_e + c_s <= f
    assert q + f + 2 * a_e + c_s < M
    return (
        q + f - a_e + c_s,
        a_e,
        r + f - a_e - c_s,
        s + c_s,
        z + h,
    )


def local_multinomial(f: int, a_e: int, c_s: int) -> int:
    """Integral part of the local contact scalar, without (-1/2)^cS."""
    if min(a_e, c_s) < 0 or a_e + c_s > f:
        return 0
    return factorial(f) // (
        factorial(a_e) * factorial(c_s) * factorial(f - a_e - c_s))


def local_scalar(f: int, a_e: int, c_s: int) -> int:
    return (local_multinomial(f, a_e, c_s)
            * pow(-pow(2, -1, P) % P, c_s, P)) % P


def correction_coefficient(k: int) -> int:
    assert 1 <= k <= DIFFERENCE_ORDER
    signed = -1 if k % 2 else 1
    return comb(ORIGINAL_Y, ORIGINAL_F) * signed * comb(
        DIFFERENCE_ORDER, k) % P


def finite_difference_and_target_receipt():
    base = comb(ORIGINAL_Y, ORIGINAL_F)
    assert base % P == 814_121_332
    coefficients = tuple(
        correction_coefficient(k) for k in range(1, DIFFERENCE_ORDER + 1))
    assert coefficients == (
        1_195_733_744,
        1_609_184_323,
        1_927_120_401,
        305_379_048,
        1_825_327_385,
        203_586_032,
        521_522_110,
        934_972_689,
        1_316_585_101,
    )

    # The load-bearing identity is integral, before reduction modulo p.
    # f |-> multinomial(f;a,c,f-a-c) is a polynomial in f of degree a+c.
    # Its ninth forward difference vanishes for every a+c <= 8.
    for a_e in range(ORIGINAL_F + 1):
        for c_s in range(ORIGINAL_F - a_e + 1):
            integer_difference = sum(
                (-1) ** k * comb(DIFFERENCE_ORDER, k)
                * local_multinomial(ORIGINAL_F + k, a_e, c_s)
                for k in range(DIFFERENCE_ORDER + 1)
            )
            assert integer_difference == 0

    target_occurrences = []
    target_rows = set()
    by_contact_degree = Counter()
    minimum_width = None
    maximum_width = None
    source_layers = set()

    for source_s in range(CURVATURE + 1):
        original_r = SLOPE - source_s
        original_width = width(ORIGINAL_Y, original_r, source_s)
        assert original_width == 76_979 + source_s
        for a_e in range(ORIGINAL_F + 1):
            for c_s in range(ORIGINAL_F - a_e + 1):
                assert ORIGINAL_Q + ORIGINAL_F + 2 * a_e + c_s < M
                expected = row(
                    ORIGINAL_Y, original_r, source_s, ORIGINAL_Z,
                    ORIGINAL_F, ORIGINAL_Y - ORIGINAL_F,
                    a_e, c_s, ORIGINAL_Q,
                )
                target_rows.add(expected)
                by_contact_degree[a_e + c_s] += 1
                scalar_sum = (
                    base * local_scalar(ORIGINAL_F, a_e, c_s)) % P

                correction_terms = []
                for k in range(1, DIFFERENCE_ORDER + 1):
                    y = ORIGINAL_F + k
                    r = original_r - k
                    s = source_s
                    z = CORRECTION_Z
                    q = ORIGINAL_Q - k
                    assert min(r, q) >= 0
                    assert q < 26
                    assert y + r + s == 29 < J
                    assert y + r + s + z == L
                    assert r + s == SLOPE - k <= SLOPE
                    assert s <= CURVATURE
                    source_layers.add((y, r, s, z))

                    source_width = width(y, r, s)
                    assert source_width == 7_023_742 + s - k
                    assert source_width > 26 * N
                    minimum_width = source_width if minimum_width is None else min(
                        minimum_width, source_width)
                    maximum_width = source_width if maximum_width is None else max(
                        maximum_width, source_width)

                    actual = row(y, r, s, z, y, 0, a_e, c_s, q)
                    assert actual == expected
                    coefficient = correction_coefficient(k)
                    scalar = coefficient * local_scalar(y, a_e, c_s) % P
                    scalar_sum = (scalar_sum + scalar) % P
                    correction_terms.append((k, (y, r, s, z), q, scalar))

                assert scalar_sum == 0
                target_occurrences.append((
                    source_s, a_e, c_s, expected, tuple(correction_terms)))

    assert len(target_occurrences) == 11 * 45 == 495
    assert len(source_layers) == 11 * DIFFERENCE_ORDER == 99
    assert (minimum_width, maximum_width) == (7_023_733, 7_023_751)
    assert minimum_width - 26 * N == 207_989

    return {
        "finite_difference_order": DIFFERENCE_ORDER,
        "base_binom_61_8_mod_p": base % P,
        "correction_coefficients_k1_to_k9_mod_p": coefficients,
        "coefficient_formula": "binom(61,8)*(-1)^k*binom(9,k)",
        "integral_identity": (
            "sum_(k=0)^9 (-1)^k binom(9,k) "
            "multinomial(8+k;aE,cS,8+k-aE-cS)=0 for aE+cS<=8"
        ),
        "target_original_provenance_and_distinct_rows": (
            len(target_occurrences), len(target_rows)),
        "target_provenance_by_aE_plus_cS": tuple(sorted(
            by_contact_degree.items())),
        "correction_source_layer_count": len(source_layers),
        "correction_source_y_r_s_z_first_last": (
            min(source_layers), max(source_layers)),
        "correction_q_range": (17, 25),
        "correction_width_min_max": (minimum_width, maximum_width),
        "minimum_width_minus_26N": minimum_width - 26 * N,
        "all_target_rows_match_in_T_E_R_S_Z": True,
        "all_target_scalars_cancel_mod_target_prime": True,
        "target_occurrence_digest": hashlib.sha256(json.dumps(
            target_occurrences, separators=(",", ":"),
        ).encode()).hexdigest(),
    }


def classify_other_tails():
    """Classify all syntactic tails of the chosen canonical A_26 sections.

    Jets below 26 other than q=26-k are prescribed zero.  Jets q>=26 are
    determined (not controlled) by the canonical degree-<26N polynomial and
    are conservatively counted as potentially nonzero.
    """
    selected_jet_occurrences = Counter()
    selected_jet_rows = {name: set() for name in (
        "desired_degree_le_8",
        "same_Z_degree_ge_9",
        "larger_Z_full_node",
        "error_only",
    )}
    suppressed_low_jet_occurrences = 0
    higher_jet_occurrences = Counter()
    same_z_aggregate = Counter()

    for source_s in range(CURVATURE + 1):
        original_r = SLOPE - source_s
        # Aggregate every same-Z, full-Y selected-jet row across k.  Terms
        # with y<aE+cS have multinomial coefficient zero and need not be
        # explicitly present.  The original k=0 term exists exactly through
        # degree eight.  The ninth difference makes all degree<=8 sums zero;
        # the first possible residual is the strict next degree, nine.
        for a_e in range(18):
            for c_s in range(18 - a_e):
                contact_degree = a_e + c_s
                if 34 + 2 * a_e + c_s >= M:
                    continue
                aggregate = 0
                if contact_degree <= ORIGINAL_F:
                    aggregate += (
                        comb(ORIGINAL_Y, ORIGINAL_F)
                        * local_scalar(ORIGINAL_F, a_e, c_s))
                for k in range(1, DIFFERENCE_ORDER + 1):
                    y = ORIGINAL_F + k
                    if contact_degree <= y:
                        aggregate += (
                            correction_coefficient(k)
                            * local_scalar(y, a_e, c_s))
                aggregate %= P
                if contact_degree <= ORIGINAL_F:
                    assert aggregate == 0
                    same_z_aggregate["cancelled_degree_le_8"] += 1
                else:
                    # Ninth finite difference of a degree-d falling
                    # factorial at 8 is nonzero here (9<=d<=17<p).
                    assert contact_degree >= 9 and aggregate != 0
                    same_z_aggregate["residual_degree_ge_9"] += 1

        for k in range(1, DIFFERENCE_ORDER + 1):
            y = ORIGINAL_F + k
            r = original_r - k
            s = source_s
            q_selected = ORIGINAL_Q - k
            for f in range(y + 1):
                for a_e in range(f + 1):
                    for c_s in range(f - a_e + 1):
                        base_without_q = f + 2 * a_e + c_s
                        for h in range(y - f + 1):
                            # Every syntactically legal lower jet other than
                            # q_selected is literally zero by the A_26
                            # residue prescription.
                            suppressed_low_jet_occurrences += sum(
                                q + base_without_q < M
                                for q in range(26) if q != q_selected)

                            if q_selected + base_without_q < M:
                                key = row(y, r, s, CORRECTION_Z,
                                          f, h, a_e, c_s, q_selected)
                                if f == y:
                                    assert h == 0
                                    if a_e + c_s <= ORIGINAL_F:
                                        category = "desired_degree_le_8"
                                    else:
                                        category = "same_Z_degree_ge_9"
                                        assert a_e + c_s >= 9
                                elif h == y - f:
                                    category = "larger_Z_full_node"
                                    assert key[-1] > CORRECTION_Z
                                else:
                                    category = "error_only"
                                    # u0 exponent y-f-h is positive, so this
                                    # vanishes on every agreement node.
                                    assert y - f - h > 0
                                selected_jet_occurrences[category] += 1
                                selected_jet_rows[category].add(key)

                            for q in range(26, M - base_without_q):
                                key = row(y, r, s, CORRECTION_Z,
                                          f, h, a_e, c_s, q)
                                if f == y:
                                    assert h == 0
                                    category = "same_Z_higher_Hasse"
                                    # Relative to the desired q=26-k,f=8+k
                                    # head, T+3E (=contact weight) is larger.
                                    assert (q + f + 2 * a_e + c_s
                                            > 34 + 2 * a_e + c_s)
                                elif h == y - f:
                                    category = "larger_Z_full_node"
                                    assert key[-1] > CORRECTION_Z
                                else:
                                    category = "error_only"
                                    assert y - f - h > 0
                                higher_jet_occurrences[category] += 1

    # There are nine correction contributions for each of the 495 original
    # provenance terms.  Their aggregate, together with the original, is zero.
    assert selected_jet_occurrences["desired_degree_le_8"] == 9 * 495
    assert selected_jet_occurrences["same_Z_degree_ge_9"] > 0
    assert same_z_aggregate["cancelled_degree_le_8"] == 11 * 45
    assert same_z_aggregate["residual_degree_ge_9"] > 0
    assert higher_jet_occurrences["same_Z_higher_Hasse"] > 0

    return {
        "A26_residue_rule": (
            "for P[k,s], set every H_q with 0<=q<26 and q!=26-k to "
            "zero; prescribe only H_(26-k)"
        ),
        "suppressed_syntactic_low_jet_occurrences": (
            suppressed_low_jet_occurrences),
        "selected_nonzero_jet_occurrences_by_tail_class": tuple(sorted(
            selected_jet_occurrences.items())),
        "selected_nonzero_jet_distinct_rows_by_tail_class": tuple(sorted(
            (name, len(rows)) for name, rows in selected_jet_rows.items())),
        "same_Z_full_Y_aggregate_classes_per_stream_aE_cS": tuple(sorted(
            same_z_aggregate.items())),
        "higher_uncontrolled_jet_potential_occurrences": tuple(sorted(
            higher_jet_occurrences.items())),
        "tail_filtration": (
            "At the prescribed jets, the desired same-Z band cancels "
            "through aE+cS=8 and any same-Z residual begins at aE+cS=9; "
            "all other full-node terms have larger Z; every non-top term "
            "has a positive U0 power and is error-node-only. For q>=26, "
            "same-Z terms have strictly larger shifted weight T+3E, while "
            "the same larger-Z/error-only dichotomy handles f<y."
        ),
        "boundary_scope": (
            "Every P[k,s] boundary column is retained. No beta value, "
            "packet residue, confluence, or final kernel is asserted."
        ),
    }


def main():
    target = finite_difference_and_target_receipt()
    tails = classify_other_tails()
    stable = {
        "scope": (
            "exact target-field/source-window ninth-finite-difference "
            "bypass of the Full187 f8,q26 top-contact obstruction; complete "
            "tail taxonomy but no packet-lift claim"
        ),
        "target_p_N_w_g_e_m_D_J_L_q_t": (
            P, N, W, G, ERRORS, M, D, J, L, SLOPE, CURVATURE),
        "original_source_y_r_s_z": "(61,21-s,s,2621), 0<=s<=10",
        "original_contact_f_q_h": (ORIGINAL_F, ORIGINAL_Q,
                                     ORIGINAL_Y - ORIGINAL_F),
        "correction_source_formula": (
            "P[k,s](X) Y^(8+k) R^(21-s-k) S^s Z^2674, 1<=k<=9"
        ),
        "correction_jet_formula": (
            "H_(26-k)(P[k,s])(x) = binom(61,8)(-1)^k binom(9,k) "
            "U1(x)^53 H_26(C_s)(x); every other jet below 26 is zero"
        ),
        "Hermite_section": (
            "all-node CRT in A_26 gives the canonical representative of "
            "degree <26N, which lies strictly inside every correction window"
        ),
        "target_receipt": target,
        "tail_receipt": tails,
        "exact_fourth_packet": "F3=B*(Y-P-(Z-gamma)*q_H)",
        "pure_Z1_rejected": True,
        "decision": "GREEN_UNIFORM_F8_Q26_NINTH_DIFFERENCE_BYPASS",
        "remaining_gate": (
            "compose this filtered quotient step with the complete mixed "
            "sharp/CRT reducer, retain every classified contact and boundary "
            "tail, and apply that operator to literal F0,F1,F2,F3"
        ),
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
