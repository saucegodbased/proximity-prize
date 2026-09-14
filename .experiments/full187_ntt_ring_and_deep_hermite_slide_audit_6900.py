#!/usr/bin/env python3
"""Exact ring/interface audit for the Full187 charge-13 reducer.

The reduced NTT value ring ``Fp[X]/(X^N-1)`` is useful for pointwise
multiplication, but it cannot carry coefficient Hasse jets or strict source
windows as modules.  This script checks that obstruction on the frozen target
instance and identifies the correct thickened Hermite algebras.

It also strengthens the low-active cross-origin slide: the y=8 correction has
room for 26 complete all-node jets and the y=7 correction has room for 27.
Consequently the triangular y=8/y=7 slide cancels every top-passive f=8 term
through Hasse order 25 and every f=7 term through order 26, not merely the 80
A/B/C principal provenance terms.  The first unsupported full-node layer is
f=8,q=26; its partial coefficient fringe is recorded rather than promoted.
"""

from __future__ import annotations

from collections import Counter
import hashlib
import json
from math import comb
from pathlib import Path
import resource

import full187_target_charge13_transposed_four_residue_gate_6900 as T


P = 2_130_706_433
N = 262_144
W = 131_071
G = 180_413
ERRORS = N - G
M = 60
D = M * G
J = 82
L = 2703
SLOPE = 21
CURVATURE = 10
BASE_WIDTH = 76_979


def source_width(s: int, slide: int) -> int:
    """Width after replacing (y,z)=(61,2621) by (61-slide,2621+slide)."""
    assert 0 <= s <= CURVATURE
    y = 61 - slide
    r = SLOPE - s
    answer = D - W * y - (W - 1) * r - (W - 2) * s
    assert answer == BASE_WIDTH + s + slide * W
    return answer


def principal_provenance_count() -> tuple[int, int, Counter]:
    families = {
        "A": (7, 1),
        "B": (8, 3),
        "C": (8, 1),
    }
    terms = 0
    rows = set()
    by_family = Counter()
    for family, (f, q_max) in families.items():
        for output_s in range(CURVATURE + 1):
            for q in range(q_max + 1):
                source_s = output_s + q
                if source_s > CURVATURE:
                    continue
                terms += 1
                by_family[family] += 1
                rows.add((family, output_s, f))
    assert (terms, len(rows), by_family) == (
        80, 33, Counter(A=21, B=38, C=21))
    return terms, len(rows), by_family


def selected_top_terms(f: int, q_max: int):
    """Every syntactic original top-passive term in the selected q window."""
    terms = []
    rows = set()
    by_q = Counter()
    for source_s in range(CURVATURE + 1):
        source_r = SLOPE - source_s
        for a_e in range(f + 1):
            for c_s in range(f - a_e + 1):
                for q in range(q_max + 1):
                    assert q + f + 2 * a_e + c_s < M
                    row = (
                        q + f - a_e + c_s,
                        a_e,
                        source_r + f - a_e - c_s,
                        source_s + c_s,
                        2621 + 61 - f,
                    )
                    terms.append((source_s, f, a_e, c_s, q, row))
                    rows.add(row)
                    by_q[q] += 1
    return tuple(terms), rows, by_q


def deep_low_slide_receipt(q26_counterexample):
    # First kill f=8 with y=8.  Its f=7 term is then killed with y=7.
    low8 = (-comb(61, 8)) % P
    low7 = (-(comb(61, 7) + comb(8, 7) * low8)) % P
    assert (low8, low7) == (1_316_585_101, 1_815_287_010)
    assert (comb(61, 8) + low8) % P == 0
    assert (comb(61, 7) + comb(8, 7) * low8 + low7) % P == 0

    minimum8 = min(source_width(s, 53) for s in range(11))
    minimum7 = min(source_width(s, 54) for s in range(11))
    assert (minimum8, minimum7) == (7_023_742, 7_154_813)
    depth8 = minimum8 // N
    depth7 = minimum7 // N
    assert (depth8, depth7) == (26, 27)
    assert minimum8 - depth8 * N == 207_998
    assert minimum7 - depth7 * N == 76_925

    f8_terms, f8_rows, f8_by_q = selected_top_terms(8, depth8 - 1)
    f7_terms, f7_rows, f7_by_q = selected_top_terms(7, depth7 - 1)
    assert len(f8_terms) == 12_870 and len(f8_rows) == 3_870
    assert len(f7_terms) == 10_692 and len(f7_rows) == 3_412
    assert set(f8_by_q.values()) == {495}
    assert set(f7_by_q.values()) == {396}
    assert f8_rows.isdisjoint(f7_rows)

    # q<26 for P8 is a literal all-node Hermite prescription in A_26.
    # After choosing P8, P7 has one extra complete jet.  At q=26 choose its
    # arbitrary H_26 values to cancel the already determined original+P8 f=7
    # values.  No formula for P8's H_26 is assumed.
    assert source_width(0, 53) < 27 * N
    first_f8_unsupported_full_node_order = depth8
    p8_partial_fringe = minimum8 - depth8 * N
    assert q26_counterexample["omega26_xNminus1_coefficient_mod_p"] != 0
    assert q26_counterexample["forced_standard_degree"] == 27 * N - 1
    assert q26_counterexample["forced_standard_degree"] >= max(
        source_width(s, 53) for s in range(11))

    principal_terms, principal_rows, principal_by_family = (
        principal_provenance_count())
    assert principal_terms <= len(f8_terms) + len(f7_terms)

    return {
        "slides_original_to_y8_y7": ((61, 2621), (8, 2674), (7, 2675)),
        "same_combined_grade": L,
        "jet_scalars_low8_low7_mod_p": (low8, low7),
        "minimum_width_y8_y7": (minimum8, minimum7),
        "complete_all_node_jet_depth_y8_y7": (depth8, depth7),
        "fringe_after_complete_jets_y8_y7": (
            p8_partial_fringe, minimum7 - depth7 * N),
        "prescriptions": (
            "in A_26, H_q(P8)=low8*u1^53*H_q(C), 0<=q<=25",
            "in A_27, H_q(P7)=low7*u1^54*H_q(C), 0<=q<=25",
            "choose H_26(P7) after P8 to cancel the remaining f7,q=26 row",
        ),
        "cancelled_original_top_provenance_f8_f7": (
            len(f8_terms), len(f7_terms), len(f8_terms) + len(f7_terms)),
        "cancelled_distinct_top_rows_f8_f7": (
            len(f8_rows), len(f7_rows), len(f8_rows) + len(f7_rows)),
        "principal_A_B_C_subset_terms_rows": (
            principal_terms, principal_rows),
        "principal_terms_by_family": tuple(sorted(principal_by_family.items())),
        "first_unsupported_complete_f8_jet_order": (
            first_f8_unsupported_full_node_order),
        "p8_q26_adjustment_subspace_dimension_upper_bound": (
            p8_partial_fringe),
        "q26_f8_literal_C_equals_one_counterexample": q26_counterexample,
        "q26_scope_guard": (
            "Uniform f8,q26 extension is false even for C=1: the unique "
            "depth-27 constant-jet lift has a nonzero X^(27N-1) term, beyond "
            "every y=8 strict window."
        ),
        "selected_term_digest": hashlib.sha256(json.dumps(
            (f8_terms, f7_terms), separators=(",", ":"),
        ).encode()).hexdigest(),
    }


def frozen_value_ring_receipt():
    instance = T.build_target_instance()

    # Convert the two frozen evaluation vectors to their unique representatives
    # in R=Fp[X]/(X^N-1).  Both circulant multipliers are literally dense.
    u1_coefficients = instance.u1_values.copy()
    T.ntt(u1_coefficients, inverse=True)
    u0_coefficients = [0] * G + [1] * ERRORS
    T.ntt(u0_coefficients, inverse=True)
    assert all(u1_coefficients) and all(u0_coefficients)

    # Exact first-failing-jet certificate for the y=8 slide, with C=1.
    # Since p=1+8128*N, the depth-27 constant-jet lift of the value polynomial
    # v representing U1^53 is v(X^p).  Writing Omega=X^N-1 gives
    # X^(i*p)=X^i*(1+Omega)^(8128*i).  Its Omega^26, X^(N-1) coefficient is
    # therefore v_(N-1)*binom(8128*(N-1),26), and is nonzero below.
    u1_pow53_coefficients = instance.u1_pow53.copy()
    T.ntt(u1_pow53_coefficients, inverse=True)
    frobenius_stride = (P - 1) // N
    assert frobenius_stride == 8128
    last = N - 1
    omega26_last = (
        u1_pow53_coefficients[last]
        * (comb(frobenius_stride * last, 26) % P)
    ) % P
    low8 = (-comb(61, 8)) % P
    scaled_omega26_last = low8 * omega26_last % P
    assert (
        u1_pow53_coefficients[last],
        comb(frobenius_stride * last, 26) % P,
        omega26_last,
        scaled_omega26_last,
    ) == (2_020_367_218, 400_901_196, 2_110_190_167, 625_032_631)
    q26_counterexample = {
        "input_stream_polynomial": "C(X)=1",
        "constant_jet_lift": (
            "low8*v(X^p) mod Omega^27, v is the degree<N representative "
            "of U1^53 and p=1+8128N"),
        "v_coefficient_at_X_Nminus1": u1_pow53_coefficients[last],
        "binomial_8128_times_Nminus1_choose_26_mod_p": (
            comb(frobenius_stride * last, 26) % P),
        "omega26_xNminus1_coefficient_mod_p": scaled_omega26_last,
        "forced_standard_degree": 27 * N - 1,
        "maximum_y8_window_degree": max(
            source_width(s, 53) for s in range(11)) - 1,
        "result": "NO_LEGAL_Y8_DEPTH27_LIFT",
    }

    # Hasse differentiation cannot descend to R: Omega represents zero, but
    # H_1(Omega)=N*X^(N-1) is nonzero because p does not divide N.
    assert N % P != 0

    # Exact elementary stabilizer proof for W_d=span(1,...,X^(d-1)):
    # u*1 in W_d first forces supp(u)<d.  If a>0 is any supported exponent,
    # multiplying by X^(d-a) (which lies in W_d) gives the noncancellable term
    # u_a X^d outside W_d.  Hence only constants stabilize a proper W_d.
    for d in (1, BASE_WIDTH, BASE_WIDTH + 10, N - 1):
        assert 0 < d < N
        for a in (1, min(7, d - 1), d - 1):
            if 0 < a < d:
                witness = d - a
                assert 0 < witness < d and a + witness == d < N

    return {
        "value_ring": "R=Fp[X]/(X^N-1) ~= product_(x in Domain) Fp",
        "u0_nonzero_coefficient_count": sum(bool(x) for x in u0_coefficients),
        "u1_nonzero_coefficient_count": sum(bool(x) for x in u1_coefficients),
        "u0_coefficients_sha256": T.sha256_u32(u0_coefficients),
        "u1_coefficients_sha256": T.sha256_u32(u1_coefficients),
        "hasse_descent_counterexample": (
            "[X^N-1]=0 in R but H_1(X^N-1)=N*X^(N-1)!=0 in R"),
        "proper_window_multiplier_stabilizer": "Fp constants only",
        "consequence": (
            "R can store row values and apply diagonal multipliers, but it "
            "cannot be the coefficient-Hasse/window quotient module."
        ),
    }, q26_counterexample


def mixed_capacity_interface():
    return {
        "correct_algebra_at_depth_d": (
            "A_d=Fp[X]/(Lambda_G^d*Lambda_E) ~= "
            "product_G Fp[eps]/eps^d x product_E Fp"),
        "dimension": "d*180413+81731",
        "canonical_section": (
            "take the unique representative of degree < d*g+e; the strong "
            "capacity inequality places it inside the source window"),
        "frozen_multiplier_lift": (
            "use the CRT constant-jet lift: value u(x), higher G-jets zero; "
            "ordinary multiplication by the dense R representative is wrong"),
        "mixed_closure_receipt": (
            "full187_mixed_pivot_capacity_closure_6900.py covers all 70543 "
            "sharp-pivot escapes; 63094 use safe103 shapes and 7449 use "
            "legal lower-active full187 witnesses with u1 exponent zero"),
        "remaining_orientation_data": (
            "For every chosen canonical CRT correction, replay and order all "
            "other contact and boundary tails. Support coverage alone does "
            "not define this coupled Schur reducer."
        ),
        "naive_row_value_storage_bytes": 70_543 * N * 4,
    }


def main():
    plain_value_ring, q26_counterexample = frozen_value_ring_receipt()
    stable = {
        "scope": (
            "exact target NTT-ring/window obstruction and deep low-y Hermite "
            "slide; exact F3 only; no production or packet-lift claim"),
        "target_p_N_w_g_e_m_D_J_L": (P, N, W, G, ERRORS, M, D, J, L),
        "plain_value_ring": plain_value_ring,
        "deep_low_slide": deep_low_slide_receipt(q26_counterexample),
        "mixed_strong_capacity": mixed_capacity_interface(),
        "exact_fourth_packet": "F3=B*(Y-P-(Z-gamma)*q_H)",
        "pure_Z1_rejected": True,
        "decision": (
            "GREEN_DEEP_HERMITE_SLIDE_F8Q25_F7Q26__"
            "RED_F8Q26__STOP_PLAIN_R"),
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
