#!/usr/bin/env python3
"""Exact symbolic interface for the Full187 charge-13 physical streams.

This is a target-parameter operator specification, not a rank experiment.
It derives the positive-Hasse collisions in the 33 advertised principal
rows, records the complete raw contact-entry formula, and emits the exact
transpose equations.  It intentionally refuses to quotient prior rows:
the repository does not yet provide a concrete global correction linear map
with all contact and boundary tails.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
import hashlib
import json
import math
from pathlib import Path
import resource


P = 2_130_706_433
N = 262_144
G = 180_413
ERRORS = N - G
W = 131_071
M = 60
D = M * G
ACTIVE_CAP = 82
SLOPE_CAP = 21
CURVATURE_CAP = 10
SEED_CAP = 2703
BASE_WIDTH = 76_979
SOURCE_Y = 61
SOURCE_Z = 2621


@dataclass(frozen=True, order=True)
class Row:
    t: int
    e: int
    r: int
    s: int
    z: int


@dataclass(frozen=True, order=True)
class Provenance:
    source_s: int
    f: int
    a_e: int
    c_s: int
    q: int


PRINCIPAL = {
    "A": {"f": 7, "a_e": 6, "c_s": 1, "u1_power": 54},
    "B": {"f": 8, "a_e": 5, "c_s": 3, "u1_power": 53},
    "C": {"f": 8, "a_e": 6, "c_s": 1, "u1_power": 53},
}

# Relative to the q=0/c_s-maximal coefficient in each named row.  H_j is
# the j-th Hasse derivative, not the j-th compositional power of H_1.
HASSE_BANDS = {
    "A": ((0, 1), (1, -2)),
    "B": ((0, 1), (1, -6), (2, 12), (3, -8)),
    "C": ((0, 1), (1, -1)),
}


def compose_hasse_bands(left, right, maximum_shift=10):
    """Compose shifted Hasse bands.

    If `L_s=sum_j left[j] H_j(c_(s+j))` and similarly for `right`,
    then `H_j o H_k = binom(j+k,j) H_(j+k)`.
    """
    left = dict(left)
    right = dict(right)
    return tuple(
        sum(
            left.get(j, 0) * right.get(n - j, 0) * math.comb(n, j)
            for j in range(n + 1)
        )
        for n in range(maximum_shift + 1)
    )


def a_inverse_band():
    # Recursion: c_10=a_10 and c_s=a_s+2 H_1(c_(s+1)).
    return tuple((j, 2**j * math.factorial(j)) for j in range(11))


def source_width(s: int) -> int:
    assert 0 <= s <= CURVATURE_CAP
    # Origin (y,r,s,z)=(61,21-s,s,2621).
    answer = D - W * SOURCE_Y - (W - 1) * (SLOPE_CAP - s) - (W - 2) * s
    assert answer == BASE_WIDTH + s
    return answer


def contact_scalar(f: int, a_e: int, c_s: int) -> int:
    """Scalar excluding Hasse(c), u0, and u1."""
    residual_r = f - a_e - c_s
    assert min(a_e, c_s, residual_r) >= 0
    multinomial = (
        math.factorial(f)
        // (math.factorial(a_e) * math.factorial(c_s)
            * math.factorial(residual_r))
    )
    inv_two = pow(2, -1, P)
    return (
        math.comb(SOURCE_Y, f)
        * multinomial
        * pow(-inv_two, c_s, P)
    ) % P


def row_of(source_s: int, f: int, h: int,
           a_e: int, c_s: int, q: int) -> Row:
    source_r = SLOPE_CAP - source_s
    return Row(
        q + f - a_e + c_s,
        a_e,
        f - a_e - c_s + source_r,
        source_s + c_s,
        SOURCE_Z + h,
    )


def principal_row(name: str, output_s: int) -> Row:
    data = PRINCIPAL[name]
    return row_of(
        output_s, data["f"], data["u1_power"],
        data["a_e"], data["c_s"], 0,
    )


def expected_principal_provenance(name: str, output_s: int):
    data = PRINCIPAL[name]
    return tuple(
        Provenance(
            source_s=output_s + j,
            f=data["f"],
            a_e=data["a_e"],
            c_s=data["c_s"] - j,
            q=j,
        )
        for j, _coefficient in HASSE_BANDS[name]
        if output_s + j <= CURVATURE_CAP
    )


def enumerate_aggregated_contact_schema():
    """Stream all syntactic choices without expanding their h intervals.

    A base `(T,E,R,S)` has every Z from 2621 through `2621+max_h`.
    This suffices to count exact distinct raw row shapes while avoiding the
    48.5 million fully expanded provenance records.
    """
    desired_rows = {
        principal_row(name, s)
        for name in PRINCIPAL for s in range(CURVATURE_CAP + 1)
    }
    provenance = defaultdict(list)
    max_h_by_base = {}
    top_rows = set()
    counts = Counter()

    for source_s in range(CURVATURE_CAP + 1):
        for f in range(SOURCE_Y + 1):
            for a_e in range(f + 1):
                for c_s in range(f - a_e + 1):
                    contact_weight_without_q = f + 2 * a_e + c_s
                    for q in range(max(0, M - contact_weight_without_q)):
                        top_h = SOURCE_Y - f
                        top_row = row_of(source_s, f, top_h, a_e, c_s, q)
                        base = (top_row.t, top_row.e, top_row.r, top_row.s)
                        max_h_by_base[base] = max(
                            max_h_by_base.get(base, -1), top_h)
                        top_rows.add(top_row)

                        is_principal_q0 = any(
                            q == 0
                            and (f, a_e, c_s) == (
                                data["f"], data["a_e"], data["c_s"])
                            for data in PRINCIPAL.values()
                        )
                        counts[
                            "top_principal_q0" if is_principal_q0
                            else "top_other_provenance"
                        ] += 1
                        counts["lower_grade_provenance"] += top_h
                        if q > 0:
                            counts["top_positive_hasse"] += 1
                            counts["lower_positive_hasse"] += top_h
                        if q == 0 and 2 * a_e + c_s > 13:
                            counts["top_q0_extra_charge_gt13"] += 1
                            counts["lower_q0_extra_charge_gt13"] += top_h
                        if q == 0 and 2 * a_e + c_s < 13:
                            counts["top_q0_extra_charge_lt13"] += 1
                            counts["lower_q0_extra_charge_lt13"] += top_h

                        if top_row in desired_rows:
                            provenance[top_row].append(Provenance(
                                source_s, f, a_e, c_s, q))

    all_row_shapes = sum(max_h + 1 for max_h in max_h_by_base.values())
    total_provenance = (
        counts["top_principal_q0"]
        + counts["top_other_provenance"]
        + counts["lower_grade_provenance"]
    )
    assert counts == Counter({
        "lower_grade_provenance": 47_315_598,
        "lower_positive_hasse": 44_792_363,
        "lower_q0_extra_charge_gt13": 1_623_259,
        "top_other_provenance": 1_200_892,
        "top_positive_hasse": 1_126_400,
        "lower_q0_extra_charge_lt13": 805_805,
        "top_q0_extra_charge_gt13": 46_805,
        "top_q0_extra_charge_lt13": 24_871,
        "top_principal_q0": 33,
    })
    assert total_provenance == 48_516_523
    assert len(max_h_by_base) == len(top_rows) == 241_475
    assert all_row_shapes == 10_011_293

    expected = {
        principal_row(name, s): expected_principal_provenance(name, s)
        for name in PRINCIPAL for s in range(CURVATURE_CAP + 1)
    }
    assert set(provenance) == set(expected)
    assert all(tuple(provenance[row]) == expected[row] for row in expected)
    total_principal_row_provenance = sum(map(len, provenance.values()))
    assert total_principal_row_provenance == 80
    assert total_principal_row_provenance - counts["top_principal_q0"] == 47

    # Check every relative coefficient in the three differential bands.
    principal_scalars = {}
    for name, data in PRINCIPAL.items():
        kappa = contact_scalar(data["f"], data["a_e"], data["c_s"])
        principal_scalars[name] = kappa
        for j, relative in HASSE_BANDS[name]:
            actual = contact_scalar(
                data["f"], data["a_e"], data["c_s"] - j)
            assert actual == kappa * relative % P
    assert principal_scalars == {
        "A": 603_758_703,
        "B": 693_269_975,
        "C": 642_373_467,
    }
    assert principal_scalars["C"] == 54 * principal_scalars["A"] % P
    assert principal_scalars["B"] == (
        principal_scalars["C"] * pow(4, -1, P) % P)

    provenance_payload = tuple(
        (
            name,
            s,
            tuple(asdict(p) for p in expected_principal_provenance(name, s)),
        )
        for s in range(CURVATURE_CAP + 1)
        for name in PRINCIPAL
    )
    multiplicities = Counter(
        len(expected_principal_provenance(name, s))
        for s in range(CURVATURE_CAP + 1)
        for name in PRINCIPAL
    )
    assert dict(multiplicities) == {2: 21, 4: 8, 3: 1, 1: 3}
    return {
        "fully_expanded_provenance_counts": dict(sorted(counts.items())),
        "fully_expanded_provenance_total": total_provenance,
        "distinct_top_row_shapes_per_node": len(top_rows),
        "distinct_all_grade_row_shapes_per_node": all_row_shapes,
        "top_row_coordinates_over_target_domain": len(top_rows) * N,
        "all_grade_row_coordinates_over_target_domain": all_row_shapes * N,
        "principal_physical_row_shapes_per_node": len(desired_rows),
        "principal_q0_and_colliding_positive_hasse_provenance": (
            counts["top_principal_q0"], 47, total_principal_row_provenance),
        "principal_row_provenance_pattern": (
            "family at output s receives (source_s,cS,q)=(s+j,cS0-j,j) "
            "for the listed Hasse-band j while s+j<=10"
        ),
        "principal_row_provenance_multiplicity_histogram": dict(
            sorted(multiplicities.items())),
        "principal_row_provenance_sha256": hashlib.sha256(
            repr(provenance_payload).encode()).hexdigest(),
        "principal_scalars_mod_p": principal_scalars,
    }


def principal_operator_spec():
    widths = tuple(source_width(s) for s in range(CURVATURE_CAP + 1))
    source_dimension = sum(widths)
    assert source_dimension == 846_824
    for name, band in HASSE_BANDS.items():
        for s in range(CURVATURE_CAP + 1):
            for j, _relative in band:
                if s + j <= CURVATURE_CAP:
                    # Hasse_j maps deg < width(s+j) to deg < width(s).
                    assert source_width(s + j) - j == source_width(s)

    formulas = {
        "A": "kA*u1(x)^54*(c_s-2*Hasse_1(c_(s+1)))(x)",
        "B": (
            "kB*u1(x)^53*(c_s-6*Hasse_1(c_(s+1))"
            "+12*Hasse_2(c_(s+2))-8*Hasse_3(c_(s+3)))(x)"
        ),
        "C": "kC*u1(x)^53*(c_s-Hasse_1(c_(s+1)))(x)",
    }
    inverse = a_inverse_band()
    a_band = HASSE_BANDS["A"]
    a_after_inverse = compose_hasse_bands(a_band, inverse)
    inverse_after_a = compose_hasse_bands(inverse, a_band)
    assert a_after_inverse == inverse_after_a == (1,) + (0,) * 10
    b_after_a_inverse = compose_hasse_bands(
        HASSE_BANDS["B"], inverse)
    c_after_a_inverse = compose_hasse_bands(
        HASSE_BANDS["C"], inverse)

    return {
        "source_module": (
            "direct_sum_s=0^10 K[X]_<76979+s",
            widths,
            source_dimension,
        ),
        "principal_polynomial_modules_before_node_evaluation": (
            "three correlated copies of the same tapered module",
            3 * source_dimension,
        ),
        "principal_node_row_module": (
            "K^(Domain x {A,B,C} x Fin11)",
            N * 33,
        ),
        "hasse_bands_relative_to_principal_scalar": HASSE_BANDS,
        "node_formulas_missing_indices_are_zero": formulas,
        "each_polynomial_band_is_square_upper_unitriangular": True,
        "A_inverse": {
            "recursive": (
                "c_10=a_10; c_s=a_s+2*Hasse_1(c_(s+1))"
            ),
            "closed_band_coefficients_2powj_times_jfactorial": inverse,
            "left_and_right_composition_coefficients": a_after_inverse,
            "Hasse_composition_rule": (
                "Hasse_j o Hasse_k = binom(j+k,j)*Hasse_(j+k)"
            ),
        },
        "principal_quotient": {
            "compatibility_residues": (
                "I_B=b-T_B*T_A^{-1}(a)",
                "I_C=c-T_C*T_A^{-1}(a)",
            ),
            "T_B_after_T_A_inverse_band": b_after_a_inverse,
            "T_C_after_T_A_inverse_band": c_after_a_inverse,
            "exact_sequence": (
                "0 -> S13 --(T_A,T_B,T_C)--> S13^3 "
                "--(I_B,I_C)--> S13^2 -> 0"
            ),
            "kernel_equals_physical_image": True,
            "quotient_map_surjective_via": "(b,c) maps from (0,b,c)",
            "cokernel_dimension_before_other_tails": 2 * source_dimension,
        },
        "warning": (
            "The three outputs are correlated images of one 846824-dimensional "
            "source, not 2540472 independently selectable coefficients. "
            "Node multiplication by u1^53/u1^54 must not be inverted in a "
            "uniform received-word theorem."
        ),
    }


def transpose_equation_spec():
    """Emit the exact principal and complete transpose equations."""
    principal_terms_for_source_t = {}
    kappas = {
        name: contact_scalar(data["f"], data["a_e"], data["c_s"])
        for name, data in PRINCIPAL.items()
    }
    for source_t in range(CURVATURE_CAP + 1):
        terms = []
        for name, band in HASSE_BANDS.items():
            for j, relative in band:
                output_s = source_t - j
                if output_s < 0:
                    continue
                terms.append({
                    "dual_row_family": name,
                    "dual_row_s": output_s,
                    "hasse_order_on_X^a": j,
                    "field_scalar": kappas[name] * relative % P,
                    "u1_power": PRINCIPAL[name]["u1_power"],
                    "basis_evaluation_factor": "binom(a,j)*x^(a-j)",
                })
        principal_terms_for_source_t[source_t] = tuple(terms)

    terms_payload = tuple(
        (source_t, tuple(
            tuple(sorted(term.items()))
            for term in principal_terms_for_source_t[source_t]
        ))
        for source_t in principal_terms_for_source_t
    )
    return {
        "principal_equation_quantifiers": (
            "for every source t=0..10 and every a=0..76978+t"
        ),
        "principal_equation": (
            "sum_(x in Domain) sum_(listed terms) "
            "fieldScalar*u1(x)^u1Power*lambda[family,s,x]"
            "*binom(a,j)*x^(a-j) = 0"
        ),
        "terms_by_source_t_pattern": (
            "source t contributes through band j to dual row (family,t-j), "
            "for every listed family band with 0<=j<=t"
        ),
        "terms_by_source_t_sha256": hashlib.sha256(
            repr(terms_payload).encode()).hexdigest(),
        "principal_adjoint_equation": (
            "T_A^*(alpha)+T_B^*(beta)+T_C^*(gamma)=0; equivalently "
            "alpha=-(T_A^{-1})^*(T_B^*(beta)+T_C^*(gamma)). "
            "Thus the formal principal annihilator is parametrized by two "
            "tapered dual streams before node weights and other tails."
        ),
        "complete_raw_stream_equation": (
            "For each t,a, sum over x,f,h,aE,cS,q with "
            "q+f+2aE+cS<60 of lambda[x,row(t,f,h,aE,cS,q)] * "
            "binom(61,f)*binom(61-f,h)*multinomial(f;aE,cS,*)*"
            "(-1/2)^cS*u0(x)^(61-f-h)*u1(x)^h*"
            "binom(a,q)*x^(a-q) = 0."
        ),
        "augmented_packet_dual_test": (
            "A RED certificate is (lambda,mu) satisfying the complete raw "
            "stream equations and every prior-source transpose equation, "
            "with <lambda,contact(F_i)>+<mu,boundary(F_i)> != 0 for a named "
            "current packet F_i. GREEN requires this pairing to vanish for "
            "every such annihilator, equivalently literal range containment."
        ),
    }


def main():
    schema = enumerate_aggregated_contact_schema()
    operator = principal_operator_spec()
    transpose = transpose_equation_spec()
    stable = {
        "scope": (
            "Full187 target-parameter symbolic sparse operator interface; "
            "no small-field grid, no localization, no production edit"
        ),
        "parameters_p_N_g_e_w_m_D_J_q_t_L": (
            P, N, G, ERRORS, W, M, D, ACTIVE_CAP,
            SLOPE_CAP, CURVATURE_CAP, SEED_CAP,
        ),
        "physical_origin": "c_s(X) Y^61 R^(21-s) S^s Z^2621",
        "principal_operator": operator,
        "contact_schema": schema,
        "transpose_verification": transpose,
        "current_packet_names": (
            "F0", "F1", "F2", "F3_partial_locator"
        ),
        "stale_interface_rejected": (
            "F0", "F1", "F2", "pure_constant_Z1"
        ),
        "missing_for_reduced_charge13_schur_operator": (
            "a concrete global prior-source contact map C0",
            "a concrete global prior-source boundary map beta0",
            "a linear correction section with C0(correction(v))=-lower(v)",
            "the complete contact/boundary columns of current F3 in the same keys",
            "an exact support/orientation theorem for every sharp-pivot remainder",
        ),
        "tails_that_must_remain_live": (
            "all 47 positive-Hasse collisions folded into the 33 principal rows",
            "the remaining 1200845 top-grade provenance terms outside those 80 heads",
            "all 47315598 lower-grade provenance terms from the eleven streams",
            "the concrete lower-prefix contact and boundary maps C0 and beta0",
            "every higher-contact remainder generated by a sharp Order2 pivot",
            "the contact and boundary effect of each mixed-CRT correction choice",
            "all agreement and error node coordinates, with u0/u1 weights intact",
        ),
        "isolated_block_limitation": (
            "Commit bd2f679 proves the eleven-stream block raw-injective in "
            "the fixed Xi_E^2 target instance. Any kernel class must therefore "
            "use cross-origin or multi-grade cancellation and carry the B/C tails."
        ),
        "decision": "GREEN_RAW_PRINCIPAL_SPEC__STOP_REDUCED_SCHUR_UNDEFINED",
        "scope_guard": (
            "All 10011293 raw contact row shapes per node remain live unless "
            "one of the missing global transpose/correction maps proves an "
            "exact quotient. The 33 principal rows alone are not a subcomplex."
        ),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    stable["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    stable["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    stable["peak_rss_kib"] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    print(json.dumps(stable, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
