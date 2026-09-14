#!/usr/bin/env python3
"""Exact Hermite-budget profile for the Full187 terminal contact shell.

Contact truncation makes every surviving grade-82 term land at active degree
at most 80, so its lower source coefficient window exceeds the number of
nodes.  Full contact cancellation, however, can require more than values: a
term of contact weight ``k`` may require a residue modulo ``Lambda_G^(60-k)``,
of degree ``g*(60-k)``.  This script classifies exactly which terminal
contact choices can carry that agreement-side Hermite factor.  This alone is
not arbitrary error-node interpolation: prescribing one scalar value at each
of the ``N-G`` error nodes needs a further ``N-G`` coefficient slots.

A negative margin is an unresolved structured-residue case, not an
impossibility certificate: the actual residue comes from a low-degree top
coefficient multiplied by a power of the received direction and need not be
arbitrary modulo the locator power.
"""

from __future__ import annotations

from collections import Counter
import hashlib
import json
from pathlib import Path
import sys


N = 262_144
W = 131_071
G = 180_413
ERRORS = N - G
M = 60
D = M * G
J = 82
SLOPE = 21
CURVATURE = 10


def coefficient_width(y: int, r: int, s: int) -> int:
    return D - W * y - (W - 1) * r - (W - 2) * s


def ceil_div(a: int, b: int) -> int:
    return (a + b - 1) // b


def main() -> None:
    derivative_shapes = tuple(
        (r, s)
        for s in range(CURVATURE + 1)
        for r in range(SLOPE - s + 1)
    )
    assert len(derivative_shapes) == 187

    rows = []
    total_contact_choices = 0
    unconditional_choices = 0
    scalar_crt_choices = 0
    agreement_only_choices = 0
    unresolved_choices = 0
    global_min_margin = None
    global_min_data = None
    threshold_histogram = Counter()
    unresolved_by_extra_contact_charge = Counter()
    unresolved_by_contact_weight = Counter()
    unresolved_transition_types = set()

    for r, s in derivative_shapes:
        y = J - r - s
        assert 61 <= y <= 82
        top_width = coefficient_width(y, r, s)
        assert top_width == D - W * J + r + 2 * s
        assert N < coefficient_width(59, r, s)

        # The hardest contact choice at fixed f is aE=cS=0.  Its Hermite
        # margin is f*(g-w) minus the derivative-shape charge.
        derivative_charge = (W - 1) * r + (W - 2) * s
        threshold = ceil_div(derivative_charge, G - W)
        assert 0 <= threshold <= 56
        threshold_histogram[threshold] += 1

        shape_total = 0
        shape_green = 0
        shape_red = 0
        shape_min_margin = None
        shape_min_tuple = None
        for f in range(M):
            h = y - f
            assert h >= 2
            lower_width = coefficient_width(f, r, s)
            assert lower_width > N
            for a_e in range(f + 1):
                for c_s in range(f - a_e + 1):
                    contact_weight = f + 2 * a_e + c_s
                    if contact_weight >= M:
                        continue
                    hermite_depth = M - contact_weight
                    modulus_degree = G * hermite_depth
                    margin = lower_width - modulus_degree
                    datum = (f, a_e, c_s, h, margin)
                    shape_total += 1
                    total_contact_choices += 1
                    if margin >= 0:
                        shape_green += 1
                        unconditional_choices += 1
                        if margin >= ERRORS:
                            scalar_crt_choices += 1
                        else:
                            agreement_only_choices += 1
                    else:
                        shape_red += 1
                        unresolved_choices += 1
                        extra_charge = 2 * a_e + c_s
                        unresolved_by_extra_contact_charge[extra_charge] += 1
                        unresolved_by_contact_weight[contact_weight] += 1
                        unresolved_transition_types.add((f, a_e, c_s))
                    if shape_min_margin is None or margin < shape_min_margin:
                        shape_min_margin = margin
                        shape_min_tuple = datum
                    if global_min_margin is None or margin < global_min_margin:
                        global_min_margin = margin
                        global_min_data = (r, s) + datum

        # Exactly f >= threshold makes the worst aE=cS=0 choice fit.  All
        # higher-weight choices at the same f have smaller Hermite depth.
        for f in range(M):
            worst_margin = coefficient_width(f, r, s) - G * (M - f)
            assert (worst_margin >= 0) == (f >= threshold)
        rows.append({
            "derivative_shape_r_s": (r, s),
            "terminal_y": y,
            "top_coefficient_width": top_width,
            "worst_choice_first_agreement_factor_f": threshold,
            "contact_choice_count": shape_total,
            "agreement_Hermite_factor_choices": shape_green,
            "structured_residue_choices": shape_red,
            "minimum_margin_at_f_aE_cS_h_margin": shape_min_tuple,
        })

    assert total_contact_choices == unconditional_choices + unresolved_choices
    assert unconditional_choices == scalar_crt_choices + agreement_only_choices
    assert global_min_data == (21, 0, 0, 0, 0, 61, -2_752_470)
    assert coefficient_width(59, 21, 0) == 339_121
    assert coefficient_width(59, 21, 0) - N == 76_977
    assert total_contact_choices == 1_266_925
    assert unconditional_choices == 1_194_075
    assert scalar_crt_choices == 1_186_372
    assert agreement_only_choices == 7_703
    assert unresolved_choices == 72_850
    assert len(unresolved_transition_types) == 1_056
    assert max(unresolved_by_extra_contact_charge) == 13
    # Extra charge at least fourteen requires at least seven active H factors.
    # Those two refunds together exceed the maximum derivative-shape charge.
    assert 7 * (G - W) + 14 * G > (W - 1) * SLOPE

    product_frontier = []
    for r, s in derivative_shapes:
        y = J - r - s
        if y - 59 != 2:
            continue
        assert r + s == SLOPE
        top_width = coefficient_width(y, r, s)
        predecessor_width = coefficient_width(59, r, s)
        maximum_product_degree = (top_width - 1) + (N - 1)
        assert predecessor_width == top_width + 2 * W
        assert maximum_product_degree == predecessor_width
        product_frontier.append({
            "shape_y_r_s": (y, r, s),
            "surviving_f_h_aE_cS": (59, 2, 0, 0),
            "top_width": top_width,
            "predecessor_width": predecessor_width,
            "maximum_generic_product_degree": maximum_product_degree,
            "strict_width_overrun_degrees": 1,
            "contact_weight_and_Hermite_depth": (59, 1),
            "reduced_mod_all_node_locator_fits": True,
        })
    assert len(product_frontier) == 11
    assert tuple(row["shape_y_r_s"] for row in product_frontier) == tuple(
        (61, 21 - s, s) for s in range(11))
    # For h>=3 the minimum legal-degree slack is already 131070.
    assert 3 * W - N + 1 == 131_070

    payload = {
        "scope": (
            "exact integer Hermite-capacity classification of all surviving "
            "contact choices from the Full187 active-grade-82 shell; a "
            "negative margin means structured recurrence remains, not that "
            "the target lift is impossible"
        ),
        "target_n_w_g_m_D_J_slope_curvature":
            (N, W, G, M, D, J, SLOPE, CURVATURE),
        "derivative_shape_count": len(derivative_shapes),
        "terminal_top_width_interval": (
            min(row["top_coefficient_width"] for row in rows),
            max(row["top_coefficient_width"] for row in rows)),
        "first_agreement_factor_f_histogram": tuple(sorted(
            threshold_histogram.items())),
        "contact_choice_counts": {
            "total": total_contact_choices,
            "agreement_Hermite_factor_fits": unconditional_choices,
            "agreement_factor_plus_arbitrary_error_scalar_CRT_fits":
                scalar_crt_choices,
            "agreement_factor_fits_but_arbitrary_error_scalar_CRT_does_not":
                agreement_only_choices,
            "structured_residue_recurrence_needed": unresolved_choices,
        },
        "structured_frontier": {
            "unique_f_aE_cS_transition_types":
                len(unresolved_transition_types),
            "maximum_extra_contact_charge_2aE_plus_cS":
                max(unresolved_by_extra_contact_charge),
            "counts_by_extra_contact_charge": tuple(sorted(
                unresolved_by_extra_contact_charge.items())),
            "counts_by_total_contact_weight": tuple(sorted(
                unresolved_by_contact_weight.items())),
            "all_extra_charge_at_least_14_agreement_factor_fits": True,
        },
        "generic_node_interpolant_product_frontier": {
            "automatic_for_seed_shift_h_at_least_3": True,
            "minimum_legal_degree_slack_when_h_is_3": 3 * W - N + 1,
            "only_h_equals_2_shapes": tuple(product_frontier),
            "shape_count": len(product_frontier),
            "interpretation": (
                "For these eleven and only these eleven terminal shapes, "
                "multiplying maximally wide top data by a worst-degree "
                "all-node interpolant reaches the predecessor cutoff exactly "
                "and is source-illegal by one leading coefficient.  This "
                "stops only the unreduced-product ansatz: contact weight 59 "
                "has Hermite depth one, so reducing its node-value data "
                "modulo the all-node locator gives degree below n and fits "
                "the predecessor window.  It is not a linear transition "
                "obstruction."
            ),
        },
        "global_minimum_margin_at_r_s_f_aE_cS_h_margin": global_min_data,
        "all_surviving_lower_windows_exceed_all_node_value_budget": True,
        "worst_all_node_value_width_receipt": {
            "shape_r_s_f": (21, 0, 59),
            "width": coefficient_width(59, 21, 0),
            "width_minus_n": coefficient_width(59, 21, 0) - N,
        },
        "per_derivative_shape": tuple(rows),
        "interpretation": (
            "The 1,194,075 count certifies only that the agreement-locator "
            "Hermite factor fits.  Of those, 1,186,372 also leave enough "
            "room for arbitrary scalar data on every error node; even that "
            "is a capacity gate, not a confluence or THREE-RHS theorem.  "
            "Low-f terms can exceed the agreement-side budget and must be "
            "carried as structured residues through the exact transpose/"
            "confluence recurrence; they are not certified obstructions."
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(
        canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    if "--compact" in sys.argv:
        compact = {key: value for key, value in payload.items()
                   if key != "per_derivative_shape"}
        print(json.dumps(compact, indent=2, sort_keys=True))
    else:
        print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
