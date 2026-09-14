#!/usr/bin/env python3
"""Exact actual-F3 gate for a two-sided covariant/locator syzygy module.

The successful F101 four-normal lift proves that the literal complete source
contains *some* all-node contact-kernel representative of the exact partial
locator packet F3.  Its canonical dense solve, however, gives no mechanism
that could plausibly be formalized at the Full187 target.  This script tests
a small factorized module suggested by the geometry rather than an arbitrary
terminal coefficient.

There are three agreement covariants A0,A1,A2 of contact orders 1,2,3 and
three error covariants E0,E1,E2 of the same orders.  A generator is

  H^(m-1-a) R^(m-a) Xi_E^(m-e)
    * V_H * A0^ay A1^ar A2^as * E0^ey E1^er E2^es,

with negative locator exponents truncated to zero, agreement order
``a=ay+2ar+3as``, and error order ``e=ey+2er+3es``.  Hence every generator
is visibly in the complete contact kernel.  ``V_H`` is the *actual* fourth
packet factor, not an arbitrary terminal C.  The exponent scan retains the
literal active/slope/curvature caps of the successful F101 chamber.

The base generator is ``B*V_H*E0^m``.  It has exactly the F3 linear boundary
because E0 has constant term -1 and m=4.  All other generators are converted
to exact boundary-zero corrections.  We then ask, by exact F_101 rank, if
polynomial X-shifts of those corrections can cancel every source-illegal
coefficient of the base.  A GREEN result is an explicit sparse/factorized
F3 lift; RED falsifies this bounded Popov ansatz, not the full source.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import resource
import sys

sys.path.insert(0, ".experiments")
import f101_o2_projective_four_normal_lift_6900 as P4  # noqa: E402
import f101_o2_xi2_full_kernel_certificate_6900 as C  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402
import prime_o2_conormal_threshold_falsifier as T  # noqa: E402


P = C.PRIME
M = C.M


def centered_blocks(locator, selected, direction):
    """Return order-1/2/3 locator covariants before outer powers."""
    ell = F.sparse_embed_x(locator)
    ell1 = F.sparse_embed_x(F.poly_derivative(locator))
    ell2 = F.sparse_embed_x(F.poly_derivative(locator, 2))

    yc = F.sparse_add(F.Y, F.sparse_embed_x(selected), -1)
    yc = F.sparse_add(
        yc, F.sparse_mul(F.Z, F.sparse_embed_x(direction)), -1)
    rc = F.sparse_add(
        F.R, F.sparse_embed_x(F.poly_derivative(selected)), -1)
    rc = F.sparse_add(
        rc,
        F.sparse_mul(F.Z, F.sparse_embed_x(
            F.poly_derivative(direction))),
        -1,
    )
    sc = F.sparse_add(
        F.S, F.sparse_embed_x(F.poly_derivative(selected, 2)), -1)
    sc = F.sparse_add(
        sc,
        F.sparse_mul(F.Z, F.sparse_embed_x(
            F.poly_derivative(direction, 2))),
        -1,
    )

    a1 = F.sparse_add(
        F.sparse_mul(ell, rc), F.sparse_mul(ell1, yc), -1)
    a2 = F.sparse_mul(F.sparse_pow(ell, 2), sc)
    a2 = F.sparse_add(
        a2, F.sparse_mul(F.sparse_mul(ell, ell1), rc), -2)
    coefficient_y = F.sparse_add(
        F.sparse_scale(2, F.sparse_pow(ell1, 2)),
        F.sparse_mul(ell, ell2),
        -1,
    )
    a2 = F.sparse_add(a2, F.sparse_mul(coefficient_y, yc))
    return yc, a1, a2


def product_of_powers(blocks, exponents):
    out = F.sparse_constant(1)
    for block, exponent in zip(blocks, exponents):
        out = F.sparse_mul(out, F.sparse_pow(block, exponent))
    return out


def polynomial_constant_term(source):
    """Coefficient polynomial of Y^0 R^0 S^0 Z^0."""
    terms = {
        xp: value
        for (xp, y, r, s, z), value in source.items()
        if (y, r, s, z) == (0, 0, 0, 0)
    }
    out = [0] * (max(terms, default=-1) + 1)
    for exponent, value in terms.items():
        out[exponent] = value
    return F.poly_trim(out)


def shift_x(source, amount):
    return {
        (xp + amount, y, r, s, z): value
        for (xp, y, r, s, z), value in source.items()
    }


def shift_seed(source, amount):
    return {
        (xp, y, r, s, z + amount): value
        for (xp, y, r, s, z), value in source.items()
    }


def source_monomial_legal(monomial):
    xp, y, r, s, z = monomial
    return (
        y + r + s <= C.JET
        and r + s <= C.SLOPE
        and s <= C.CURVATURE
        and z + y + r + s <= C.SEED
        and xp + C.W * y + (C.W - 1) * r + (C.W - 2) * s
        < C.DEGREE
    )


def target_safe_103_shape(r, s):
    """Conservative affine-error terminal shape from the target audit."""
    return (
        s <= 8
        and r + s + max(0, 3 * s - 17) <= 16
        and (s <= 6 or r + 4 * s <= 32)
    )


def target_minimal_three_shape_pair_count():
    """Size of the literal target analogue with total R/S exponent <= 1."""
    exponent_triples = tuple(
        (y, r, s)
        for r, s in ((0, 0), (1, 0), (0, 1))
        for y in range(82 - r - s)
        if y + 2 * r + 3 * s <= 60
    )
    pairs = tuple(
        (left, right)
        for left in exponent_triples
        for right in exponent_triples
        if left[1] + left[2] + right[1] + right[2] <= 1
        and 1 + sum(left) + sum(right) <= 82
    )
    assert len(exponent_triples) == 178
    assert len(pairs) == 14_327
    return len(exponent_triples), len(pairs)


def build_module():
    F.GAMMA = 0
    T.PRIME = P
    xi_error, direction = C.xi_and_q()
    locator = F.locator(C.AGREEMENT)
    f3, q_h, lambda_h, lambda_r, _factor = (
        P4.build_partial_locator_row(direction))
    first_three = F.centered_locator_normals(locator, (0,), direction)
    four_boundary_rows = tuple(
        P4.boundary_normal(row) for row in first_three + (f3,))
    four_boundary_determinant = P4.determinant4(four_boundary_rows)
    assert four_boundary_determinant

    agreement_blocks = centered_blocks(locator, (0,), direction)
    # On the three error nodes the received scalar is 1 and the direction is
    # zero.  These blocks are therefore the literal error-side covariants.
    error_blocks = centered_blocks(xi_error, (1,), (0,))
    v_h = F.sparse_add(
        F.Y, F.sparse_mul(F.Z, F.sparse_embed_x(q_h)), -1)
    h = F.sparse_embed_x(lambda_h)
    r = F.sparse_embed_x(lambda_r)
    e = F.sparse_embed_x(xi_error)

    def generator(agreement_exponents, error_exponents):
        agreement_order = sum(
            weight * exponent
            for weight, exponent in zip((1, 2, 3), agreement_exponents))
        error_order = sum(
            weight * exponent
            for weight, exponent in zip((1, 2, 3), error_exponents))
        out = F.sparse_mul(
            F.sparse_pow(h, max(M - 1 - agreement_order, 0)),
            F.sparse_pow(r, max(M - agreement_order, 0)),
        )
        out = F.sparse_mul(
            out, F.sparse_pow(e, max(M - error_order, 0)))
        out = F.sparse_mul(out, v_h)
        out = F.sparse_mul(
            out, product_of_powers(
                agreement_blocks, agreement_exponents))
        out = F.sparse_mul(
            out, product_of_powers(error_blocks, error_exponents))
        return out

    exponent_pairs = []
    for ay in range(C.JET):
        for ar in range(C.SLOPE + 1):
            for ass in range(C.CURVATURE + 1):
                for ey in range(C.JET):
                    for er in range(C.SLOPE + 1):
                        for es in range(C.CURVATURE + 1):
                            aa = (ay, ar, ass)
                            ee = (ey, er, es)
                            if ar + ass + er + es > C.SLOPE:
                                continue
                            if ass + es > C.CURVATURE:
                                continue
                            if 1 + sum(aa) + sum(ee) > C.JET:
                                continue
                            if ay + 2 * ar + 3 * ass > M:
                                continue
                            if ey + 2 * er + 3 * es > M:
                                continue
                            exponent_pairs.append((aa, ee))

    base_key = ((0, 0, 0), (M, 0, 0))
    assert base_key in exponent_pairs
    base = generator(*base_key)
    assert P4.boundary_normal(base) == P4.boundary_normal(f3)

    u0 = tuple(0 if node in C.AGREEMENT else 1
               for node in range(C.N))
    u1 = tuple(C.poly_eval(direction, node) for node in range(C.N))
    assert not F.contact_image(base, u0, u1)

    corrections = []
    labels = []
    contact_checks = 1
    for aa, ee in exponent_pairs:
        if (aa, ee) == base_key:
            continue
        candidate = generator(aa, ee)
        assert not F.contact_image(candidate, u0, u1)
        contact_checks += 1

        if aa == (0, 0, 0):
            # Only the error covariants can have scalar constants.  Divide
            # the candidate Y-boundary by the base Y-boundary, then subtract
            # that exact polynomial multiple of the base.
            numerator = P4.boundary_normal(candidate)[0]
            denominator = P4.boundary_normal(base)[0]
            quotient, remainder = P4.B.polynomial_divmod(
                numerator, denominator)
            assert not remainder
            candidate = F.sparse_add(
                candidate,
                F.sparse_mul(F.sparse_embed_x(quotient), base),
                -1,
            )

        assert all(not row for row in P4.boundary_normal(candidate))
        if candidate:
            corrections.append(candidate)
            labels.append((aa, ee))

    return {
        "f3": f3,
        "base": base,
        "corrections": tuple(corrections),
        "labels": tuple(labels),
        "u0": u0,
        "u1": u1,
        "contact_checks": contact_checks,
        "exponent_pair_count": len(exponent_pairs),
        "q_h": q_h,
        "direction": direction,
        "locator": locator,
        "xi_error": xi_error,
        "four_boundary_determinant": four_boundary_determinant,
    }


def solve_illegal_tail(module, max_shift, max_seed_shift):
    seed_shifted = []
    seed_labels = []
    for amount in range(max_seed_shift + 1):
        for label, correction in zip(
                module["labels"], module["corrections"]):
            seed_shifted.append(shift_seed(correction, amount))
            seed_labels.append((amount, label))
    # Positive seed multiples of the normalized base have zero linear
    # boundary and are essential: the successful dense lift uses the whole
    # passive staircase, whereas a K[X]-module alone cannot propagate it.
    for amount in range(1, max_seed_shift + 1):
        seed_shifted.append(shift_seed(module["base"], amount))
        seed_labels.append((amount, "base"))

    shifted = []
    shifted_labels = []
    for amount in range(max_shift + 1):
        for label, correction in zip(seed_labels, seed_shifted):
            shifted.append(shift_x(correction, amount))
            shifted_labels.append((amount, label))

    illegal_rows = tuple(sorted({
        monomial
        for source in (module["base"], *shifted)
        for monomial in source
        if not source_monomial_legal(monomial)
    }))
    row_index = {row: index for index, row in enumerate(illegal_rows)}
    columns = [
        {row_index[row]: value for row, value in source.items()
         if row in row_index}
        for source in shifted
    ]
    # Last column is -base, so a null relation with nonzero last coordinate
    # is exactly a correction cancelling the entire illegal tail.
    columns.append({
        row_index[row]: (-value) % P
        for row, value in module["base"].items()
        if row in row_index
    })
    matrix = T.dense_matrix(columns)
    rank = matrix.rank()
    nullspace, nullity = matrix.nullspace()
    last = len(shifted)
    relation = next(
        (column for column in range(nullity)
         if int(nullspace[last, column]) % P),
        None,
    )

    result = {
        "max_polynomial_X_shift": max_shift,
        "max_passive_seed_shift": max_seed_shift,
        "boundary_zero_generator_count": len(module["corrections"]),
        "seed_shifted_generator_count": len(seed_shifted),
        "shifted_correction_columns": len(shifted),
        "illegal_coefficient_rows": len(illegal_rows),
        "correction_rank": rank if relation is None else None,
        "augmented_rank": rank,
        "augmented_nullity": nullity,
        "solvable": relation is not None,
    }
    if relation is None:
        # Since the augmented matrix has one more column than the correction
        # matrix in every recorded RED run, report both exact ranks.
        correction_matrix = T.dense_matrix(columns[:-1])
        result["correction_rank"] = correction_matrix.rank()
        result["augmented_rank"] = rank
        result["rank_gain_of_actual_F3_illegal_tail"] = (
            rank - result["correction_rank"])
        return result

    scale = pow(int(nullspace[last, relation]) % P, -1, P)
    representative = dict(module["base"])
    used = []
    for row, source in enumerate(shifted):
        # nullspace gives sum c_i*correction_i - c_last*base = 0;
        # therefore base is killed by adding -c_i/c_last corrections.
        coefficient = -int(nullspace[row, relation]) * scale % P
        if coefficient:
            representative = F.sparse_add(
                representative, source, coefficient)
            used.append((shifted_labels[row], coefficient))
    assert all(source_monomial_legal(row) for row in representative)
    contact_image = F.contact_image(
        representative, module["u0"], module["u1"])
    assert not contact_image
    boundary = P4.boundary_normal(representative)
    assert boundary == P4.boundary_normal(module["f3"])
    derivative_shapes = tuple(sorted({
        (r, s) for _xp, _y, r, s, _z in representative
    }))
    target_deleted_face_terms = tuple(
        monomial for monomial in representative
        if monomial[1] + monomial[2] + monomial[3] == C.JET
        and sum(monomial[1:]) == C.SEED
        and not target_safe_103_shape(monomial[2], monomial[3])
    )
    x_shifts = tuple(label[0] for label, _coefficient in used)
    seed_shifts = tuple(label[1][0] for label, _coefficient in used)
    factor_labels = tuple(
        label[1][1] for label, _coefficient in used
        if label[1][1] != "base"
    )
    unique_factor_labels = set(factor_labels)
    result.update({
        "correction_rank": rank,
        "representative_support": len(representative),
        "representative_nonzero_contact_rows": len(contact_image),
        "representative_boundary_polynomial_degrees": tuple(
            len(row) - 1 for row in boundary),
        "used_shifted_generators": len(used),
        "representative_sha256": P4.B.source_hash(representative),
        "used_X_shift_min_max": (min(x_shifts), max(x_shifts)),
        "used_seed_shift_min_max": (
            min(seed_shifts), max(seed_shifts)),
        "used_distinct_covariant_factor_pairs": len(unique_factor_labels),
        "used_agreement_y_min_max": (
            min(label[0][0] for label in unique_factor_labels),
            max(label[0][0] for label in unique_factor_labels)),
        "used_error_y_min_max": (
            min(label[1][0] for label in unique_factor_labels),
            max(label[1][0] for label in unique_factor_labels)),
        "representative_derivative_shapes": derivative_shapes,
        "target_safe103_deleted_face_term_count": len(
            target_deleted_face_terms),
    })
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-shift", type=int, default=7)
    parser.add_argument("--max-seed-shift", type=int, default=7)
    args = parser.parse_args()
    if args.max_shift < 0 or args.max_seed_shift < 0:
        raise SystemExit("shift bounds must be nonnegative")

    module = build_module()
    gate = solve_illegal_tail(
        module, args.max_shift, args.max_seed_shift)
    stable = {
        "scope": (
            "exact F101 actual-F3 two-sided covariant Popov ansatz; "
            "not an arbitrary terminal C, target theorem, or full-source "
            "falsifier"
        ),
        "field_and_parameters_n_w_g_m_D_s_t_J_L": (P, *C.CASE),
        "actual_packet": "F3=B*(Y-Z*q_H)",
        "q_H_coefficients": module["q_h"],
        "agreement_direction_coefficients": module["direction"],
        "all_factorized_generators_complete_contact_zero": True,
        "factorized_generator_contact_checks": module["contact_checks"],
        "literal_exponent_pairs": module["exponent_pair_count"],
        "base_boundary_equals_actual_F3": True,
        "four_packet_boundary_determinant_nonzero_degree": (
            len(module["four_boundary_determinant"]) - 1),
        "base_support_and_illegal_terms": (
            len(module["base"]),
            sum(not source_monomial_legal(row) for row in module["base"]),
        ),
        "target_scaling_ledger": {
            "target_m_J_slope_curvature_L": (60, 82, 21, 10, 2703),
            "minimal_three_shape_exponent_triples_and_factor_pairs":
                target_minimal_three_shape_pair_count(),
            "same_7_by_7_shift_rectangle_columns_upper_bound":
                14_327 * 8 * 8,
            "all_three_derivative_shapes_in_safe103": all(
                target_safe_103_shape(r, s)
                for r, s in ((0, 0), (1, 0), (0, 1))),
            "raw_generators_individually_source_legal": False,
            "certification_needed": (
                "shifted bivariate Popov/module membership showing the "
                "combined representative, not each raw generator, lies in "
                "every literal Full187 X/active/passive window"),
        },
        "gate": gate,
        "decision": (
            "GREEN_SPARSE_FACTOR_MODULE_LIFTS_ACTUAL_F3"
            if gate["solvable"] else
            "RED_BOUNDED_TWO_SIDED_COVARIANT_POPOV_ANSATZ"
        ),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    print(json.dumps({
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
