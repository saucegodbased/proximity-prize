#!/usr/bin/env python3
"""Extract literal R^2 kernel relations and formal boundary normals.

The corrected flattened-contact F_101 m6,L8 control is ordered as

    raw, R, S, R^2.

The first three groups are contact-injective.  This script performs one exact
destructive contact RREF, reconstructs every nonpivot R^2 relation from that
RREF, and applies the same source coefficients to the literal graph-boundary
map.  It records the first contact dependency, independent boundary normals,
and cumulative results by R^2 Y-degree.  The boundary uses the accepted
second-jet convention S=Hasse_2(P)=P''/2.  No compressed E oracle or augmented
second RREF is used.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import asdict
import gc
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat, nmod_poly

sys.path.insert(0, ".experiments")
import k0_capacity_positive_layer_attribution_6900 as Layer  # noqa: E402
import k0_first_positive_passive_universal_falsifier_6900 as Old  # noqa: E402
from k0_centered_head_y_correction_gate_6900 import (  # noqa: E402
    P, RAW_R, RAW_S, RAW_Y, RAW_Z, flattened_raw_column, raw_contact,
)


FOUR_POINT_TWO_GB = 4_200_000_000
INV_TWO = pow(2, -1, P)
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
if soft < 0 or soft > FOUR_POINT_TWO_GB:
    resource.setrlimit(resource.RLIMIT_AS, (FOUR_POINT_TWO_GB, hard))


def literal_expansions(profile, receipt, monomial):
    for node in receipt.nodes:
        for local, coefficient in flattened_raw_column(
                monomial, node, receipt.u0[node], receipt.u1[node],
                profile.m).items():
            if coefficient:
                yield (node, local), coefficient


def add_normal_basis(basis, vector):
    value = list(vector)
    for pivot in sorted(basis):
        factor = value[pivot]
        if factor:
            value = [
                (entry - factor * basis[pivot][coordinate]) % P
                for coordinate, entry in enumerate(value)
            ]
    pivot = next((coordinate for coordinate, entry in enumerate(value)
                  if entry), None)
    if pivot is None:
        return False
    inverse = pow(value[pivot], -1, P)
    basis[pivot] = tuple(entry * inverse % P for entry in value)
    return True


def poly_derivative(coefficients):
    return tuple((i + 1) * coefficients[i + 1] % P
                 for i in range(len(coefficients) - 1)) or (0,)


def poly_eval(coefficients, x):
    answer = 0
    for coefficient in reversed(coefficients):
        answer = (answer * x + coefficient) % P
    return answer


def poly_mul(left, right):
    answer = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            answer[i + j] = (answer[i + j] + a * b) % P
    while len(answer) > 1 and answer[-1] == 0:
        answer.pop()
    return tuple(answer)


def poly_pow(coefficients, exponent):
    answer = (1,)
    base = tuple(coefficients)
    while exponent:
        if exponent & 1:
            answer = poly_mul(answer, base)
        exponent //= 2
        if exponent:
            base = poly_mul(base, base)
    return answer


def poly_scale(coefficients, scalar):
    return tuple(scalar * coefficient % P for coefficient in coefficients)


def hasse_two(coefficients):
    """Coefficient polynomial for Hasse_2(f)=f''/2 in characteristic 101."""
    return poly_scale(poly_derivative(poly_derivative(tuple(coefficients))),
                      INV_TWO)


def formal_graph_bases(receipt):
    candidate = tuple(receipt.polynomial)
    return (
        candidate,
        poly_derivative(candidate),
        hasse_two(candidate),
        (receipt.seed % P,),
    )


def formal_monomial_value_poly(monomial, receipt):
    xp, yp, rp, sp, zp = monomial
    answer = (0,) * xp + (1,)
    for base, exponent in zip(
            formal_graph_bases(receipt), (yp, rp, sp, zp)):
        answer = poly_mul(answer, poly_pow(base, exponent))
    return nmod_poly(list(answer), P)


def formal_gradient(monomial, receipt, x):
    xp, yp, rp, sp, zp = monomial
    bases = tuple(poly_eval(base, x) for base in formal_graph_bases(receipt))
    exponents = (yp, rp, sp, zp)
    answer = []
    for coordinate in range(4):
        if exponents[coordinate] == 0:
            answer.append(0)
            continue
        value = pow(x, xp, P) * exponents[coordinate] % P
        for j, (base, exponent) in enumerate(zip(bases, exponents)):
            value = value * pow(base, exponent - (j == coordinate), P) % P
        answer.append(value)
    return tuple(answer)


def partial_x_at_graph(monomial, receipt, x):
    xp, yp, rp, sp, zp = monomial
    if xp == 0:
        return 0
    values = tuple(poly_eval(base, x) for base in formal_graph_bases(receipt))
    answer = xp * pow(x, xp - 1, P) % P
    for value, exponent in zip(values, (yp, rp, sp, zp)):
        answer = answer * pow(value, exponent, P) % P
    return answer


def relation_receipt(relation, monomials, groups, receipt, boundaries,
                     boundary_x):
    group_names = tuple(name for name, _shape, _indices in groups)
    group_of = {}
    for name, _shape, indices in groups:
        for index in indices:
            group_of[index] = name
    support = tuple(sorted((index, coefficient % P)
                           for index, coefficient in relation.items()
                           if coefficient % P))
    breakdown = Counter(group_of[index] for index, _coefficient in support)
    boundary = tuple(
        sum(coefficient * boundaries[index][coordinate]
            for index, coefficient in support) % P
        for coordinate in range(4)
    )

    specialized = nmod_poly([], P)
    partial_x = 0
    for index, coefficient in support:
        specialized += coefficient * formal_monomial_value_poly(
            monomials[index], receipt)
        partial_x = (partial_x + coefficient * partial_x_at_graph(
            monomials[index], receipt, boundary_x)) % P
    assert not specialized
    candidate = tuple(receipt.polynomial)
    graph_tangent = (
        poly_eval(poly_derivative(candidate), boundary_x),
        poly_eval(poly_derivative(poly_derivative(candidate)), boundary_x),
        poly_eval(poly_scale(poly_derivative(poly_derivative(
            poly_derivative(candidate))), INV_TWO), boundary_x),
        0,
    )
    tangent_pairing = sum(a * b for a, b in zip(boundary, graph_tangent)) % P
    assert (partial_x + tangent_pairing) % P == 0
    canonical = repr(support).encode()
    return {
        "relation_support_size": len(support),
        "relation_support_by_group": tuple(
            (name, breakdown.get(name, 0)) for name in group_names),
        "relation_source_sha256": hashlib.sha256(canonical).hexdigest(),
        "first_16_index_coefficient_monomial": tuple(
            (index, coefficient, monomials[index])
            for index, coefficient in support[:16]),
        "boundary_normal_Y_R_S_Z": boundary,
        "candidate_specialization_zero_polynomial": True,
        "partial_X_and_graph_tangent_pairing_sum": (
            partial_x, tangent_pairing, (partial_x + tangent_pairing) % P),
    }


def main():
    started = time.monotonic()
    profile = Old.K0.Profile(11, 5, 8, 6, 2, 1, 8, 8, 0, 1)
    receipt = Old.make_custom_receipt(
        profile, P, 0, "random", "mid", "minimal", "arbitrary",
        "alternating", 2)
    source = Old.K0.support(profile)
    group_specs = (
        ("raw", (0, 0)),
        ("R1", (1, 0)),
        ("S1", (0, 1)),
        ("R2", (2, 0)),
    )
    grouped_monomials = tuple(
        tuple(q for q in source if (q[2], q[3]) == shape)
        for _name, shape in group_specs)
    monomials = sum(grouped_monomials, ())
    assert Counter((q[2], q[3]) for q in source) == Counter({
        (0, 0): 1560, (1, 0): 1164, (0, 1): 1200, (2, 0): 840,
    })
    assert len(monomials) == 4764

    # Primitive formal-contact assertions and explicit row/boundary orders.
    node = receipt.nodes[0]
    assert raw_contact(RAW_R, receipt, profile.m, (node,)) == {
        (node, (0, 0, 0, 1, 0)): 1}
    assert raw_contact(RAW_S, receipt, profile.m, (node,)) == {
        (node, (0, 1, 0, 0, 0)): 1}
    assert raw_contact(RAW_Z, receipt, profile.m, (node,)) == {
        (node, (0, 0, 0, 0, 1)): 1}
    y_sanity = raw_contact(RAW_Y, receipt, profile.m, (node,))
    assert y_sanity.get((node, (1, 0, 0, 1, 0))) == 1
    assert y_sanity.get((node, (2, 1, 0, 0, 0))) == -1 % P
    assert y_sanity.get((node, (3, 0, 1, 0, 0))) == 1
    assert all(local[0] < profile.m for _node, local in y_sanity)
    assert formal_gradient(next(iter(RAW_Y)), receipt, profile.n) == (1, 0, 0, 0)
    assert formal_gradient(next(iter(RAW_R)), receipt, profile.n) == (0, 1, 0, 0)
    assert formal_gradient(next(iter(RAW_S)), receipt, profile.n) == (0, 0, 1, 0)
    assert formal_gradient(next(iter(RAW_Z)), receipt, profile.n) == (0, 0, 0, 1)

    rows_set = set()
    for position, monomial in enumerate(monomials, start=1):
        rows_set.update(row for row, _value in literal_expansions(
            profile, receipt, monomial))
        if position % 1000 == 0:
            print(f"row pass {position}/{len(monomials)}",
                  file=sys.stderr, flush=True)
    rows = tuple(sorted(rows_set, key=repr))
    row_index = {row: index for index, row in enumerate(rows)}
    matrix = nmod_mat(len(rows), len(monomials), P)
    boundaries = []
    for column, monomial in enumerate(monomials):
        for row, coefficient in literal_expansions(
                profile, receipt, monomial):
            matrix[row_index[row], column] = coefficient
        boundaries.append(formal_gradient(monomial, receipt, profile.n))
        if (column + 1) % 1000 == 0:
            print(f"fill pass {column + 1}/{len(monomials)}",
                  file=sys.stderr, flush=True)
    flattened_raw_column.cache_clear()
    gc.collect()
    print(f"contact rref {matrix.nrows()}x{matrix.ncols()}",
          file=sys.stderr, flush=True)
    _, rank = matrix.rref(inplace=True)
    pivots = Layer.pivot_columns(matrix, rank)
    pivot_set = set(pivots)
    assert rank == 4719

    group_indices = []
    offset = 0
    for (name, shape), group in zip(group_specs, grouped_monomials):
        indices = tuple(range(offset, offset + len(group)))
        group_indices.append((name, shape, indices))
        offset += len(group)
    groups = tuple(group_indices)
    r2_start = groups[-1][2][0]
    assert r2_start == 3924
    assert all(index in pivot_set for index in range(r2_start))

    normal_basis = {}
    first_dependency = None
    first_gains = {}
    y_rows = []
    contact_rank = r2_start
    nullity = 0
    relation_receipts = {}
    y_end = {}
    for y, count in sorted(Counter(q[1] for q in grouped_monomials[-1]).items()):
        y_end[y] = r2_start + sum(
            amount for degree, amount in Counter(
                q[1] for q in grouped_monomials[-1]).items()
            if degree <= y)

    for column in range(r2_start, len(monomials)):
        if column in pivot_set:
            contact_rank += 1
        else:
            nullity += 1
            relation = {column: 1}
            residual = list(boundaries[column])
            for row, pivot_column in enumerate(pivots):
                coefficient = int(matrix[row, column]) % P
                if not coefficient:
                    continue
                relation[pivot_column] = (-coefficient) % P
                residual = [
                    (entry - coefficient * boundaries[pivot_column][coordinate]) % P
                    for coordinate, entry in enumerate(residual)
                ]
            if first_dependency is None:
                first_dependency = relation_receipt(
                    relation, monomials, groups, receipt, boundaries,
                    profile.n)
                first_dependency["ordered_column_zero_based"] = column
                first_dependency["R2_column_one_based"] = column - r2_start + 1
                first_dependency["nonpivot_monomial_X_Y_R_S_Z"] = monomials[column]
            old_gain = len(normal_basis)
            if add_normal_basis(normal_basis, tuple(residual)):
                gain = len(normal_basis)
                receipt_row = relation_receipt(
                    relation, monomials, groups, receipt, boundaries,
                    profile.n)
                receipt_row["ordered_column_zero_based"] = column
                receipt_row["R2_column_one_based"] = column - r2_start + 1
                receipt_row["nonpivot_monomial_X_Y_R_S_Z"] = monomials[column]
                first_gains[gain] = receipt_row
                assert gain == old_gain + 1
        position = column + 1
        completed_y = next((y for y, end in y_end.items() if end == position), None)
        if completed_y is not None:
            y_rows.append({
                "completed_R2_Y_degree": completed_y,
                "total_columns_contact_rank_nullity_boundary_gain": (
                    position, contact_rank, nullity, len(normal_basis)),
            })

    assert (contact_rank, nullity) == (4719, 45)
    assert len(normal_basis) == 3
    assert first_dependency is not None
    assert set(first_gains) == set(range(1, len(normal_basis) + 1))
    stable = {
        "scope": (
            "exact literal flattened m6,L8 raw/R/S/R2 attribution with first "
            "R2 dependencies and boundary normals"
        ),
        "field": P,
        "profile_n_w_g_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "agreement_set": receipt.agreement,
        "candidate_and_tangent_degrees": (
            Old.degree(receipt.polynomial, P),
            Old.degree(receipt.tangent, P)),
        "contact_semantics": (
            "formal local rows (eps,S,T,R,Z), "
            "Y=u0+u1Z+epsR-eps^2S+eps^3T mod eps^m"
        ),
        "boundary_semantics": (
            "formal graph gradient at X=11 with S=Hasse_2(P)=P''/2, "
            "in script order (Y,R,S,Z)"
        ),
        "primitive_contact_sanity": True,
        "group_order_counts": tuple(
            (name, shape, len(group))
            for (name, shape), group in zip(group_specs, grouped_monomials)),
        "prefix_raw_R_S_is_contact_injective": True,
        "R2_relative_columns_contact_rank_kernel_boundary_gain": (
            len(grouped_monomials[-1]), rank - r2_start,
            len(grouped_monomials[-1]) - (rank - r2_start),
            len(normal_basis)),
        "first_R2_contact_dependency": first_dependency,
        "first_independent_boundary_gains": tuple(
            (gain, first_gains[gain])
            for gain in range(1, len(normal_basis) + 1)),
        "R2_Y_degree_stages": tuple(y_rows),
        "verdict": (
            "GREEN finite attribution: R2 is the first ordered group creating "
            "the complete contact kernel and its exact formal-boundary gain "
            "is three"
        ),
        "scope_guard": (
            "The first relation and Y-stage depend on the declared source "
            "order. This finite F101 extraction is not a target-uniform "
            "R2 recurrence, source count, or determinant proof."
        ),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    payload = {
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "runtime": {
            "seconds": round(time.monotonic() - started, 3),
            "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            "external_memory_cap_bytes": FOUR_POINT_TWO_GB,
        },
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
