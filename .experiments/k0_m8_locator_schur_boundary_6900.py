#!/usr/bin/env python3
"""Locator/Hasse Schur audit for the capacity-positive m=8 K0 receipt.

This is a finite mechanism discriminator, not a target theorem.  It replaces
the large literal target at each node by an exact 2179-row basis of the local
contact map, changes every consecutive X window to

    Lambda_A(X)^q X^d,  0 <= d < |A|=5,

and records the residual labels after row reduction.  The ``structure`` mode
checks the genuinely small first Schur step: the 91-dimensional familywise
localization cokernel is filled by the product of the five local contact
kernels.  The ``schur`` mode first quotients by the resulting full-rank
agreement map, then eliminates only the 6537-by-6784 error map and emits the
resulting four-by-268 boundary block.

Both modes are deterministic over F_101 and impose a process address-space
limit below 4 GiB.  No production submission file is imported or modified.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import asdict
import gc
import hashlib
import json
from math import comb, factorial
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat


LIMIT_BYTES = 3900 * 1024**2
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
new_hard = LIMIT_BYTES if hard == resource.RLIM_INFINITY else min(hard, LIMIT_BYTES)
resource.setrlimit(resource.RLIMIT_AS, (min(LIMIT_BYTES, new_hard), new_hard))

sys.path.insert(0, ".experiments")
import k0_second_exact_chamber_full_source_rank_gate_6900 as Full  # noqa: E402


K0 = Full.K0
P = Full.P
PROFILE = Full.PROFILE
BOUNDARY_X = PROFILE.n
FAMILY_NAME = {
    (0, 0): "one",
    (0, 1): "R",
    (1, 0): "S",
    (1, 1): "SR",
    (0, 2): "R2",
    (0, 3): "R3",
}
FAMILY_ORDER = {name: i for i, name in enumerate(
    ("one", "R", "S", "R2", "R3", "SR"))}


def add_to(out, key, value):
    value %= P
    if not value:
        return
    value = (out.get(key, 0) + value) % P
    if value:
        out[key] = value
    else:
        out.pop(key, None)


def poly_mul(left, right):
    out = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i + j] = (out[i + j] + a * b) % P
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return tuple(out)


def poly_pow(base, exponent):
    out = (1,)
    while exponent:
        if exponent & 1:
            out = poly_mul(out, base)
        exponent //= 2
        if exponent:
            base = poly_mul(base, base)
    return out


def poly_eval(poly, x):
    out = 0
    for a in reversed(poly):
        out = (out * x + a) % P
    return out


def hasse_translate(poly, x, cutoff=PROFILE.m):
    """Coefficients of p(x+epsilon), with ordinary Hasse normalization."""
    out = [0] * cutoff
    for degree, coefficient in enumerate(poly):
        for j in range(min(degree, cutoff - 1) + 1):
            out[j] = (out[j] + coefficient * comb(degree, j)
                      * pow(x, degree - j, P)) % P
    return tuple(out)


def locator(nodes):
    out = (1,)
    for x in nodes:
        out = poly_mul(out, ((-x) % P, 1))
    return out


def local_source_rows():
    """Literal relaxed local coordinates (outer,S,A,R,Z), grouped by S/R."""
    grouped = defaultdict(list)
    p = PROFILE
    for outer in range(p.m):
        for s in range(p.s + 1):
            for a in range(outer + 1):
                for r in range(p.B - 2 * s + 1):
                    if s + a + r > p.U:
                        continue
                    for z in range(p.L - s - a - r + 1):
                        grouped[(s, r)].append((outer, s, a, r, z))
    return {key: tuple(value) for key, value in grouped.items()}


def local_contact_column(source):
    """Contact A -> R-epsilon*S/2+epsilon^2*T in weighted-E rows.

    Output rows use the literal Python receipt order
    (free-epsilon, E, R, S, Z), with free-epsilon+3*E < m.
    """
    outer, s0, a0, r0, z0 = source
    out = {}
    minus_half = (-pow(2, -1, P)) % P
    for t_power in range(a0 + 1):
        for s_power in range(a0 - t_power + 1):
            r_power = a0 - t_power - s_power
            free = outer + s_power - t_power
            if free < 0 or free + 3 * t_power >= PROFILE.m:
                continue
            multinomial = (factorial(a0) //
                           (factorial(t_power) * factorial(s_power)
                            * factorial(r_power)))
            coefficient = multinomial * pow(minus_half, s_power, P)
            row = (free, t_power, r0 + r_power, s0 + s_power, z0)
            add_to(out, row, coefficient)
    return out


def local_contact_basis(local_rows):
    """Return target rows and a free-coordinate basis of the local kernel."""
    all_source = tuple(row for family in sorted(local_rows)
                       for row in local_rows[family])
    columns = tuple(local_contact_column(row) for row in all_source)
    terms = tuple(sorted({term for column in columns for term in column}, key=repr))
    term_index = {term: i for i, term in enumerate(terms)}
    transpose = nmod_mat(len(all_source), len(terms), P)
    for i, column in enumerate(columns):
        for term, coefficient in column.items():
            transpose[i, term_index[term]] = coefficient
    _, rank = transpose.rref(inplace=True)
    pivots = pivot_columns(transpose, rank)
    selected = tuple(terms[i] for i in pivots)
    assert (len(all_source), len(terms), rank, len(selected)) == (
        2844, 2965, 2179, 2179)
    del transpose
    gc.collect()

    selected_index = {term: i for i, term in enumerate(selected)}
    contact = nmod_mat(len(selected), len(all_source), P)
    for j, column in enumerate(columns):
        for term, coefficient in column.items():
            i = selected_index.get(term)
            if i is not None:
                contact[i, j] = coefficient
    _, rank2 = contact.rref(inplace=True)
    assert rank2 == rank
    source_pivots = pivot_columns(contact, rank2)
    source_pivot_set = set(source_pivots)
    source_free = tuple(i for i in range(len(all_source))
                        if i not in source_pivot_set)
    assert len(source_free) == 665
    kernel = nmod_mat(len(all_source), len(source_free), P)
    for j, free in enumerate(source_free):
        kernel[free, j] = 1
        for i, pivot in enumerate(source_pivots):
            kernel[pivot, j] = (-int(contact[i, free])) % P
    assert not any((nmod_mat(
        len(selected), len(all_source),
        [columns[j].get(term, 0) for term in selected
         for j in range(len(all_source))], P) * kernel).entries())
    free_labels = tuple(all_source[i] for i in source_free)
    del contact
    gc.collect()
    return selected, all_source, kernel, free_labels


def source_shapes(monomials):
    widths = {}
    for xp, y, r, s, z in monomials:
        key = (y, r, s, z)
        widths[key] = max(widths.get(key, 0), xp + 1)
    return widths


def make_labels(receipt):
    lam = locator(receipt.agreement)
    labels = []
    for (y, r, s, z), width in source_shapes(K0.support(PROFILE)).items():
        family = FAMILY_NAME[(s, r)]
        for degree in range(width):
            q, d = divmod(degree, len(receipt.agreement))
            poly = poly_mul(poly_pow(lam, q), (0,) * d + (1,))
            assert len(poly) - 1 == degree
            labels.append({
                "family": family,
                "s": s,
                "r": r,
                "y": y,
                "z": z,
                "width": width,
                "locator_level": q,
                "residual_degree": d,
                "top_partial": (q == width // len(receipt.agreement)
                                  and width % len(receipt.agreement) != 0),
                "poly": poly,
            })
    assert len(labels) == 17679
    return labels


def transformed_contact_column(receipt, label, node):
    """Literal contact of Lambda^q X^d times one raw inner monomial."""
    inner = Full.Shape.translated_column(
        0, (label["y"], label["r"], label["s"]), label["z"],
        node, receipt.u0[node], receipt.u1[node], PROFILE.m, 2, P)
    xjets = hasse_translate(label["poly"], node)
    out = {}
    for term, coefficient in inner.items():
        free, e, rr, ss, zz = term
        for shift, value in enumerate(xjets):
            if value and free + shift + 3 * e < PROFILE.m:
                add_to(out, (free + shift, e, rr, ss, zz),
                       coefficient * value)
    return out


def transformed_boundary_column(receipt, label):
    gradients = K0.monomial_gradient_polys(
        (0, label["y"], label["r"], label["s"], label["z"]), receipt)
    scale = poly_eval(label["poly"], BOUNDARY_X)
    return tuple(scale * int(value(BOUNDARY_X)) % P for value in gradients)


def localized_source_column(receipt, label, node):
    """Pre-contact localization in coordinates (outer,S,A,R,Z)."""
    y = label["y"]
    out = {}
    xjets = hasse_translate(label["poly"], node)
    u0 = receipt.u0[node]
    u1 = receipt.u1[node]
    for a_power in range(y + 1):
        anchor_power = y - a_power
        choose_a = comb(y, a_power)
        for z_from_anchor in range(anchor_power + 1):
            anchor_coefficient = (comb(anchor_power, z_from_anchor)
                                  * pow(u0, anchor_power - z_from_anchor, P)
                                  * pow(u1, z_from_anchor, P))
            for x_order, x_coefficient in enumerate(xjets):
                outer = x_order + a_power
                if outer >= PROFILE.m or not x_coefficient:
                    continue
                row = (outer, label["s"], a_power, label["r"],
                       label["z"] + z_from_anchor)
                add_to(out, row, choose_a * anchor_coefficient * x_coefficient)
    return out


def compose_local_contact(localized):
    out = {}
    for source, coefficient in localized.items():
        for target, value in local_contact_column(source).items():
            add_to(out, target, coefficient * value)
    return out


def validate_factorization(receipt, labels):
    probes = (labels[0], labels[len(labels) // 3], labels[-1])
    probes += tuple(label for label in labels
                    if label["family"] in ("S", "SR", "R2", "R3")
                    and label["locator_level"] >= 2)[:5]
    for label in probes:
        for node in receipt.nodes:
            direct = transformed_contact_column(receipt, label, node)
            factored = compose_local_contact(
                localized_source_column(receipt, label, node))
            assert direct == factored, (label, node, direct, factored)


def locator_charts(receipt):
    """Confluent Vandermonde charts for every possible local A degree."""
    lam = locator(receipt.agreement)
    charts = {}
    for a_power in range(PROFILE.m):
        height = PROFILE.m - a_power
        basis = tuple((q, d) for q in range(height)
                      for d in range(len(receipt.agreement)))
        rows = tuple((node, t) for node in receipt.agreement
                     for t in range(height))
        matrix = nmod_mat(
            len(rows), len(basis),
            [hasse_translate(poly_mul(poly_pow(lam, q), (0,) * d + (1,)),
                             node, height)[t]
             for node, t in rows for q, d in basis], P)
        assert matrix.nrows() == matrix.ncols()
        assert matrix.rank() == len(rows)
        inverse = matrix.inv()
        charts[a_power] = {
            "height": height,
            "basis": basis,
            "rows": rows,
            "inverse": tuple(tuple(int(inverse[i, j])
                                   for j in range(inverse.ncols()))
                             for i in range(inverse.nrows())),
        }
    return charts


def transformed_localization_column(receipt, label, charts):
    """Agreement localization in canonical locator/Hasse coordinates.

    Coordinates are (local-A, local-Z, locator-level, residue-degree); the
    raw S/R exponents are fixed by the surrounding derivative family.
    """
    grouped = defaultdict(dict)
    for node_position, node in enumerate(receipt.agreement):
        for row, value in localized_source_column(receipt, label, node).items():
            outer, _s, a_power, _r, z = row
            raw_index = node_position * charts[a_power]["height"] + (
                outer - a_power)
            grouped[(a_power, z)][raw_index] = value
    out = {}
    for (a_power, z), raw in grouped.items():
        chart = charts[a_power]
        inverse = chart["inverse"]
        for coordinate, (q, d) in enumerate(chart["basis"]):
            value = sum(inverse[coordinate][j] * coefficient
                        for j, coefficient in raw.items()) % P
            if value:
                out[(a_power, z, q, d)] = value
    return out


def pivot_columns(rref, rank):
    answer = []
    column = 0
    for row in range(rank):
        while column < rref.ncols() and int(rref[row, column]) % P == 0:
            column += 1
        assert column < rref.ncols()
        answer.append(column)
        column += 1
    return tuple(answer)


def locator_summary(labels):
    counts = Counter((label["family"], label["locator_level"],
                      label["residual_degree"], label["top_partial"])
                     for label in labels)
    return tuple((family, q, d, partial, count)
                 for (family, q, d, partial), count in sorted(
                     counts.items(), key=lambda item: (
                         FAMILY_ORDER[item[0][0]], item[0][1], item[0][2],
                         item[0][3])))


def structure_audit(receipt, labels, local_rows, local_source,
                    local_kernel, local_kernel_free):
    """Familywise Hermite elimination and its 91-cell contact repair."""
    charts = locator_charts(receipt)
    answer = []
    quotient_data = []
    for family_pair in sorted(local_rows, key=lambda pair: FAMILY_ORDER[
            FAMILY_NAME[pair]]):
        family = FAMILY_NAME[family_pair]
        family_labels = [label for label in labels if label["family"] == family]
        rows_one = local_rows[family_pair]
        rows = tuple((a_power, z, q, d)
                     for _outer, _s, a_power, _r, z in rows_one
                     if _outer == a_power
                     for q in range(PROFILE.m - a_power)
                     for d in range(len(receipt.agreement)))
        # The comprehension above lists each (a,z) block exactly once: the
        # local source contains its lowest legal outer degree outer=A.
        assert len(rows) == len(rows_one) * len(receipt.agreement)
        row_index = {row: i for i, row in enumerate(rows)}
        matrix = nmod_mat(len(rows), len(family_labels), P)
        for j, label in enumerate(family_labels):
            for row, value in transformed_localization_column(
                    receipt, label, charts).items():
                matrix[row_index[row], j] = value

        # Left-null vectors are the literal residual locator/Hasse cells.
        padded, cokernel_dimension = matrix.transpose().nullspace()
        qmatrix = nmod_mat(cokernel_dimension, len(rows), P)
        for j in range(cokernel_dimension):
            for i in range(len(rows)):
                value = int(padded[i, j]) % P
                qmatrix[j, i] = value
        del padded
        gc.collect()
        _, qrank = qmatrix.rref(inplace=True)
        assert qrank == cokernel_dimension
        dual_leads = [rows[i] for i in pivot_columns(qmatrix, qrank)]

        _, rank = matrix.rref(inplace=True)
        pivots = pivot_columns(matrix, rank)
        pivot_set = set(pivots)
        residual = [label for j, label in enumerate(family_labels)
                    if j not in pivot_set]
        assert rank + cokernel_dimension == len(rows)
        answer.append({
            "family": family,
            "global_columns": len(family_labels),
            "one_node_local_source_rows": len(rows_one),
            "five_node_rows_and_rank": (len(rows), rank),
            "localization_kernel_dimension": len(residual),
            "localization_cokernel_dimension": cokernel_dimension,
            "cokernel_dual_lead_A_Z_locatorLevel_residueDegree":
                tuple(dual_leads),
            "nonpivot_locator_labels": locator_summary(residual),
        })
        quotient_data.append((family_pair, rows, qmatrix, dual_leads))
        del matrix
        gc.collect()
    assert sum(row["localization_kernel_dimension"] for row in answer) == 3550
    assert sum(row["localization_cokernel_dimension"] for row in answer) == 91

    # Test whether the product of five universal 665-dimensional local
    # contact kernels fills all 91 locator/Hasse deficits.  This is the small
    # Schur complement behind maximal agreement contact rank.
    source_index = {row: i for i, row in enumerate(local_source)}
    residual = nmod_mat(91, len(receipt.agreement) * 665, P)
    residual_row = 0
    residual_row_labels = []
    for family_pair, transformed_rows, qmatrix, dual_leads in quotient_data:
        rows_one = local_rows[family_pair]
        h_family = nmod_mat(len(rows_one), 665, P)
        for i, row in enumerate(rows_one):
            source_row = source_index[row]
            for j in range(665):
                h_family[i, j] = local_kernel[source_row, j]
        transformed_index = {row: i for i, row in enumerate(transformed_rows)}
        family = FAMILY_NAME[family_pair]
        for node_position, node in enumerate(receipt.agreement):
            qnode = nmod_mat(qmatrix.nrows(), len(rows_one), P)
            for raw_column, (outer, _s, a_power, _r, z) in enumerate(rows_one):
                chart = charts[a_power]
                raw_index = node_position * chart["height"] + (outer - a_power)
                for locator_coordinate, (q, d) in enumerate(chart["basis"]):
                    transformed_row = transformed_index[(a_power, z, q, d)]
                    coefficient = chart["inverse"][locator_coordinate][raw_index]
                    if coefficient:
                        for coker_row in range(qmatrix.nrows()):
                            value = (int(qnode[coker_row, raw_column])
                                     + int(qmatrix[coker_row, transformed_row])
                                     * coefficient) % P
                            qnode[coker_row, raw_column] = value
            block = qnode * h_family
            for i in range(block.nrows()):
                for j in range(block.ncols()):
                    residual[residual_row + i, node_position * 665 + j] = block[i, j]
        residual_row_labels.extend((family,) + tuple(label)
                                   for label in dual_leads)
        residual_row += qmatrix.nrows()
    assert residual_row == 91
    _, repair_rank = residual.rref(inplace=True)
    assert repair_rank == 91
    repair_pivots = pivot_columns(residual, repair_rank)
    repair_columns = tuple({
        "agreement_node": receipt.agreement[column // 665],
        "local_kernel_free_coordinate_outer_S_A_R_Z":
            local_kernel_free[column % 665],
        "local_kernel_free_family": FAMILY_NAME[(
            local_kernel_free[column % 665][1],
            local_kernel_free[column % 665][3])],
    } for column in repair_pivots)
    repair_summary = Counter(row["local_kernel_free_family"]
                             for row in repair_columns)
    residual_summary = {
        "shape_rank": (91, 5 * 665, repair_rank),
        "row_labels_family_A_Z_locatorLevel_residueDegree":
            tuple(residual_row_labels),
        "pivot_local_kernel_columns": repair_columns,
        "pivot_family_counts": tuple(sorted(repair_summary.items(),
                                             key=lambda item:
                                             FAMILY_ORDER[item[0]])),
        "interpretation": (
            "the five local contact kernels surject onto every familywise "
            "localization deficit, so agreement contact has rank 5*2179"
        ),
    }
    return tuple(answer), residual_summary


def is_selected_low(label):
    r, s, y, z = label["r"], label["s"], label["y"], label["z"]
    return ((r, s) in {(0, 0), (1, 0)}
            or ((r, s) == (0, 1) and y < PROFILE.m)
            or (r, s, y) == (1, 1, PROFILE.m - 1)
            or ((r, s, y) == (0, 1, PROFILE.m) and z <= 1))


def column_stage(label):
    if is_selected_low(label):
        return 0
    if label["family"] == "S":
        return 1
    if label["family"] == "R2":
        return 2
    if label["family"] == "R3":
        return 3
    assert label["family"] == "SR"
    return 4


def ordered_labels(labels):
    # Descending locator level is the natural back-substitution order for
    # agreement Hasse jets.  The stage order reuses the exact injective prefix
    # certificate from f2119ef and therefore forces all final free coordinates
    # into the omitted SR family.
    return tuple(sorted(labels, key=lambda label: (
        column_stage(label), -label["locator_level"],
        label["residual_degree"], label["y"], label["z"])))


def schur_audit(receipt, labels, selected_terms):
    labels = ordered_labels(labels)
    stage_counts = Counter(column_stage(label) for label in labels)
    assert tuple(stage_counts[i] for i in range(5)) == (
        9964, 258, 2640, 2195, 2622)
    errors = tuple(node for node in receipt.nodes
                   if node not in receipt.agreement)
    selected_index = {term: i for i, term in enumerate(selected_terms)}
    selected_set = set(selected_terms)

    # First Schur step: eliminate agreement contact alone.  Its exact rank is
    # 5*2179, independently certified by structure_audit's 91-cell repair.
    agreement_rank = len(receipt.agreement) * len(selected_terms)
    agreement = nmod_mat(agreement_rank, len(labels), P)
    boundary = nmod_mat(4, len(labels), P)
    for j, label in enumerate(labels):
        for node_position, node in enumerate(receipt.agreement):
            for term, value in transformed_contact_column(
                    receipt, label, node).items():
                if term in selected_set:
                    agreement[node_position * len(selected_terms)
                              + selected_index[term], j] = value
        for coordinate, value in enumerate(
                transformed_boundary_column(receipt, label)):
            boundary[coordinate, j] = value
        if (j + 1) % 500 == 0:
            print(f"agreement contact fill {j + 1}/{len(labels)}",
                  file=sys.stderr, flush=True)
    print(f"agreement contact {agreement.nrows()}x{agreement.ncols()}; "
          "in-place rref", file=sys.stderr, flush=True)
    _, rank = agreement.rref(inplace=True)
    assert rank == agreement_rank == 10895
    agreement_pivots = pivot_columns(agreement, rank)
    agreement_pivot_set = set(agreement_pivots)
    agreement_free = tuple(i for i in range(len(labels))
                           if i not in agreement_pivot_set)
    assert len(agreement_free) == 6784

    # RREF is [I A] in the pivot/free coordinate order, hence
    # K=(-A;I) is an exact full-column-rank basis of ker(C_agreement).
    # Store A instead of the much larger 17679-by-6784 K.  The two asserted
    # dimensions plus FLINT's exact RREF contract check C_agreement*K=0 and
    # rank(K)=6784 before any error row is constructed.
    agreement_a = nmod_mat(rank, len(agreement_free), P)
    for i in range(rank):
        for j, column in enumerate(agreement_free):
            agreement_a[i, j] = agreement[i, column]
    assert agreement_a.nrows() + agreement_a.ncols() == len(labels)
    agreement_kernel_certificate = {
        "rref_shape_rank": (agreement.nrows(), agreement.ncols(), rank),
        "kernel_basis_shape_rank": (len(labels), len(agreement_free),
                                    len(agreement_free)),
        "identity": "RREF=[I A], K=(-A;I), hence C_agreement*K=0",
        "checked_before_error_elimination": True,
    }

    # Push the boundary through the same exact agreement quotient.
    b_pivot = nmod_mat(4, rank, P)
    b_free = nmod_mat(4, len(agreement_free), P)
    for row in range(4):
        for j, column in enumerate(agreement_pivots):
            b_pivot[row, j] = boundary[row, column]
        for j, column in enumerate(agreement_free):
            b_free[row, j] = boundary[row, column]
    boundary_kernel = b_free - b_pivot * agreement_a
    del agreement, boundary, b_pivot, b_free
    gc.collect()

    # Second Schur step: evaluate K on only the three error nodes.  Partition
    # C_error by the agreement pivots/free coordinates so that
    # C_error*K = C_error,free - C_error,pivot*A, without materializing K.
    error_rows = len(errors) * len(selected_terms)
    error_pivot = nmod_mat(error_rows, rank, P)
    error_free = nmod_mat(error_rows, len(agreement_free), P)
    pivot_position = {column: j for j, column in enumerate(agreement_pivots)}
    free_position = {column: j for j, column in enumerate(agreement_free)}
    for column, label in enumerate(labels):
        target = error_pivot if column in agreement_pivot_set else error_free
        target_column = (pivot_position[column] if column in agreement_pivot_set
                         else free_position[column])
        for node_position, node in enumerate(errors):
            for term, value in transformed_contact_column(
                    receipt, label, node).items():
                if term in selected_set:
                    target[node_position * len(selected_terms)
                           + selected_index[term], target_column] = value
        if (column + 1) % 500 == 0:
            print(f"error contact fill {column + 1}/{len(labels)}",
                  file=sys.stderr, flush=True)
    print("forming 6537x6784 error-on-agreement-kernel map",
          file=sys.stderr, flush=True)
    error_kernel = error_pivot * agreement_a
    error_kernel = error_free - error_kernel
    del error_pivot, error_free, agreement_a
    gc.collect()
    print(f"error kernel {error_kernel.nrows()}x{error_kernel.ncols()}; "
          "in-place rref", file=sys.stderr, flush=True)
    _, error_rank = error_kernel.rref(inplace=True)
    assert error_rank == 6516
    error_pivots = pivot_columns(error_kernel, error_rank)
    error_pivot_set = set(error_pivots)
    final_free = tuple(i for i in range(len(agreement_free))
                       if i not in error_pivot_set)
    assert len(final_free) == 268
    final_global_columns = tuple(agreement_free[i] for i in final_free)
    assert all(labels[i]["family"] == "SR" for i in final_global_columns)

    # The last quotient is now literally four rows by 268 columns.
    error_a = nmod_mat(error_rank, len(final_free), P)
    for i in range(error_rank):
        for j, column in enumerate(final_free):
            error_a[i, j] = error_kernel[i, column]
    bk_pivot = nmod_mat(4, error_rank, P)
    bk_free = nmod_mat(4, len(final_free), P)
    for row in range(4):
        for j, column in enumerate(error_pivots):
            bk_pivot[row, j] = boundary_kernel[row, column]
        for j, column in enumerate(final_free):
            bk_free[row, j] = boundary_kernel[row, column]
    schur = bk_free - bk_pivot * error_a
    assert schur.rank() == 4
    schur_rref, schur_rank = schur.rref()
    witness_relative = pivot_columns(schur_rref, schur_rank)
    witness_columns = tuple(final_global_columns[j] for j in witness_relative)
    witness_minor = nmod_mat(
        4, 4,
        [int(schur[i, j]) for i in range(4) for j in witness_relative], P)
    witness_labels = tuple(labels[j] for j in witness_columns)
    serial_labels = tuple({key: value for key, value in label.items()
                           if key != "poly"} for label in witness_labels)
    nonpivot_labels = tuple(labels[j] for j in final_global_columns)
    support_labels = tuple(labels[final_global_columns[j]]
                           for j in range(len(final_global_columns))
                           if any(int(schur[i, j]) for i in range(4)))
    serial_nonpivots = tuple({key: value for key, value in label.items()
                              if key != "poly"} for label in nonpivot_labels)
    serial_support = tuple({key: value for key, value in label.items()
                            if key != "poly"} for label in support_labels)
    payload = {
        "agreement_kernel_certificate": agreement_kernel_certificate,
        "agreement_free_coordinate_count": len(agreement_free),
        "error_on_agreement_kernel_rows_columns_rank_nullity": (
            error_rows, len(agreement_free), error_rank, len(final_free)),
        "ordered_stage_counts": tuple(stage_counts[i] for i in range(5)),
        "free_coordinate_locator_labels": locator_summary(nonpivot_labels),
        "free_coordinate_exact_labels": serial_nonpivots,
        "boundary_schur_shape_rank": (4, len(final_free), schur.rank()),
        "boundary_schur_nonzero_columns": len(support_labels),
        "boundary_schur_support_locator_labels": locator_summary(support_labels),
        "boundary_schur_support_exact_labels": serial_support,
        "witness_relative_columns": witness_relative,
        "witness_source_labels": serial_labels,
        "witness_4x4_rows": tuple(tuple(int(witness_minor[i, j])
                                        for j in range(4)) for i in range(4)),
        "witness_determinant": int(witness_minor.det()) % P,
        "free_labels_sha256": hashlib.sha256(repr(tuple(
            {key: value for key, value in label.items() if key != "poly"}
            for label in nonpivot_labels)).encode()).hexdigest(),
        "schur_entries_sha256": hashlib.sha256(repr(tuple(
            tuple(int(schur[i, j]) for j in range(schur.ncols()))
            for i in range(4))).encode()).hexdigest(),
    }
    del error_kernel, boundary_kernel, error_a, bk_pivot, bk_free, schur
    gc.collect()
    return payload


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("validate", "structure", "schur"),
                        default="validate")
    args = parser.parse_args()
    started = time.monotonic()
    receipt = Full.M8.monomial_tangent_receipt(PROFILE, 811, 0)
    local_rows = local_source_rows()
    labels = make_labels(receipt)
    selected_terms, local_source, local_kernel, local_kernel_free = \
        local_contact_basis(local_rows)
    validate_factorization(receipt, labels)

    local_counts = tuple((FAMILY_NAME[key], len(local_rows[key])) for key in
                         sorted(local_rows, key=lambda pair:
                                FAMILY_ORDER[FAMILY_NAME[pair]]))
    stable = {
        "scope": "m8 K0 locator/Hasse agreement and boundary Schur audit",
        "mode": args.mode,
        "field": "F_101",
        "profile_n_w_A_m_B_s_U_L_k_n0": tuple(asdict(PROFILE).values()),
        "trial": 811,
        "agreement_set": receipt.agreement,
        "errors": tuple(node for node in receipt.nodes
                        if node not in receipt.agreement),
        "seed": receipt.seed,
        "agreement_locator_low_to_high": locator(receipt.agreement),
        "global_source_columns": len(labels),
        "local_source_family_rows": local_counts,
        "local_source_contact_rows_rank_kernel": (2844, 2965, 2179, 665),
        "five_agreement_localization_rows": 5 * 2844,
        "factorization_identity_checked": True,
    }
    if args.mode in ("structure", "schur"):
        families, repair = structure_audit(
            receipt, labels, local_rows, local_source,
            local_kernel, local_kernel_free)
        stable["agreement_localization_families"] = families
        stable["agreement_locator_contact_repair"] = repair
        stable["agreement_schur_dimensions"] = {
            "localization_kernel": 3550,
            "localization_cokernel_repaired_by_local_contact_kernel": 91,
            "five_local_contact_kernels": 5 * 665,
            "local_contact_kernel_intersection": 5 * 665 - 91,
            "agreement_contact_kernel": 3550 + 5 * 665 - 91,
            "agreement_contact_rank": 5 * 2179,
        }
        assert 3550 + 5 * 665 - 91 == 6784
        assert len(labels) - 6784 == 5 * 2179
    if args.mode == "schur":
        stable["full_contact_boundary_schur"] = schur_audit(
            receipt, labels, selected_terms)
    stable["verdict"] = (
        "The agreement step is an exact locator/Hasse quotient.  In schur "
        "mode the final four normals are read from a 4x268 block; this is "
        "finite mechanism evidence, not a universal target recurrence."
    )
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    result = {
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "runtime": {
            "seconds": round(time.monotonic() - started, 3),
            "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            "address_space_limit_bytes": LIMIT_BYTES,
        },
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
