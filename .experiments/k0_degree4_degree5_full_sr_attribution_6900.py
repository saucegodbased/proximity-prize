#!/usr/bin/env python3
"""Exact degree-4/degree-5 full-source and S*R attribution control.

The positive-margin profile ``(n,w,g,m,B,s,U,L)=(9,3,6,8,3,1,12,10)``
permits retained-badness tangents of degrees four and five.  Both cases use
the same deterministic candidate, agreement set, seed, and off-agreement
data; only the prescribed agreement tangent changes from X^4 to X^5.

One destructive exact contact RREF also yields the boundary gain.  For each
nonpivot source column, its RREF coefficients express its contact image using
earlier pivot columns.  Applying the identical relation to the four boundary
values gives a literal contact-kernel normal.  This avoids a second augmented
matrix and reports the first kernel and gains 1--4 in an explicit source
order.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import asdict, replace
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import k0_second_exact_chamber_full_source_rank_gate_6900 as Full  # noqa: E402
import k0_capacity_positive_layer_attribution_6900 as Layer  # noqa: E402
from higher6810_secondjet_retarget_exact import relaxed_rank_bound  # noqa: E402


K0 = Full.K0
P = Full.P
PROFILE = K0.Profile(9, 3, 6, 8, 3, 1, 12, 10, 0, 1)
TRIAL = 912


def boundary_value(profile, receipt, monomial):
    gradients = K0.monomial_gradient_polys(monomial, receipt)
    return tuple(int(polynomial(profile.n)) % P for polynomial in gradients)


def add_to_basis(basis, vector):
    value = list(vector)
    for pivot in sorted(basis):
        factor = value[pivot]
        if factor:
            value = [
                (entry - factor * basis[pivot][i]) % P
                for i, entry in enumerate(value)
            ]
    pivot = next((i for i, entry in enumerate(value) if entry), None)
    if pivot is None:
        return False
    inverse = pow(value[pivot], -1, P)
    basis[pivot] = tuple(entry * inverse % P for entry in value)
    return True


def ordered_source(profile):
    complete = K0.support(profile)
    selected_low = tuple(
        q for q in complete
        if (q[2], q[3]) in {(0, 0), (1, 0)}
        or ((q[2], q[3]) == (0, 1) and q[1] < profile.m)
        or (q[2], q[3], q[1]) == (1, 1, profile.m - 1)
        or ((q[2], q[3], q[1]) == (0, 1, profile.m) and q[4] <= 1))
    selected_set = set(selected_low)
    remaining_s = tuple(
        q for q in complete
        if (q[2], q[3]) == (0, 1) and q not in selected_set)
    r2 = tuple(q for q in complete if (q[2], q[3]) == (2, 0))
    r3 = tuple(q for q in complete if (q[2], q[3]) == (3, 0))
    remaining_sr = tuple(sorted(
        (q for q in complete
         if (q[2], q[3]) == (1, 1) and q not in selected_set),
        key=lambda q: (q[1], q[4], q[0])))
    groups = (selected_low, remaining_s, r2, r3, remaining_sr)
    if profile.L == 10:
        assert tuple(map(len, groups)) == (6661, 20, 1620, 1260, 1617)
    assert len(set().union(*(set(group) for group in groups))) == len(complete)
    return groups, sum(groups, ())


def literal_contact_matrix(profile, receipt, monomials):
    rows_set = set()
    for j, monomial in enumerate(monomials):
        rows_set.update(row for row, _ in Full.expansions(
            profile, receipt, monomial))
        if (j + 1) % 1000 == 0:
            print(f"row pass {j + 1}/{len(monomials)}",
                  file=sys.stderr, flush=True)
    rows = tuple(sorted(rows_set, key=repr))
    row_index = {row: i for i, row in enumerate(rows)}
    matrix = nmod_mat(len(rows), len(monomials), P)
    boundaries = []
    for j, monomial in enumerate(monomials):
        for row, value in Full.expansions(profile, receipt, monomial):
            matrix[row_index[row], j] = value
        boundaries.append(boundary_value(profile, receipt, monomial))
        if (j + 1) % 1000 == 0:
            print(f"fill pass {j + 1}/{len(monomials)}",
                  file=sys.stderr, flush=True)
    return matrix, boundaries


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--tangent-degree", type=int, choices=(4, 5),
                        required=True)
    parser.add_argument("--passive-cap", type=int, default=10)
    parser.add_argument("--receipt-passive-cap", type=int, default=10,
                        help=("passive cap used only to seed the deterministic "
                              "receipt; keep fixed for controlled cap tests"))
    args = parser.parse_args()
    started = time.monotonic()
    profile = replace(PROFILE, L=args.passive_cap)
    receipt_profile = replace(PROFILE, L=args.receipt_passive_cap)
    quotient_degree = args.tangent_degree - profile.w - 1
    receipt = Full.M8.monomial_tangent_receipt(
        receipt_profile, TRIAL, quotient_degree)
    assert K0.poly_degree(receipt.tangent) == args.tangent_degree
    groups, monomials = ordered_source(profile)
    group_names = ("selected_low", "remaining_S", "R2", "R3", "remaining_SR")
    group_ends = []
    running = 0
    for name, group in zip(group_names, groups):
        running += len(group)
        group_ends.append((running, name))
    sr_start = len(monomials) - len(groups[-1])
    y_ends = []
    running = sr_start
    for y, count in sorted(Counter(q[1] for q in groups[-1]).items()):
        running += count
        y_ends.append((running, y))

    local_bound = relaxed_rank_bound(
        profile.m, profile.L, profile.B, profile.s, profile.U)
    margin = len(monomials) - profile.n * local_bound
    if profile.L == 10:
        assert (len(monomials), local_bound, margin) == (11178, 1207, 315)
    assert margin > 0

    matrix, boundaries = literal_contact_matrix(
        profile, receipt, monomials)
    contact_rows = matrix.nrows()
    print(f"literal contact {matrix.nrows()}x{matrix.ncols()}; rref",
          file=sys.stderr, flush=True)
    _, rank = matrix.rref(inplace=True)
    pivots = Layer.pivot_columns(matrix, rank)
    pivot_set = set(pivots)

    normal_basis = {}
    contact_rank = 0
    nullity = 0
    first_kernel = None
    first_gain = {}
    group_table = []
    y_band_table = []
    group_end_map = dict(group_ends)
    y_end_map = dict(y_ends)
    for position, monomial in enumerate(monomials, start=1):
        column = position - 1
        if column in pivot_set:
            contact_rank += 1
        else:
            nullity += 1
            if first_kernel is None:
                first_kernel = {
                    "ordered_column": position,
                    "remaining_SR_column": position - sr_start,
                    "monomial_X_Y_R_S_Z": monomial,
                }
            residual = list(boundaries[column])
            for row, pivot_column in enumerate(pivots):
                coefficient = int(matrix[row, column]) % P
                if coefficient:
                    pivot_boundary = boundaries[pivot_column]
                    residual = [
                        (entry - coefficient * pivot_boundary[i]) % P
                        for i, entry in enumerate(residual)
                    ]
            if add_to_basis(normal_basis, tuple(residual)):
                gain = len(normal_basis)
                first_gain[gain] = {
                    "ordered_column": position,
                    "remaining_SR_column": position - sr_start,
                    "monomial_X_Y_R_S_Z": monomial,
                    "kernel_boundary_vector": tuple(residual),
                }
        if position in group_end_map:
            group_table.append((
                group_end_map[position], position, contact_rank, nullity,
                len(normal_basis)))
        if position in y_end_map:
            y_band_table.append((
                y_end_map[position], position, contact_rank, nullity,
                len(normal_basis)))

    assert contact_rank == rank
    assert nullity == len(monomials) - rank
    assert len(normal_basis) <= 4
    payload = {
        "scope": "exact full-source degree4/degree5 and SR-order discriminator",
        "field": "F_101",
        "profile_n_w_A_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "trial": TRIAL,
        "agreement_set": receipt.agreement,
        "seed": receipt.seed,
        "candidate_and_tangent_degrees": (
            K0.poly_degree(receipt.polynomial),
            K0.poly_degree(receipt.tangent)),
        "source_local_bound_margin": (
            len(monomials), local_bound,
            len(monomials) - profile.n * local_bound),
        "contact_rows_columns_rank_nullity_boundary_gain": (
            contact_rows, len(monomials), rank, nullity, len(normal_basis)),
        "source_order": (
            "selected low, remaining S, R2, R3, then remaining SR sorted "
            "by (Y degree, Z degree, X degree)"
        ),
        "group_name_columns_contact_rank_nullity_gain": group_table,
        "completed_SR_y_columns_contact_rank_nullity_gain": y_band_table,
        "first_contact_kernel_relation": first_kernel,
        "first_boundary_gain_1_through_4": first_gain,
        "ordering_caveat": (
            "first means this explicit order; it is not an order-independent "
            "minimality or target-universal claim"
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(
        canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    payload["runtime"] = {
        "seconds": round(time.monotonic() - started, 3),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
