#!/usr/bin/env python3
"""Exact chain-rule audit of the first raw-1 passive relative killer.

The source order is the complete L10 source followed by the L11 passive
``raw 1`` bands in increasing active degree/seed/X degree, stopping at
``X^2 Y^9 Z^2``.  The final column is the first new dependency in that order
and the first one whose repaired boundary normal escapes the L10 rank-three
image.  This script reconstructs the literal relation and checks its contact,
candidate specialization, old conormal pairing, and full five-coordinate
chain rule.
"""

from __future__ import annotations

from dataclasses import asdict, replace
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_poly

sys.path.insert(0, ".experiments")
import k0_degree4_degree5_full_sr_attribution_6900 as Degree  # noqa: E402
import k0_capacity_positive_layer_attribution_6900 as Layer  # noqa: E402


K0 = Degree.K0
P = Degree.P
KILLER = (2, 9, 0, 0, 2)


def dot(left, right):
    return sum(a * b for a, b in zip(left, right)) % P


def partial_x_at(monomial, receipt, x):
    xp, yp, rp, sp, zp = monomial
    if xp == 0:
        return 0
    value = xp * pow(x, xp - 1, P) % P
    for base, exponent in zip(
            K0.bases(receipt), (yp, rp, sp, zp)):
        value = value * pow(int(base(x)) % P, exponent, P) % P
    return value


def main():
    started = time.monotonic()
    profile10 = replace(Degree.PROFILE, L=10)
    profile11 = replace(Degree.PROFILE, L=11)
    receipt = Degree.Full.M8.monomial_tangent_receipt(
        profile10, Degree.TRIAL, 0)
    base = K0.support(profile10)
    source11 = set(K0.support(profile11))
    added_raw1 = tuple(sorted(
        (q for q in source11 - set(base)
         if (q[2], q[3]) == (0, 0) and q[4] > 0),
        key=lambda q: (q[1], q[4], q[0])))
    killer_index = added_raw1.index(KILLER)
    raw_prefix = added_raw1[:killer_index + 1]
    monomials = base + raw_prefix
    assert len(raw_prefix) == 327
    assert monomials[-1] == KILLER
    assert all(q[1] + q[4] == 11 for q in raw_prefix)

    matrix, boundaries = Degree.literal_contact_matrix(
        profile11, receipt, monomials)
    print(f"raw1 killer contact {matrix.nrows()}x{matrix.ncols()}; rref",
          file=sys.stderr, flush=True)
    _, rank = matrix.rref(inplace=True)
    pivots = Layer.pivot_columns(matrix, rank)
    pivot_set = set(pivots)
    final_column = len(monomials) - 1
    assert final_column not in pivot_set
    assert all(column in pivot_set
               for column in range(len(base), final_column))
    assert (rank, len(monomials) - rank) == (11187, 318)

    relation = {final_column: 1}
    for row, pivot_column in enumerate(pivots):
        coefficient = (-int(matrix[row, final_column])) % P
        if coefficient:
            relation[pivot_column] = coefficient
    relation_support = tuple(sorted(
        (monomials[column], coefficient)
        for column, coefficient in relation.items()))
    base_terms = sum(column < len(base) for column in relation)
    raw1_terms = len(relation) - base_terms
    assert (len(relation), base_terms, raw1_terms) == (10193, 9908, 285)

    contact = {}
    specialization = nmod_poly([], P)
    boundary = [0, 0, 0, 0]
    partial_x = 0
    x = profile10.n
    for column, coefficient in relation.items():
        monomial = monomials[column]
        for row_key, row_value in Degree.Full.expansions(
                profile11, receipt, monomial):
            value = (contact.get(row_key, 0)
                     + coefficient * row_value) % P
            if value:
                contact[row_key] = value
            else:
                contact.pop(row_key, None)
        specialization += coefficient * K0.monomial_value_poly(
            monomial, receipt)
        monomial_boundary = boundaries[column]
        boundary = [
            (entry + coefficient * monomial_boundary[i]) % P
            for i, entry in enumerate(boundary)]
        partial_x = (partial_x + coefficient * partial_x_at(
            monomial, receipt, x)) % P
    assert not contact
    assert not specialization
    boundary = tuple(boundary)
    assert boundary == (71, 5, 97, 79)

    # Recover the complete old normal image using the same prefix RREF.  Later
    # pivot columns have zero coefficients in every earlier nonpivot column.
    old_basis = {}
    old_nonpivots = tuple(
        column for column in range(len(base)) if column not in pivot_set)
    assert len(old_nonpivots) == 317
    for column in old_nonpivots:
        residual = list(boundaries[column])
        for row, pivot_column in enumerate(pivots):
            coefficient = int(matrix[row, column]) % P
            if coefficient:
                assert pivot_column < len(base)
                residual = [
                    (entry - coefficient * boundaries[pivot_column][i]) % P
                    for i, entry in enumerate(residual)]
        Degree.add_to_basis(old_basis, tuple(residual))
    assert len(old_basis) == 3

    tangent_conormal = tuple(
        int(polynomial(x)) % P for polynomial in K0.tangent_bases(receipt))
    assert tangent_conormal == (97, 88, 63, 1)
    assert all(dot(tangent_conormal, vector) == 0
               for vector in old_basis.values())
    tangent_on_killer = dot(tangent_conormal, boundary)
    assert tangent_on_killer == 84

    candidate = K0.as_poly(receipt.polynomial)
    candidate_graph_tangent = (
        int(candidate.derivative()(x)) % P,
        int(candidate.derivative().derivative()(x)) % P,
        int(candidate.derivative().derivative().derivative()(x)) % P,
        0,
    )
    graph_pairing = dot(candidate_graph_tangent, boundary)
    full_chain_derivative = (partial_x + graph_pairing) % P
    assert candidate_graph_tangent == (29, 52, 38, 0)
    assert (partial_x, graph_pairing, full_chain_derivative) == (55, 46, 0)

    payload = {
        "scope": "exact raw-1 passive relative-killer chain-rule audit",
        "field": "F_101",
        "receipt_profile": tuple(asdict(profile10).values()),
        "source_profile": tuple(asdict(profile11).values()),
        "trial": Degree.TRIAL,
        "agreement_set": receipt.agreement,
        "contact_rows_columns_rank_nullity": (
            matrix.nrows(), matrix.ncols(), rank, len(monomials) - rank),
        "L10_base_and_raw1_prefix_counts": (len(base), len(raw_prefix)),
        "all_prior_new_raw1_columns_independent": True,
        "first_new_dependency_and_fourth_normal": KILLER,
        "relation_support_total_base_raw1": (
            len(relation), base_terms, raw1_terms),
        "relation_support_sha256": hashlib.sha256(
            repr(relation_support).encode()).hexdigest(),
        "literal_contact_support_size": len(contact),
        "candidate_specialization_identically_zero": not specialization,
        "candidate_specialization_degree_bound_and_agreement_root_count": (
            47, profile10.m * len(receipt.agreement)),
        "old_boundary_normal_rank": len(old_basis),
        "old_conormal_Q_Q1_Q2_1": tangent_conormal,
        "new_repaired_boundary_normal": boundary,
        "old_conormal_pairing_with_new_normal": tangent_on_killer,
        "candidate_graph_tangent_Y_R_S_Z": candidate_graph_tangent,
        "partial_X_and_graph_pairing_and_full_chain_derivative": (
            partial_x, graph_pairing, full_chain_derivative),
        "interpretation": (
            "the repaired relation is zero on the candidate curve and obeys "
            "the full X,Y,R,S,Z chain rule, while its four-coordinate normal "
            "escapes the old image; raw-1 passive connection is genuine"),
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
