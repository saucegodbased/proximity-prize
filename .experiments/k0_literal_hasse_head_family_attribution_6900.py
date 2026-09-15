#!/usr/bin/env python3
"""Exact derivative-family attribution for the formal eps>=3 head.

This is the corrected F_101 m6,L8 control.  Contact rows are literal
``(eps,S,T,R,Z)`` rows and boundary specialization is
``(Y,R,S,Z)=(P,P',Hasse_2(P),gamma)``.  The source is ordered by derivative
family ``raw,R,S,R^2``.  For epsilon cutoffs 3,2,1,0 we compute one exact RREF,
the boundary rank on its kernel after every family, and (at cutoff 3) receipts
for the first four independent head-boundary directions.  Their discarded
eps<3 residuals identify the one-dimensional tail obstruction.
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

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import k0_capacity_positive_layer_attribution_6900 as Layer  # noqa: E402
import k0_first_positive_passive_universal_falsifier_6900 as Old  # noqa: E402
import k0_literal_r2_first_dependency_6900 as R2  # noqa: E402
from k0_centered_head_y_correction_gate_6900 import (  # noqa: E402
    P, RAW_R, RAW_S, RAW_Y, RAW_Z, flattened_raw_column, raw_contact,
)


FOUR_POINT_TWO_GB = 4_200_000_000
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


def relation_from_rref(matrix, pivots, column):
    relation = {column: 1}
    for row, pivot_column in enumerate(pivots):
        coefficient = int(matrix[row, column]) % P
        if coefficient:
            relation[pivot_column] = (-coefficient) % P
    return relation


def apply_boundary(relation, boundaries):
    return tuple(
        sum(coefficient * boundaries[index][coordinate]
            for index, coefficient in relation.items()) % P
        for coordinate in range(4)
    )


def head_relation_receipt(relation, monomials, group_of, receipt, profile,
                          boundaries):
    support = tuple(sorted((index, coefficient % P)
                           for index, coefficient in relation.items()
                           if coefficient % P))
    tail = {}
    head = {}
    for index, coefficient in support:
        for row, value in literal_expansions(profile, receipt, monomials[index]):
            target = tail if row[1][0] < 3 else head
            updated = (target.get(row, 0) + coefficient * value) % P
            if updated:
                target[row] = updated
            else:
                target.pop(row, None)
    assert not head
    breakdown = Counter(group_of[index] for index, _coefficient in support)
    tail_order = Counter(row[1][0] for row in tail)
    tail_node = Counter(row[0] for row in tail)
    canonical = repr(support).encode()
    return {
        "relation_support_size": len(support),
        "relation_support_by_family": tuple(sorted(breakdown.items())),
        "relation_source_sha256": hashlib.sha256(canonical).hexdigest(),
        "boundary_normal_Y_R_S_Z": apply_boundary(relation, boundaries),
        "discarded_tail_nonzero_rows": len(tail),
        "discarded_tail_support_by_epsilon_order": tuple(sorted(tail_order.items())),
        "discarded_tail_support_by_node": tuple(sorted(tail_node.items())),
        "discarded_tail_vector_sha256": hashlib.sha256(
            repr(tuple(sorted(tail.items(), key=repr))).encode()).hexdigest(),
        "head_contact_residual_empty": True,
        "first_12_index_coefficient_monomial": tuple(
            (index, coefficient, monomials[index])
            for index, coefficient in support[:12]),
    }


def analyze_cutoff(cutoff, all_rows, monomials, groups, group_of,
                   receipt, profile, boundaries, capture_receipts=False):
    rows = tuple(row for row in all_rows if row[1][0] >= cutoff)
    row_index = {row: index for index, row in enumerate(rows)}
    matrix = nmod_mat(len(rows), len(monomials), P)
    for column, monomial in enumerate(monomials):
        for row, coefficient in literal_expansions(profile, receipt, monomial):
            index = row_index.get(row)
            if index is not None:
                matrix[index, column] = coefficient
        if (column + 1) % 1000 == 0:
            print(f"cutoff {cutoff} fill {column + 1}/{len(monomials)}",
                  file=sys.stderr, flush=True)
    print(f"cutoff {cutoff} rref {matrix.nrows()}x{matrix.ncols()}",
          file=sys.stderr, flush=True)
    _, rank = matrix.rref(inplace=True)
    pivots = Layer.pivot_columns(matrix, rank)
    pivot_set = set(pivots)
    normal_basis = {}
    contact_rank = 0
    nullity = 0
    first_gains = {}
    stages = []
    group_ends = {indices[-1] + 1: name for name, _shape, indices in groups}
    for column in range(len(monomials)):
        if column in pivot_set:
            contact_rank += 1
        else:
            nullity += 1
            relation = relation_from_rref(matrix, pivots, column)
            boundary = apply_boundary(relation, boundaries)
            if add_normal_basis(normal_basis, boundary):
                gain = len(normal_basis)
                entry = {
                    "gain": gain,
                    "ordered_column_zero_based": column,
                    "family": group_of[column],
                    "monomial_X_Y_R_S_Z": monomials[column],
                    "boundary_normal_Y_R_S_Z": boundary,
                }
                if capture_receipts:
                    entry["relation_receipt"] = head_relation_receipt(
                        relation, monomials, group_of, receipt, profile,
                        boundaries)
                first_gains[gain] = entry
        position = column + 1
        if position in group_ends:
            stages.append({
                "completed_family": group_ends[position],
                "columns_contact_rank_nullity_boundary_gain": (
                    position, contact_rank, nullity, len(normal_basis)),
            })
    assert contact_rank == rank
    result = {
        "minimum_epsilon_order": cutoff,
        "row_count": len(rows),
        "contact_rank_nullity_boundary_gain": (
            rank, len(monomials) - rank, len(normal_basis)),
        "family_stages": tuple(stages),
        "first_independent_boundary_gains": tuple(
            first_gains[gain] for gain in sorted(first_gains)),
    }
    basis_vectors = tuple(normal_basis[pivot] for pivot in sorted(normal_basis))
    del matrix
    gc.collect()
    return result, basis_vectors


def annihilator_of_rank_three(vectors):
    assert len(vectors) == 3
    matrix = nmod_mat([list(vector) for vector in vectors], P)
    kernel, nullity = matrix.nullspace()
    assert nullity == 1
    vector = tuple(int(kernel[row, 0]) % P for row in range(4))
    pivot = next(entry for entry in vector if entry)
    inverse = pow(pivot, -1, P)
    return tuple(entry * inverse % P for entry in vector)


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
    grouped = tuple(tuple(q for q in source if (q[2], q[3]) == shape)
                    for _name, shape in group_specs)
    monomials = sum(grouped, ())
    assert tuple(map(len, grouped)) == (1560, 1164, 1200, 840)
    groups = []
    group_of = {}
    offset = 0
    for (name, shape), members in zip(group_specs, grouped):
        indices = tuple(range(offset, offset + len(members)))
        groups.append((name, shape, indices))
        group_of.update({index: name for index in indices})
        offset += len(members)

    # Literal contact and formal Hasse-boundary primitive guards.
    node = receipt.nodes[0]
    assert raw_contact(RAW_R, receipt, profile.m, (node,)) == {
        (node, (0, 0, 0, 1, 0)): 1}
    assert raw_contact(RAW_S, receipt, profile.m, (node,)) == {
        (node, (0, 1, 0, 0, 0)): 1}
    assert raw_contact(RAW_Z, receipt, profile.m, (node,)) == {
        (node, (0, 0, 0, 0, 1)): 1}
    y_contact = raw_contact(RAW_Y, receipt, profile.m, (node,))
    assert y_contact.get((node, (1, 0, 0, 1, 0))) == 1
    assert y_contact.get((node, (2, 1, 0, 0, 0))) == -1 % P
    assert y_contact.get((node, (3, 0, 1, 0, 0))) == 1
    assert all(R2.formal_gradient(next(iter(raw)), receipt, profile.n) == axis
               for raw, axis in (
                   (RAW_Y, (1, 0, 0, 0)),
                   (RAW_R, (0, 1, 0, 0)),
                   (RAW_S, (0, 0, 1, 0)),
                   (RAW_Z, (0, 0, 0, 1))))

    all_rows_set = set()
    for position, monomial in enumerate(monomials, start=1):
        all_rows_set.update(row for row, _coefficient in literal_expansions(
            profile, receipt, monomial))
        if position % 1000 == 0:
            print(f"row pass {position}/{len(monomials)}",
                  file=sys.stderr, flush=True)
    all_rows = tuple(sorted(all_rows_set, key=repr))
    boundaries = tuple(R2.formal_gradient(monomial, receipt, profile.n)
                       for monomial in monomials)

    analyses = []
    bases = {}
    for cutoff in (3, 2, 1, 0):
        analysis, basis = analyze_cutoff(
            cutoff, all_rows, monomials, tuple(groups), group_of, receipt,
            profile, boundaries, capture_receipts=(cutoff == 3))
        analyses.append(analysis)
        bases[cutoff] = basis
    head = analyses[0]
    complete = analyses[-1]
    assert tuple(row["contact_rank_nullity_boundary_gain"]
                 for row in analyses) == (
                     (3663, 1101, 4), (4015, 749, 4),
                     (4367, 397, 4), (4719, 45, 3))
    assert head["contact_rank_nullity_boundary_gain"][2] == 4
    assert complete["contact_rank_nullity_boundary_gain"][2] == 3
    assert head["family_stages"][2]["completed_family"] == "S1"
    assert head["family_stages"][2][
        "columns_contact_rank_nullity_boundary_gain"][3] == 4
    assert head["first_independent_boundary_gains"][3]["family"] == "S1"
    assert head["first_independent_boundary_gains"][3][
        "monomial_X_Y_R_S_Z"] == (0, 0, 0, 1, 0)
    ell = annihilator_of_rank_three(bases[0])
    assert all(sum(a * b for a, b in zip(ell, vector)) % P == 0
               for vector in bases[0])
    head_pairings = tuple(
        (entry["gain"], entry["family"],
         sum(a * b for a, b in zip(
             ell, entry["boundary_normal_Y_R_S_Z"])) % P)
        for entry in head["first_independent_boundary_gains"])
    assert any(pairing for _gain, _family, pairing in head_pairings)

    stable = {
        "scope": (
            "exact literal formal-contact m6,L8 derivative-family head and "
            "discarded-tail attribution"
        ),
        "field": P,
        "profile_n_w_g_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "agreement_set": receipt.agreement,
        "candidate_and_tangent_degrees": (
            Old.degree(receipt.polynomial, P),
            Old.degree(receipt.tangent, P)),
        "contact_semantics": (
            "rows (eps,S,T,R,Z), Y=u0+u1Z+epsR-eps^2S+eps^3T"
        ),
        "boundary_semantics": (
            "(Y,R,S,Z)=(P,P',Hasse_2(P),gamma) at X=11"
        ),
        "group_order_counts": tuple(
            (name, shape, len(members))
            for (name, shape), members in zip(group_specs, grouped)),
        "cutoff_analyses": tuple(analyses),
        "complete_kernel_boundary_image_basis_Y_R_S_Z": bases[0],
        "complete_boundary_annihilator_ell_Y_R_S_Z": ell,
        "ell_pairing_with_first_head_gains": head_pairings,
        "verdict": (
            "GREEN finite attribution: exact family and epsilon order causing "
            "the fourth projected-head direction are identified; this is not "
            "a target-uniform producer theorem"
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
