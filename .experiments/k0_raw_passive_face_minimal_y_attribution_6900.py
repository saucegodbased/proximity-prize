#!/usr/bin/env python3
"""Locate the first Y-degree in the raw positive-Z face repairing K0 rank 4.

The base is the corrected formal-contact m6,L8 source.  We append only the
new L9 raw face (R=S=0), ordered by increasing Y exponent.  One exact contact
RREF reconstructs every prefix kernel and its formal-Hasse boundary image.
The first fourth normal is emitted with a canonical source receipt.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import asdict, replace
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
from k0_centered_head_y_correction_gate_6900 import (  # noqa: E402
    P, flattened_raw_column,
)
from k0_literal_flat_strong_cap_probe_6900 import (  # noqa: E402
    formal_gradient_vector,
)


FOUR_POINT_TWO_GB = 4_200_000_000
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
if soft < 0 or soft > FOUR_POINT_TWO_GB:
    resource.setrlimit(resource.RLIMIT_AS, (FOUR_POINT_TWO_GB, hard))


def expansions(profile, receipt, monomial):
    for node in receipt.nodes:
        for local, coefficient in flattened_raw_column(
                monomial, node, receipt.u0[node], receipt.u1[node],
                profile.m).items():
            if coefficient:
                yield (node, local), coefficient


def add_basis(basis, vector):
    value = list(vector)
    for pivot in sorted(basis):
        factor = value[pivot]
        if factor:
            value = [
                (entry - factor * basis[pivot][coordinate]) % P
                for coordinate, entry in enumerate(value)
            ]
    pivot = next((i for i, entry in enumerate(value) if entry), None)
    if pivot is None:
        return False
    inverse = pow(value[pivot], -1, P)
    basis[pivot] = tuple(entry * inverse % P for entry in value)
    return True


def boundary_of_relation(relation, boundaries):
    return tuple(
        sum(coefficient * boundaries[index][coordinate]
            for index, coefficient in relation.items()) % P
        for coordinate in range(4)
    )


def main():
    started = time.monotonic()
    profile8 = Old.K0.Profile(11, 5, 8, 6, 2, 1, 8, 8, 0, 1)
    profile9 = replace(profile8, L=9)
    receipt = Old.make_custom_receipt(
        profile8, P, 0, "random", "mid", "minimal", "arbitrary",
        "alternating", 2)
    base = tuple(Old.K0.support(profile8))
    base_set = set(base)
    full9 = set(Old.K0.support(profile9))
    raw_face = tuple(q for q in full9 - base_set
                     if q[2] == 0 and q[3] == 0)
    groups = tuple(
        (y, tuple(sorted((q for q in raw_face if q[1] == y),
                         key=lambda q: (q[4], q[0]))))
        for y in sorted(set(q[1] for q in raw_face)))
    assert tuple((y, len(group)) for y, group in groups) == (
        (0, 48), (1, 43), (2, 38), (3, 33), (4, 28),
        (5, 23), (6, 18), (7, 13), (8, 8))
    face = sum((group for _y, group in groups), ())
    assert len(base) == 4764 and len(face) == 252
    assert all(y + z == 9 and z > 0
               for _x, y, _r, _s, z in face)
    monomials = base + face
    boundaries = tuple(
        formal_gradient_vector(q, receipt, profile9.n) for q in monomials)

    rows_set = set()
    for position, monomial in enumerate(monomials, start=1):
        rows_set.update(row for row, _value in expansions(
            profile9, receipt, monomial))
        if position % 1000 == 0:
            print(f"row pass {position}/{len(monomials)}",
                  file=sys.stderr, flush=True)
    rows = tuple(sorted(rows_set, key=repr))
    row_index = {row: i for i, row in enumerate(rows)}
    matrix = nmod_mat(len(rows), len(monomials), P)
    for column, monomial in enumerate(monomials):
        for row, coefficient in expansions(profile9, receipt, monomial):
            matrix[row_index[row], column] = coefficient
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
    assert rank == 4950

    group_ends = {}
    end = len(base)
    for y, group in groups:
        end += len(group)
        group_ends[end] = y
    normal_basis = {}
    contact_rank = 0
    nullity = 0
    stages = []
    first_fourth = None
    for column in range(len(monomials)):
        if column in pivot_set:
            contact_rank += 1
        else:
            nullity += 1
            relation = {column: 1}
            for row, pivot_column in enumerate(pivots):
                coefficient = int(matrix[row, column]) % P
                if coefficient:
                    # Leftmost-pivot elimination must express a prefix
                    # dependency using only earlier pivot columns.
                    assert pivot_column < column
                    relation[pivot_column] = (-coefficient) % P
            boundary = boundary_of_relation(relation, boundaries)
            if add_basis(normal_basis, boundary) and len(normal_basis) == 4:
                support = tuple(sorted(relation.items()))
                face_support = tuple(
                    (index, coefficient, monomials[index])
                    for index, coefficient in support if index >= len(base))
                first_fourth = {
                    "ordered_column_zero_based": column,
                    "last_monomial_X_Y_R_S_Z": monomials[column],
                    "boundary_normal_Y_R_S_Z": boundary,
                    "relation_support_size": len(support),
                    "base_and_new_face_support_counts": (
                        sum(index < len(base) for index, _ in support),
                        len(face_support)),
                    "new_face_support_by_Y": tuple(sorted(Counter(
                        monomial[1] for _index, _coefficient, monomial
                        in face_support).items())),
                    "new_face_X_support_by_Y": tuple(
                        (y, tuple(monomial[0]
                                  for _index, _coefficient, monomial
                                  in face_support if monomial[1] == y))
                        for y in sorted(set(monomial[1]
                            for _index, _coefficient, monomial
                            in face_support))),
                    "new_face_missing_X_by_Y": tuple(
                        (y, tuple(sorted(
                            set(q[0] for q in group) -
                            set(monomial[0]
                                for _index, _coefficient, monomial
                                in face_support if monomial[1] == y))))
                        for y, group in groups if y <= monomials[column][1]),
                    "new_face_Y_range": (
                        min(monomial[1] for _index, _coefficient, monomial
                            in face_support),
                        max(monomial[1] for _index, _coefficient, monomial
                            in face_support)),
                    "relation_source_sha256": hashlib.sha256(
                        repr(support).encode()).hexdigest(),
                    "first_16_new_face_terms": face_support[:16],
                    "pairing_with_complete_annihilator_1_74_26_77":
                        sum(a * b for a, b in zip(
                            (1, 74, 26, 77), boundary)) % P,
                }
        position = column + 1
        if position == len(base) or position in group_ends:
            stages.append({
                "stage": "L8_base" if position == len(base)
                         else f"through_raw_face_Y{group_ends[position]}",
                "columns_contact_rank_nullity_boundary_gain": (
                    position, contact_rank, nullity, len(normal_basis)),
            })

    assert first_fourth is not None
    assert stages[0]["columns_contact_rank_nullity_boundary_gain"] == (
        4764, 4719, 45, 3)
    assert stages[-1]["columns_contact_rank_nullity_boundary_gain"] == (
        5016, 4950, 66, 4)
    stable = {
        "scope": (
            "exact corrected formal-contact L8 base plus raw-only positive-Z "
            "L9 face, increasing-Y attribution"),
        "field": P,
        "base_profile": tuple(asdict(profile8).values()),
        "extended_profile": tuple(asdict(profile9).values()),
        "agreement_set": receipt.agreement,
        "contact_semantics": (
            "rows(eps,S,T,R,Z), Y=u0+u1Z+epsR-eps^2S+eps^3T"),
        "boundary_semantics": "(Y,R,S,Z)=(P,P',Hasse2(P),gamma)",
        "raw_face_group_counts_by_Y": tuple(
            (y, len(group)) for y, group in groups),
        "prefix_stages": tuple(stages),
        "first_fourth_boundary_direction": first_fourth,
        "scope_guard": (
            "prefix minimality is for increasing Y order on one exact F101 "
            "receipt; it is not target-uniform or subset-minimal"),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    payload = {
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "runtime": {
            "seconds": round(time.monotonic() - started, 3),
            "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            "address_space_cap_bytes": FOUR_POINT_TWO_GB,
        },
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
