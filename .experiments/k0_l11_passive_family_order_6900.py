#!/usr/bin/env python3
"""Exact family/active-degree ordering of the causal L11 passive scaffold.

The complete L10 source is placed first.  The 1860 causal L11 additions all
have passive total ``Y+R+S+Z=11`` and exclude every new active-11, Z=0
column.  They are then ordered by derivative family

    raw 1, raw R, raw S, R^2, R^3, S*R

and inside each family by active degree, Z degree, and X degree.  A single
exact contact RREF reports rank/nullity/boundary gain after every family and
active-degree band.  First pivots are relative to this explicit ordering.
"""

from __future__ import annotations

from dataclasses import asdict, replace
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

sys.path.insert(0, ".experiments")
import k0_degree4_degree5_full_sr_attribution_6900 as Degree  # noqa: E402
import k0_capacity_positive_layer_attribution_6900 as Layer  # noqa: E402


K0 = Degree.K0
P = Degree.P
FAMILIES = (
    ("raw_1", (0, 0)),
    ("raw_R", (1, 0)),
    ("raw_S", (0, 1)),
    ("R2", (2, 0)),
    ("R3", (3, 0)),
    ("S_R", (1, 1)),
)


def main():
    started = time.monotonic()
    profile10 = replace(Degree.PROFILE, L=10)
    profile11 = replace(Degree.PROFILE, L=11)
    receipt = Degree.Full.M8.monomial_tangent_receipt(
        profile10, Degree.TRIAL, 0)
    base = K0.support(profile10)
    base_set = set(base)
    source11 = set(K0.support(profile11))
    added = source11 - base_set
    active11_z0 = {
        q for q in added if q[1] + q[2] + q[3] == 11 and q[4] == 0}
    passive = added - active11_z0
    assert (len(base), len(source11), len(active11_z0), len(passive)) == (
        11178, 13139, 101, 1860)
    assert not (passive & active11_z0)
    assert all(q[1] + q[2] + q[3] + q[4] == 11 and q[4] > 0
               for q in passive)

    family_groups = []
    for name, shape in FAMILIES:
        group = tuple(sorted(
            (q for q in passive if (q[2], q[3]) == shape),
            key=lambda q: (q[1] + q[2] + q[3], q[4], q[0])))
        family_groups.append((name, group))
    assert tuple(len(group) for _, group in family_groups) == (
        363, 325, 335, 288, 252, 297)
    assert set().union(*(set(group) for _, group in family_groups)) == passive
    monomials = base + sum((group for _, group in family_groups), ())
    assert len(monomials) == 13038

    family_ends = []
    band_ends = []
    position = len(base)
    for name, group in family_groups:
        active_values = sorted({q[1] + q[2] + q[3] for q in group})
        for active in active_values:
            position += sum(1 for q in group
                            if q[1] + q[2] + q[3] == active)
            band_ends.append((position, name, active))
        family_ends.append((position, name))
    assert position == len(monomials)

    matrix, boundaries = Degree.literal_contact_matrix(
        profile11, receipt, monomials)
    contact_rows = matrix.nrows()
    print(f"passive family order contact "
          f"{matrix.nrows()}x{matrix.ncols()}; rref",
          file=sys.stderr, flush=True)
    _, rank = matrix.rref(inplace=True)
    pivots = Layer.pivot_columns(matrix, rank)
    pivot_set = set(pivots)

    normal_basis = {}
    contact_rank = 0
    nullity = 0
    first_gain = {}
    relative_relation_receipts = {}
    family_table = []
    band_table = []
    family_end_map = {end: name for end, name in family_ends}
    band_end_map = {end: (name, active)
                    for end, name, active in band_ends}
    for source_position, monomial in enumerate(monomials, start=1):
        column = source_position - 1
        if column in pivot_set:
            contact_rank += 1
        else:
            nullity += 1
            residual = list(boundaries[column])
            for row, pivot_column in enumerate(pivots):
                coefficient = int(matrix[row, column]) % P
                if coefficient:
                    pivot_boundary = boundaries[pivot_column]
                    residual = [
                        (entry - coefficient * pivot_boundary[i]) % P
                        for i, entry in enumerate(residual)
                    ]
            before = len(normal_basis)
            Degree.add_to_basis(normal_basis, tuple(residual))
            if source_position > len(base) and (
                    "first_passive_dependency" not in
                    relative_relation_receipts or
                    (before == 3 and len(normal_basis) == 4)):
                relation_support = [(monomial, 1)]
                repair_counts = {"L10_base": 0}
                repair_counts.update({name: 0 for name, _shape in FAMILIES})
                for row, pivot_column in enumerate(pivots):
                    coefficient = (-int(matrix[row, column])) % P
                    if not coefficient:
                        continue
                    pivot_monomial = monomials[pivot_column]
                    relation_support.append((pivot_monomial, coefficient))
                    if pivot_column < len(base):
                        repair_counts["L10_base"] += 1
                    else:
                        repair_family = next(
                            name for name, shape in FAMILIES
                            if (pivot_monomial[2], pivot_monomial[3]) == shape)
                        repair_counts[repair_family] += 1
                relation_support_tuple = tuple(sorted(relation_support))
                relation_payload = {
                    "ordered_column": source_position,
                    "new_passive_monomial_X_Y_R_S_Z": monomial,
                    "contact_repair_uses_only_earlier_columns": all(
                        pivot_column < column
                        for row, pivot_column in enumerate(pivots)
                        if int(matrix[row, column]) % P),
                    "relation_support_size": len(relation_support_tuple),
                    "repair_support_counts": repair_counts,
                    "relation_support_sha256": hashlib.sha256(
                        repr(relation_support_tuple).encode()).hexdigest(),
                    "boundary_after_contact_repair": tuple(residual),
                    "boundary_rank_before_and_after": (
                        before, len(normal_basis)),
                }
                if "first_passive_dependency" not in relative_relation_receipts:
                    relative_relation_receipts["first_passive_dependency"] = (
                        relation_payload)
                if before == 3 and len(normal_basis) == 4:
                    relative_relation_receipts[
                        "first_passive_fourth_normal"] = relation_payload
            if len(normal_basis) > before:
                family = "L10_base"
                active = monomial[1] + monomial[2] + monomial[3]
                if source_position > len(base):
                    family = next(
                        name for name, shape in FAMILIES
                        if (monomial[2], monomial[3]) == shape)
                first_gain[len(normal_basis)] = {
                    "ordered_column": source_position,
                    "family": family,
                    "active_degree": active,
                    "monomial_X_Y_R_S_Z": monomial,
                    "last_column_is_new_passive": monomial in passive,
                    "kernel_boundary_vector": tuple(residual),
                }
        if source_position == len(base):
            family_table.append((
                "L10_base", source_position, contact_rank, nullity,
                len(normal_basis)))
        if source_position in band_end_map:
            name, active = band_end_map[source_position]
            band_table.append((
                name, active, source_position, contact_rank, nullity,
                len(normal_basis)))
        if source_position in family_end_map:
            family_table.append((
                family_end_map[source_position], source_position,
                contact_rank, nullity, len(normal_basis)))

    assert (contact_rank, nullity, len(normal_basis)) == (12321, 717, 4)
    payload = {
        "scope": "exact causal L11 passive scaffold family/degree ordering",
        "field": "F_101",
        "receipt_profile": tuple(asdict(profile10).values()),
        "source_profile": tuple(asdict(profile11).values()),
        "trial": Degree.TRIAL,
        "agreement_set": receipt.agreement,
        "candidate_and_tangent_degrees": (
            K0.poly_degree(receipt.polynomial),
            K0.poly_degree(receipt.tangent)),
        "active11_z0_columns_excluded": len(active11_z0),
        "L10_base_and_passive_addition_counts": (len(base), len(passive)),
        "passive_family_order_and_counts": tuple(
            (name, len(group)) for name, group in family_groups),
        "contact_rows_columns_rank_nullity_boundary_gain": (
            contact_rows, len(monomials), contact_rank, nullity,
            len(normal_basis)),
        "family_columns_contact_rank_nullity_gain": family_table,
        "band_family_active_columns_contact_rank_nullity_gain": band_table,
        "first_boundary_gain_1_through_4": first_gain,
        "relative_connecting_relation_receipts":
            relative_relation_receipts,
        "ordering_caveat": (
            "first means L10 base then the stated family/active-degree order; "
            "relations may use many earlier columns"
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
