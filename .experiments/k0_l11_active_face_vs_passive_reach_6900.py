#!/usr/bin/env python3
"""Exact ablation of the L10 -> L11 K0 repair.

The frozen degree-four receipt has function-field normal rank three at L10
and specialized rank four at L11.  The 1961 newly legal columns split into
101 columns on the new active-degree-11, Z-degree-zero face and 1860 columns
which extend passive reach on already-active shapes.  This script adjoins
exactly one part at a time to the complete L10 source and computes contact
rank and four-boundary gain at X=9.
"""

from __future__ import annotations

import argparse
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
from higher6810_secondjet_retarget_exact import relaxed_rank_bound  # noqa: E402


K0 = Degree.K0
P = Degree.P


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--support-mode", choices=("active11_z0", "other_l11"),
        required=True)
    args = parser.parse_args()
    started = time.monotonic()

    profile10 = replace(Degree.PROFILE, L=10)
    profile11 = replace(Degree.PROFILE, L=11)
    receipt = Degree.Full.M8.monomial_tangent_receipt(
        profile10, Degree.TRIAL, 0)
    assert K0.poly_degree(receipt.tangent) == 4

    source10 = set(K0.support(profile10))
    source11 = set(K0.support(profile11))
    added = source11 - source10
    active11_z0 = {
        q for q in added if q[1] + q[2] + q[3] == 11 and q[4] == 0}
    other_l11 = added - active11_z0
    assert (len(source10), len(source11), len(added),
            len(active11_z0), len(other_l11)) == (
                11178, 13139, 1961, 101, 1860)
    chosen = active11_z0 if args.support_mode == "active11_z0" else other_l11
    allowed = source10 | chosen

    full_groups, _full_order = Degree.ordered_source(profile11)
    groups = tuple(tuple(q for q in group if q in allowed)
                   for group in full_groups)
    monomials = sum(groups, ())
    assert len(monomials) == len(allowed) == len(source10) + len(chosen)

    local_bound11 = relaxed_rank_bound(
        profile11.m, profile11.L, profile11.B, profile11.s, profile11.U)
    assert local_bound11 == 1369
    matrix, boundaries = Degree.literal_contact_matrix(
        profile11, receipt, monomials)
    contact_rows = matrix.nrows()
    print(f"{args.support_mode} contact "
          f"{matrix.nrows()}x{matrix.ncols()}; rref",
          file=sys.stderr, flush=True)
    _, rank = matrix.rref(inplace=True)
    pivots = Layer.pivot_columns(matrix, rank)
    pivot_set = set(pivots)

    normal_basis = {}
    nullity = 0
    first_fourth_gain = None
    first_relation_using_chosen_last_column = None
    for position, monomial in enumerate(monomials, start=1):
        column = position - 1
        if column in pivot_set:
            continue
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
        if monomial in chosen and first_relation_using_chosen_last_column is None:
            first_relation_using_chosen_last_column = {
                "ordered_column": position,
                "monomial_X_Y_R_S_Z": monomial,
                "boundary_gain_before_after": (before, len(normal_basis)),
            }
        if len(normal_basis) == 4 and before < 4 and first_fourth_gain is None:
            first_fourth_gain = {
                "ordered_column": position,
                "monomial_X_Y_R_S_Z": monomial,
                "last_column_is_new_in_L11": monomial in chosen,
                "kernel_boundary_vector": tuple(residual),
            }

    assert nullity == len(monomials) - rank
    payload = {
        "scope": "exact frozen-receipt L11 active-face/passive-reach ablation",
        "field": "F_101",
        "support_mode": args.support_mode,
        "receipt_profile": tuple(asdict(profile10).values()),
        "source_profile": tuple(asdict(profile11).values()),
        "trial": Degree.TRIAL,
        "agreement_set": receipt.agreement,
        "candidate_and_tangent_degrees": (
            K0.poly_degree(receipt.polynomial),
            K0.poly_degree(receipt.tangent)),
        "L10_L11_added_active11_z0_other_counts": (
            len(source10), len(source11), len(added),
            len(active11_z0), len(other_l11)),
        "chosen_columns_and_L11_local_bound_margin": (
            len(monomials), local_bound11,
            len(monomials) - profile11.n * local_bound11),
        "group_counts_selected_S_R2_R3_SR": tuple(map(len, groups)),
        "contact_rows_columns_rank_nullity_boundary_gain": (
            contact_rows, len(monomials), rank, nullity, len(normal_basis)),
        "first_relation_with_chosen_last_column":
            first_relation_using_chosen_last_column,
        "first_fourth_boundary_gain": first_fourth_gain,
        "interpretation_caveat": (
            "last-column provenance is order-relative; a relation may use "
            "many earlier base and chosen columns"
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
