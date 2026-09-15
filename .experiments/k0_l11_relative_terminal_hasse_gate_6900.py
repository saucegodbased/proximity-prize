#!/usr/bin/env python3
"""Exact terminal reverse-Hasse gate for the causal L10 -> L11 repair.

The frozen F_101, m=8 receipt has boundary-normal gain three on the complete
L10 source and gain four after adjoining only the 1860 newly legal passive
L11 columns.  This script asks whether that *relative* fourth direction is
detected by restriction of compatible contact duals to the final three
reverse-Hasse rows, modulo restrictions of pure contact annihilators.

For local multiplicity eight the reverse-Hasse indices are 0,...,7, and a
literal contact row ``(node, term)`` has outer index ``term[0]``.  Thus the
target tail 44,45,46 specializes to 5,6,7.  For each terminal tail of length
one, two, and three we compute exact contact and boundary-image ranks for the
L10 base and the base plus passive layer.  No random projection is used.

It separately reports the tempting but different operation of discarding all
nonterminal primal contact equations.  The latter is not the dual quotient
used by the HRS proposal.  The full contact matrix is eliminated once, in
base-then-passive order.  RREF residuals recover boundary images of contact
kernels without allocating a huge nullspace.  All matrices are destroyed in
place so the run stays below the stated 4.2-GiB cap.
"""

from __future__ import annotations

import argparse
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
import k0_degree4_degree5_full_sr_attribution_6900 as Degree  # noqa: E402
import k0_capacity_positive_layer_attribution_6900 as Layer  # noqa: E402


K0 = Degree.K0
P = Degree.P
TAILS = ((7,), (6, 7), (5, 6, 7))


def causal_source_and_receipt():
    profile10 = replace(Degree.PROFILE, L=10)
    profile11 = replace(Degree.PROFILE, L=11)
    receipt = Degree.Full.M8.monomial_tangent_receipt(
        profile10, Degree.TRIAL, 0)
    base = tuple(K0.support(profile10))
    base_set = set(base)
    source11 = set(K0.support(profile11))
    added = source11 - base_set
    active11_z0 = {
        q for q in added if q[1] + q[2] + q[3] == 11 and q[4] == 0}
    passive = tuple(sorted(
        added - active11_z0,
        key=lambda q: ((q[2], q[3]), q[1] + q[2] + q[3], q[4], q[0])))
    assert (len(base), len(active11_z0), len(passive)) == (11178, 101, 1860)
    assert all(q[1] + q[2] + q[3] + q[4] == 11 and q[4] > 0
               for q in passive)
    return profile10, profile11, receipt, base, passive, active11_z0


def boundary_values(profile, receipt, monomials):
    return tuple(Degree.boundary_value(profile, receipt, q)
                 for q in monomials)


def row_universe(profile, receipt, monomials):
    rows = set()
    for j, monomial in enumerate(monomials, start=1):
        rows.update(row for row, _ in Degree.Full.expansions(
            profile, receipt, monomial))
        if j % 1000 == 0:
            print(f"row pass {j}/{len(monomials)}", file=sys.stderr,
                  flush=True)
    return tuple(sorted(rows, key=repr))


def fill_contact(profile, receipt, monomials, rows):
    row_index = {row: i for i, row in enumerate(rows)}
    matrix = nmod_mat(len(rows), len(monomials), P)
    for j, monomial in enumerate(monomials, start=1):
        column = j - 1
        for row, value in Degree.Full.expansions(
                profile, receipt, monomial):
            target = row_index.get(row)
            if target is not None:
                matrix[target, column] = value
        if j % 1000 == 0:
            print(f"fill pass {j}/{len(monomials)}", file=sys.stderr,
                  flush=True)
    return matrix


def stage_ranks(matrix, boundaries, base_columns):
    """Contact/kernel-boundary ranks at the base prefix and at all columns."""
    print(f"rref {matrix.nrows()}x{matrix.ncols()}", file=sys.stderr,
          flush=True)
    _, rank = matrix.rref(inplace=True)
    pivots = Layer.pivot_columns(matrix, rank)
    pivot_set = set(pivots)
    normal_basis = {}
    contact_rank = 0
    nullity = 0
    stages = {}
    for position in range(1, matrix.ncols() + 1):
        column = position - 1
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
            Degree.add_to_basis(normal_basis, tuple(residual))
        if position in (base_columns, matrix.ncols()):
            stages[position] = {
                "columns": position,
                "contact_rank": contact_rank,
                "contact_nullity": nullity,
                "kernel_boundary_rank": len(normal_basis),
                "compatible_boundary_dual_dimension": 4 - len(normal_basis),
            }
    assert contact_rank == rank
    return stages


def relative_receipt(label, indices, rows, stages, base_columns,
                     passive_columns):
    old = stages[base_columns]
    new = stages[base_columns + passive_columns]
    contact_increment = new["contact_rank"] - old["contact_rank"]
    augmented_increment = (
        new["contact_rank"] + new["kernel_boundary_rank"]
        - old["contact_rank"] - old["kernel_boundary_rank"])
    relative_domain_dimension = passive_columns - contact_increment
    connecting_rank = augmented_increment - contact_increment
    assert connecting_rank == (
        new["kernel_boundary_rank"] - old["kernel_boundary_rank"])
    return {
        "projection": label,
        "reverse_Hasse_indices": indices,
        "literal_contact_rows": len(rows),
        "L10_base": old,
        "L10_plus_passive": new,
        "passive_contact_rank_increment": contact_increment,
        "relative_compatible_domain_dimension": relative_domain_dimension,
        "relative_connecting_rank": connecting_rank,
        "relative_connecting_kernel_dimension": (
            relative_domain_dimension - connecting_rank),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--mode", choices=("all", "head-only"), default="all",
        help=("head-only runs the dual counterexample gate for indices 5,6,7 "
              "without rebuilding the complete contact RREF"))
    args = parser.parse_args()
    started = time.monotonic()
    (profile10, profile11, receipt, base, passive,
     active11_z0) = causal_source_and_receipt()
    monomials = base + passive
    boundaries = boundary_values(profile11, receipt, monomials)
    all_rows = row_universe(profile11, receipt, monomials)
    row_counts = {
        j: sum(1 for _node, term in all_rows if term[0] == j)
        for j in range(profile11.m)
    }
    assert set(row_counts) == set(range(8))

    # A compatible dual pair obeys C_old^T eta = B_old^T ell.  It has zero
    # terminal coordinates precisely when eta is supported on the head rows
    # 0,...,4.  Such a pair with ell != 0 exists iff the boundary image of
    # ker(C_old projected to the head) is not all four-dimensional.  This is
    # the basis-free direct falsifier requested by the three-moment proposal.
    head_indices = tuple(range(5))
    head_rows = tuple(row for row in all_rows
                      if row[1][0] in head_indices)
    head_matrix = fill_contact(
        profile11, receipt, monomials, head_rows)
    head_stages = stage_ranks(head_matrix, boundaries, len(base))
    head = relative_receipt(
        "head/complement of final-three tail", head_indices, head_rows,
        head_stages, len(base), len(passive))
    del head_matrix
    gc.collect()
    old_nonzero_dual_with_zero_last_three_exists = (
        head["L10_base"]["compatible_boundary_dual_dimension"] > 0)

    if args.mode == "head-only":
        payload = {
            "scope": "dual last-three counterexample gate only",
            "field": "F_101",
            "head_projection": head,
            "nonzero_old_compatible_boundary_dual_with_zero_last_three_exists":
                old_nonzero_dual_with_zero_last_three_exists,
        }
        canonical = json.dumps(
            payload, sort_keys=True, separators=(",", ":"))
        payload["canonical_sha256"] = hashlib.sha256(
            canonical.encode()).hexdigest()
        payload["runtime"] = {
            "seconds": round(time.monotonic() - started, 3),
            "peak_rss_kib": resource.getrusage(
                resource.RUSAGE_SELF).ru_maxrss,
        }
        print(json.dumps(payload, indent=2, sort_keys=True))
        return

    projected = []
    for indices in TAILS:
        selected = tuple(row for row in all_rows if row[1][0] in indices)
        matrix = fill_contact(
            profile11, receipt, monomials, selected)
        stages = stage_ranks(matrix, boundaries, len(base))
        projected.append(relative_receipt(
            f"terminal tail length {len(indices)}", indices, selected,
            stages, len(base), len(passive)))
        del matrix
        gc.collect()

    # The full exact gate is last.  Its matrix is the only large allocation.
    matrix = fill_contact(profile11, receipt, monomials, all_rows)
    stages = stage_ranks(matrix, boundaries, len(base))
    full = relative_receipt(
        "complete contact", tuple(range(8)), all_rows, stages,
        len(base), len(passive))
    del matrix
    gc.collect()

    last_three = projected[-1]
    same_old_boundary_image = (
        last_three["L10_base"]["kernel_boundary_rank"] ==
        full["L10_base"]["kernel_boundary_rank"])
    same_new_boundary_image = (
        last_three["L10_plus_passive"]["kernel_boundary_rank"] ==
        full["L10_plus_passive"]["kernel_boundary_rank"])
    same_connecting_rank = (
        last_three["relative_connecting_rank"] ==
        full["relative_connecting_rank"])

    # Since ker(C_full) is contained in ker(C_tail), equality of the two old
    # boundary-image dimensions proves equality of the actual old boundary
    # subspaces.  On the full relative domain the two connecting maps then
    # have the same quotient target and the same value.  This makes equality
    # of their kernels a theorem of the rank receipt, not a basis heuristic.
    support_only_tail_preserves_primal_map = (
        same_old_boundary_image and same_new_boundary_image and
        same_connecting_rank and full["relative_connecting_rank"] == 1)

    old_full = full["L10_base"]
    old_head = head["L10_base"]
    pure_contact_dual_dimension = (
        len(all_rows) - old_full["contact_rank"])
    compatible_pair_dimension = (
        pure_contact_dual_dimension +
        old_full["compatible_boundary_dual_dimension"])
    pure_dual_tail_kernel_dimension = (
        len(head_rows) - old_head["contact_rank"])
    pure_dual_tail_image_rank = (
        pure_contact_dual_dimension - pure_dual_tail_kernel_dimension)
    compatible_tail_kernel_dimension = (
        pure_dual_tail_kernel_dimension +
        old_head["compatible_boundary_dual_dimension"])
    compatible_tail_image_rank = (
        compatible_pair_dimension - compatible_tail_kernel_dimension)
    induced_tail_quotient_rank = (
        compatible_tail_image_rank - pure_dual_tail_image_rank)
    induced_tail_quotient_kernel_dimension = (
        old_full["compatible_boundary_dual_dimension"] -
        induced_tail_quotient_rank)
    assert induced_tail_quotient_rank in (0, 1)
    assert induced_tail_quotient_kernel_dimension in (0, 1)
    dual_tail_detects_connecting_direction = (
        induced_tail_quotient_rank == 1 and
        induced_tail_quotient_kernel_dimension == 0 and
        full["relative_connecting_rank"] == 1)

    def rank_tuple(stage):
        return (stage["contact_rank"], stage["contact_nullity"],
                stage["kernel_boundary_rank"])

    assert rank_tuple(full["L10_base"]) == (10861, 317, 3)
    assert rank_tuple(full["L10_plus_passive"]) == (12321, 717, 4)
    assert full["relative_compatible_domain_dimension"] == 400
    assert full["relative_connecting_rank"] == 1
    assert rank_tuple(head["L10_base"]) == (7029, 4149, 4)
    assert rank_tuple(head["L10_plus_passive"]) == (7911, 5127, 4)
    assert tuple((rank_tuple(row["L10_base"]),
                  rank_tuple(row["L10_plus_passive"]),
                  row["relative_connecting_rank"])
                 for row in projected) == (
        ((1890, 9288, 4), (2205, 10833, 4), 0),
        ((3645, 7533, 4), (4230, 8808, 4), 0),
        ((4995, 6183, 4), (5760, 7278, 4), 0),
    )
    assert (pure_contact_dual_dimension, compatible_pair_dimension,
            pure_dual_tail_kernel_dimension, pure_dual_tail_image_rank,
            compatible_tail_kernel_dimension, compatible_tail_image_rank,
            induced_tail_quotient_rank,
            induced_tail_quotient_kernel_dimension) == (
                5699, 5700, 3573, 2126, 3573, 2127, 1, 0)
    assert dual_tail_detects_connecting_direction

    payload = {
        "scope": (
            "exact F101 m8 L10 base to passive-only L11 relative connecting "
            "map, projected to terminal reverse-Hasse contact rows"
        ),
        "field": "F_101",
        "receipt_profile": tuple(asdict(profile10).values()),
        "source_profile": tuple(asdict(profile11).values()),
        "trial": Degree.TRIAL,
        "agreement_set": receipt.agreement,
        "candidate_and_tangent_degrees": (
            K0.poly_degree(receipt.polynomial),
            K0.poly_degree(receipt.tangent)),
        "base_passive_active11_z0_counts": (
            len(base), len(passive), len(active11_z0)),
        "active11_z0_excluded": True,
        "outer_index_semantics": (
            "term[0] is the outer T/Hasse index; depth m=8 gives indices "
            "0..7, so the exact analogue of target 44,45,46 is 5,6,7"
        ),
        "contact_row_counts_by_outer_index": row_counts,
        "complete_relative_map": full,
        "terminal_tail_projections": projected,
        "head_complement_projection": head,
        "dual_last_three_detection": {
            "nonzero_old_compatible_boundary_dual_with_zero_last_three_exists":
                old_nonzero_dual_with_zero_last_three_exists,
            "last_three_zero_forces_boundary_dual_zero":
                not old_nonzero_dual_with_zero_last_three_exists,
            "pure_contact_dual_dimension": pure_contact_dual_dimension,
            "compatible_dual_pair_dimension": compatible_pair_dimension,
            "pure_dual_last_three_projection_kernel_dimension":
                pure_dual_tail_kernel_dimension,
            "pure_dual_last_three_image_rank": pure_dual_tail_image_rank,
            "compatible_pair_last_three_projection_kernel_dimension":
                compatible_tail_kernel_dimension,
            "compatible_pair_last_three_image_rank":
                compatible_tail_image_rank,
            "induced_last_three_quotient_rank_mod_pure_contact_duals":
                induced_tail_quotient_rank,
            "induced_last_three_quotient_kernel_dimension":
                induced_tail_quotient_kernel_dimension,
            "full_relative_connecting_transpose_rank_and_kernel_dimension": (
                full["relative_connecting_rank"],
                old_full["compatible_boundary_dual_dimension"] -
                full["relative_connecting_rank"]),
            "induced_tail_and_full_connecting_kernels_agree":
                dual_tail_detects_connecting_direction,
            "logic": (
                "C_old^T eta = B_old^T ell with eta_tail=0 is exactly the "
                "adjoint compatibility equation for the head-projected "
                "contact map. Quotienting the terminal projection by the "
                "terminal projections of pure contact annihilators makes it "
                "well-defined on compatible boundary-dual classes. Its rank "
                "is dim(proj_tail compatible pairs)-dim(proj_tail pure "
                "duals), computed exactly by rank-nullity from the full and "
                "head contact ranks."
            ),
        },
        "support_only_tail_projection_diagnostic": {
            "same_old_kernel_boundary_image": same_old_boundary_image,
            "same_extended_kernel_boundary_image": same_new_boundary_image,
            "same_relative_connecting_rank": same_connecting_rank,
            "preserves_complete_primal_relative_map":
                support_only_tail_preserves_primal_map,
            "logic": (
                "ker full-contact is contained in ker tail-contact. Equal old "
                "boundary-image dimensions therefore give the same actual "
                "boundary quotient; the tail connecting map restricted to "
                "the complete relative domain is then literally the full "
                "map, so their kernels agree there"
            ),
        },
        "verdict": (
            "GREEN finite dual-tail detector" if
            dual_tail_detects_connecting_direction else
            "RED finite dual-tail detector"
        ),
        "scope_caveat": (
            "This is one frozen finite chamber. GREEN would validate the "
            "three-tail mechanism here, not prove the target m47 raw-source "
            "realization theorem. The target still needs a uniform theorem "
            "producing its three terminal aggregate adjoint equations."
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
