#!/usr/bin/env python3
"""Faithful exact gate for the K0 final-three connecting transpose.

The historical L10 -> L11 receipt selected the compressed oracle's free
Taylor exponent ``q`` and evaluated the boundary at ordinary ``P''``.  Both
choices were wrong for the accepted formal map.  This replay computes ranks
from the literal substitution

    X = x + eps,
    Y = u0 + u1*Z + eps*R - eps^2*S + eps^3*T  (mod eps^m)

and the boundary point ``(Y,R,S,Z)=(P,P',Hasse_2(P),gamma)``.  The final
three rows are the *high* ordinary epsilon orders ``m-3,m-2,m-1``.  For an
independent semantic guard, sampled compressed rows are mapped by

    (q,E,V1,V2,Z) -> (eps=q+3*E,S=V2,T=E,R=V1,Z)

and checked coefficientwise against the literal columns.

For an old complete contact map C with boundary map B, let I be the boundary
image B(ker C).  The script reports separately

* ``dim Boundary/I``;
* the rank of the relative passive-layer connecting transpose; and
* the rank of terminal restriction modulo restricted pure contact duals.

The last rank is exactly ``rank(B(ker C_head))-rank(I)``, where ``C_head``
retains the complement of the final three epsilon orders.  Equality of the
two transpose kernels is checked by equality of the corresponding boundary
image subspaces, not inferred merely from equal ranks.

All arithmetic is exact over F_101.  This is finite evidence only, never a
target-size rank theorem.  A hard 4.2 GB address-space cap is installed.
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
import k0_capacity_positive_layer_attribution_6900 as Layer  # noqa: E402
import k0_degree4_degree5_full_sr_attribution_6900 as Degree  # noqa: E402
import k0_first_positive_passive_universal_falsifier_6900 as Old  # noqa: E402
import k0_flattened_contact_sweep_regression_6900 as Flat  # noqa: E402
from higher_jet_literal_matrix import translated_column  # noqa: E402


P = 101
ADDRESS_SPACE_CAP_BYTES = 4_200_000_000
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
if soft < 0 or soft > ADDRESS_SPACE_CAP_BYTES:
    resource.setrlimit(
        resource.RLIMIT_AS, (ADDRESS_SPACE_CAP_BYTES, hard))


Row = tuple[int, int, int, int, int, int]
BoundaryVector = tuple[int, int, int, int]


def add_boundary_basis(
        basis: dict[int, BoundaryVector], source: BoundaryVector,
        p: int = P) -> bool:
    """Insert into a deterministic four-dimensional row-echelon basis."""
    vector = list(source)
    for pivot in sorted(basis):
        factor = vector[pivot]
        if factor:
            old = basis[pivot]
            vector = [
                (entry - factor * old[i]) % p
                for i, entry in enumerate(vector)
            ]
    pivot = next((i for i, entry in enumerate(vector) if entry), None)
    if pivot is None:
        return False
    inverse = pow(vector[pivot], -1, p)
    basis[pivot] = tuple(entry * inverse % p for entry in vector)
    return True


def basis_vectors(basis: dict[int, BoundaryVector]) -> tuple[BoundaryVector, ...]:
    return tuple(basis[pivot] for pivot in sorted(basis))


def span_rank(*families: tuple[BoundaryVector, ...]) -> int:
    basis: dict[int, BoundaryVector] = {}
    for vector in sum(families, ()):
        add_boundary_basis(basis, vector)
    return len(basis)


def same_span(left: tuple[BoundaryVector, ...],
              right: tuple[BoundaryVector, ...]) -> bool:
    return (len(left) == len(right) and
            span_rank(left, right) == len(left))


def formal_column(profile, receipt, monomial) -> dict[Row, int]:
    """Actual flattened formal contact, with explicit epsilon exponent."""
    column = Flat.flattened_column(profile, receipt, monomial, P)
    assert all(0 <= row[1] < profile.m for row in column)
    return column


def formal_boundary(profile, receipt, monomial) -> BoundaryVector:
    """Gradient in script order (Y,R,S,Z), with S=Hasse_2(P)."""
    return Flat.formal_boundary_gradient(
        monomial, receipt, profile.n, P)


def mapped_compressed_node_column(profile, receipt, monomial, node):
    """Compressed oracle conjugated to literal formal row/column scales."""
    xp, yp, rp, sp, zp = monomial
    answer = {}
    compressed = translated_column(
        xp, (yp, rp, sp), zp, node, receipt.u0[node], receipt.u1[node],
        profile.m, 2, P)
    for (q, error_power, v1, v2, z), value in compressed.items():
        epsilon = q + 3 * error_power
        assert epsilon < profile.m
        row = (node, epsilon, v2, error_power, v1, z)
        coefficient = value * pow(2, v2 - sp, P) % P
        updated = (answer.get(row, 0) + coefficient) % P
        if updated:
            answer[row] = updated
        else:
            answer.pop(row, None)
    return answer


def semantic_sanity(profile, receipt, monomials) -> dict[str, object]:
    """Check signs, Hasse boundary, and q+3E on deterministic samples."""
    node = receipt.nodes[0]
    primitives = {
        "Y": (0, 1, 0, 0, 0),
        "R": (0, 0, 1, 0, 0),
        "S": (0, 0, 0, 1, 0),
        "Z": (0, 0, 0, 0, 1),
    }
    y = formal_column(profile, receipt, primitives["Y"])
    expected_y = {
        (node, 0, 0, 0, 0, 0): receipt.u0[node] % P,
        (node, 0, 0, 0, 0, 1): receipt.u1[node] % P,
        (node, 1, 0, 0, 1, 0): 1,
        (node, 2, 1, 0, 0, 0): -1 % P,
        (node, 3, 0, 1, 0, 0): 1,
    }
    expected_y = {row: value for row, value in expected_y.items() if value}
    # Restrict the global literal column to the selected node before checking.
    assert {row: value for row, value in y.items() if row[0] == node} == \
        expected_y
    expected_primitives = {
        "R": {(node, 0, 0, 0, 1, 0): 1},
        "S": {(node, 0, 1, 0, 0, 0): 1},
        "Z": {(node, 0, 0, 0, 0, 1): 1},
    }
    for label in ("R", "S", "Z"):
        actual = formal_column(profile, receipt, primitives[label])
        actual = {row: value for row, value in actual.items()
                  if row[0] == node}
        assert actual == expected_primitives[label]

    # Boundary coordinates are (Y,R,S,Z).  The point used internally has
    # S=P''/2; primitive gradients check the coordinate normalization.
    assert formal_boundary(profile, receipt, primitives["Y"]) == (1, 0, 0, 0)
    assert formal_boundary(profile, receipt, primitives["R"]) == (0, 1, 0, 0)
    assert formal_boundary(profile, receipt, primitives["S"]) == (0, 0, 1, 0)
    assert formal_boundary(profile, receipt, primitives["Z"]) == (0, 0, 0, 1)
    hasse2 = Old.evaluate(receipt.polynomial, profile.n, P, 2) \
        * pow(2, -1, P) % P

    candidates = list(primitives.values())
    if monomials:
        positions = {
            0, len(monomials) // 7, len(monomials) // 3,
            len(monomials) // 2, 2 * len(monomials) // 3,
            6 * len(monomials) // 7, len(monomials) - 1,
        }
        candidates.extend(monomials[i] for i in sorted(positions))
    tested = 0
    for monomial in dict.fromkeys(candidates):
        literal = formal_column(profile, receipt, monomial)
        literal_node = {row: value for row, value in literal.items()
                        if row[0] == node}
        mapped = mapped_compressed_node_column(
            profile, receipt, monomial, node)
        assert mapped == literal_node
        tested += 1
    return {
        "literal_Y_sign_pattern": (
            "u0+u1*Z+eps*R-eps^2*S+eps^3*T"),
        "boundary_order_and_second_jet": (
            "(Y,R,S,Z), S=Hasse2(P)=P''/2"),
        "boundary_Hasse2_value_at_Xn": hasse2,
        "compressed_formal_row_map": (
            "(q,E,V1,V2,Z)->(eps=q+3E,S=V2,T=E,R=V1,Z)"),
        "sampled_node_columns_checked_coefficientwise": tested,
    }


def row_universes(profile, receipt, old_monomials, passive_monomials):
    old_rows = set()
    all_rows = set()
    combined = old_monomials + passive_monomials
    for position, monomial in enumerate(combined, start=1):
        rows = set(formal_column(profile, receipt, monomial))
        all_rows.update(rows)
        if position <= len(old_monomials):
            old_rows.update(rows)
        if position % 1000 == 0:
            print(f"row pass {position}/{len(combined)}", file=sys.stderr,
                  flush=True)
    return tuple(sorted(old_rows, key=repr)), tuple(sorted(all_rows, key=repr))


def fill_contact(profile, receipt, monomials, rows, label):
    row_index = {row: i for i, row in enumerate(rows)}
    matrix = nmod_mat(len(rows), len(monomials), P)
    for j, monomial in enumerate(monomials, start=1):
        for row, value in formal_column(profile, receipt, monomial).items():
            i = row_index.get(row)
            if i is not None:
                matrix[i, j - 1] = value
        if j % 1000 == 0:
            print(f"fill {label} {j}/{len(monomials)}", file=sys.stderr,
                  flush=True)
    return matrix


def stage_ranks(matrix, boundaries, checkpoints, label):
    """Exact contact and kernel-boundary ranks for ordered prefixes."""
    print(f"rref {label}: {matrix.nrows()}x{matrix.ncols()}",
          file=sys.stderr, flush=True)
    _, rank = matrix.rref(inplace=True)
    pivots = Layer.pivot_columns(matrix, rank)
    pivot_set = set(pivots)
    contact_rank = 0
    normal_basis: dict[int, BoundaryVector] = {}
    stages = {}
    checkpoints = set(checkpoints)
    for position in range(1, matrix.ncols() + 1):
        column = position - 1
        if column in pivot_set:
            contact_rank += 1
        elif len(normal_basis) < 4:
            residual = list(boundaries[column])
            for row, pivot_column in enumerate(pivots):
                # Later pivot columns have zero entry in an earlier column.
                coefficient = int(matrix[row, column]) % P
                if coefficient:
                    pivot_boundary = boundaries[pivot_column]
                    residual = [
                        (entry - coefficient * pivot_boundary[i]) % P
                        for i, entry in enumerate(residual)
                    ]
            add_boundary_basis(normal_basis, tuple(residual))
        if position in checkpoints:
            stages[position] = {
                "columns": position,
                "contact_rank": contact_rank,
                "contact_nullity": position - contact_rank,
                "kernel_boundary_rank": len(normal_basis),
                "kernel_boundary_basis_Y_R_S_Z": basis_vectors(normal_basis),
                "boundary_cokernel_dimension": 4 - len(normal_basis),
            }
    assert contact_rank == rank
    assert set(stages) == checkpoints
    return stages


def make_case(name):
    if name == "small_m4_rank3":
        profile = Old.K0.Profile(8, 2, 5, 4, 2, 1, 6, 5, 0, 1)
        receipt = Old.make_custom_receipt(
            profile, P, 0, "random", "mid", "minimal", "arbitrary",
            "alternating", 2)
        family = "small adversarial; old boundary gain 3"
    elif name == "small_m4_rank1":
        profile = Old.K0.Profile(10, 4, 7, 4, 2, 1, 6, 5, 0, 1)
        receipt = Old.make_custom_receipt(
            profile, P, 0, "random", "mid", "minimal", "arbitrary",
            "alternating", 2)
        family = "small adversarial; old boundary gain 1"
    elif name == "target_ratio_m5":
        profile = Old.K0.Profile(11, 5, 8, 5, 2, 1, 8, 8, 0, 1)
        receipt = Old.make_custom_receipt(
            profile, P, 0, "random", "mid", "minimal", "arbitrary",
            "alternating", 2)
        family = (
            "exact target-ratio scaled control: m=3B-1, B=2,s=1,U=8, "
            "arbitrary off-agreement direction")
    elif name == "target_ratio_m6":
        profile = Old.K0.Profile(11, 5, 8, 6, 2, 1, 8, 8, 0, 1)
        receipt = Old.make_custom_receipt(
            profile, P, 0, "random", "mid", "minimal", "arbitrary",
            "alternating", 2)
        family = (
            "target-feasible scaled control: B=2,s=1,U=8,m=6, "
            "arbitrary off-agreement direction")
    elif name == "primary_m8":
        profile = replace(Degree.PROFILE, L=10)
        receipt = Degree.Full.M8.monomial_tangent_receipt(
            profile, Degree.TRIAL, 0)
        family = "original F101 m8 L10->L11 passive-only chamber"
    else:
        raise ValueError(name)
    return profile, receipt, family


def analyze_case(name):
    started = time.monotonic()
    old_profile, receipt, family = make_case(name)
    next_profile = replace(old_profile, L=old_profile.L + 1)
    old_monomials = tuple(Old.K0.support(old_profile))
    old_set = set(old_monomials)
    successor = tuple(Old.K0.support(next_profile))
    added = tuple(q for q in successor if q not in old_set)
    passive = tuple(q for q in added if q[4] > 0)
    excluded_active = tuple(q for q in added if q[4] == 0)
    combined = old_monomials + passive
    assert all(sum(q[1:]) == next_profile.L for q in added)
    assert all(q[4] > 0 for q in passive)

    sanity = semantic_sanity(next_profile, receipt, combined)
    old_rows, all_rows = row_universes(
        next_profile, receipt, old_monomials, passive)
    terminal_indices = tuple(range(max(0, next_profile.m - 3),
                                   next_profile.m))
    head_indices = tuple(range(max(0, next_profile.m - 3)))
    head_rows = tuple(row for row in old_rows if row[1] in head_indices)
    assert set(head_indices).isdisjoint(terminal_indices)
    assert set(head_indices) | set(terminal_indices) == set(
        range(next_profile.m))

    boundaries = tuple(formal_boundary(next_profile, receipt, q)
                       for q in combined)
    full_matrix = fill_contact(
        next_profile, receipt, combined, all_rows, f"{name} full")
    full_stages = stage_ranks(
        full_matrix, boundaries, (len(old_monomials), len(combined)),
        f"{name} full")
    del full_matrix
    gc.collect()

    old_boundaries = boundaries[:len(old_monomials)]
    head_matrix = fill_contact(
        next_profile, receipt, old_monomials, head_rows, f"{name} head")
    head_stage = stage_ranks(
        head_matrix, old_boundaries, (len(old_monomials),),
        f"{name} complement-of-terminal") [len(old_monomials)]
    del head_matrix
    gc.collect()

    old = full_stages[len(old_monomials)]
    extended = full_stages[len(combined)]
    old_image = tuple(old["kernel_boundary_basis_Y_R_S_Z"])
    extended_image = tuple(
        extended["kernel_boundary_basis_Y_R_S_Z"])
    head_image = tuple(head_stage["kernel_boundary_basis_Y_R_S_Z"])
    assert same_span(old_image, old_image)
    assert span_rank(old_image, extended_image) == len(extended_image)
    assert span_rank(old_image, head_image) == len(head_image)

    boundary_cokernel_dimension = old["boundary_cokernel_dimension"]
    connecting_rank = (extended["kernel_boundary_rank"] -
                       old["kernel_boundary_rank"])
    terminal_detection_rank = (head_stage["kernel_boundary_rank"] -
                               old["kernel_boundary_rank"])
    compatible_new_coefficient_dimension = (
        len(passive) -
        (extended["contact_rank"] - old["contact_rank"]))
    connecting_kernel_dimension = (
        boundary_cokernel_dimension - connecting_rank)
    terminal_kernel_dimension = (
        boundary_cokernel_dimension - terminal_detection_rank)
    same_kernel = same_span(head_image, extended_image)
    separates_cokernel = (
        terminal_detection_rank == boundary_cokernel_dimension)
    same_missing_directions = (
        same_kernel and terminal_detection_rank == connecting_rank)
    primary_gate = (
        connecting_rank > 0 and same_missing_directions and
        separates_cokernel)

    stable = {
        "case": name,
        "family": family,
        "field": P,
        "old_profile_n_w_g_m_B_s_U_L_k_n0":
            tuple(asdict(old_profile).values()),
        "successor_profile_n_w_g_m_B_s_U_L_k_n0":
            tuple(asdict(next_profile).values()),
        "agreement_set": receipt.agreement,
        "candidate_and_tangent_degrees": (
            Old.degree(receipt.polynomial, P),
            Old.degree(receipt.tangent, P)),
        "semantic_sanity": sanity,
        "source_counts_old_passive_added_excluded_active": (
            len(old_monomials), len(passive), len(added),
            len(excluded_active)),
        "row_counts_old_all_head_complement": (
            len(old_rows), len(all_rows), len(head_rows)),
        "final_three_epsilon_indices": terminal_indices,
        "head_complement_epsilon_indices": head_indices,
        "old_complete": old,
        "extended_old_plus_passive_only": extended,
        "old_head_complement_of_final_three": head_stage,
        "boundary_cokernel_dimension": boundary_cokernel_dimension,
        "relative_passive_compatible_coefficient_dimension":
            compatible_new_coefficient_dimension,
        "full_relative_connecting_transpose_rank": connecting_rank,
        "full_relative_connecting_transpose_kernel_dimension":
            connecting_kernel_dimension,
        "last_three_quotient_transpose_detection_rank":
            terminal_detection_rank,
        "last_three_quotient_transpose_kernel_dimension":
            terminal_kernel_dimension,
        "head_and_extended_boundary_image_combined_rank":
            span_rank(head_image, extended_image),
        "last_three_and_connecting_transpose_kernels_equal": same_kernel,
        "last_three_separates_entire_old_boundary_cokernel":
            separates_cokernel,
        "last_three_detects_same_missing_directions":
            same_missing_directions,
        "nonvacuous_full_separation_gate": primary_gate,
        "logic": (
            "old cokernel dim=4-rank B(ker C_old); connecting transpose "
            "rank=rank I_extended-rank I_old; terminal quotient rank="
            "rank I_head-rank I_old. Their kernels agree exactly iff "
            "I_extended=I_head, checked by an exact four-dimensional span "
            "comparison."),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    return {
        **stable,
        "case_canonical_sha256": hashlib.sha256(
            canonical.encode()).hexdigest(),
        "case_runtime": {
            "seconds": round(time.monotonic() - started, 3),
            "peak_rss_kib_so_far": resource.getrusage(
                resource.RUSAGE_SELF).ru_maxrss,
        },
    }


def assert_regression(case):
    """Pin every load-bearing rank in the frozen exact cases."""
    old = case["old_complete"]
    extended = case["extended_old_plus_passive_only"]
    head = case["old_head_complement_of_final_three"]
    actual = (
        old["contact_rank"], old["contact_nullity"],
        old["kernel_boundary_rank"],
        extended["contact_rank"], extended["contact_nullity"],
        extended["kernel_boundary_rank"],
        head["contact_rank"], head["contact_nullity"],
        head["kernel_boundary_rank"],
        case["boundary_cokernel_dimension"],
        case["full_relative_connecting_transpose_rank"],
        case["last_three_quotient_transpose_detection_rank"],
    )
    expected = {
        "small_m4_rank3": (984, 31, 3, 1224, 96, 4,
                           160, 855, 4, 1, 1, 1),
        "small_m4_rank1": (1228, 5, 1, 1530, 50, 4,
                           200, 1033, 4, 3, 3, 3),
        "target_ratio_m5": (3443, 161, 4, 3949, 258, 4,
                            847, 2757, 4, 0, 0, 0),
        "target_ratio_m6": (4719, 45, 3, 5445, 178, 4,
                            1463, 3301, 4, 1, 1, 1),
        "primary_m8": (10861, 317, 3, 12321, 717, 4,
                       4734, 6444, 4, 1, 1, 1),
    }[case["case"]]
    assert actual == expected


def main():
    parser = argparse.ArgumentParser()
    names = (
        "small_m4_rank3", "small_m4_rank1", "target_ratio_m5",
        "target_ratio_m6", "primary_m8")
    parser.add_argument("--case", choices=names + ("controls", "all"),
                        default="all")
    args = parser.parse_args()
    started = time.monotonic()
    if args.case == "controls":
        selected = names[:-1]
    elif args.case == "all":
        selected = names
    else:
        selected = (args.case,)
    cases = []
    for index, name in enumerate(selected, start=1):
        print(f"case {index}/{len(selected)}: {name}", file=sys.stderr,
              flush=True)
        case = analyze_case(name)
        assert_regression(case)
        cases.append(case)

    primary = next((row for row in cases if row["case"] == "primary_m8"),
                   None)
    stable_cases = tuple({key: value for key, value in row.items()
                          if key != "case_runtime"} for row in cases)
    stable = {
        "scope": (
            "faithful literal final-three quotient-aware connecting-"
            "transpose gate; finite exact controls, not target transport"),
        "selected_cases": selected,
        "cases": stable_cases,
        "primary_verdict": (
            None if primary is None else
            ("GREEN" if primary["nonvacuous_full_separation_gate"] else
             "RED")),
        "scope_guard": (
            "GREEN certifies only the named finite chamber. It does not "
            "prove target m47 source realization, target boundary cokernel "
            "dimension, or a target-uniform passive producer."),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    payload = {
        **stable,
        "case_runtimes": tuple(row["case_runtime"] for row in cases),
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(
            Path(__file__).read_bytes()).hexdigest(),
        "runtime": {
            "seconds": round(time.monotonic() - started, 3),
            "peak_rss_kib": resource.getrusage(
                resource.RUSAGE_SELF).ru_maxrss,
            "hard_address_space_cap_bytes": ADDRESS_SPACE_CAP_BYTES,
        },
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
