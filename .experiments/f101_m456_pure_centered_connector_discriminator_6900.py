#!/usr/bin/env python3
"""Test the pure centered one-shell connector at multiplicities 4, 5, 6.

For each fixed matched F_101 chamber this script reduces the exact
F0,F1,F2,F3 packet and

    C00 = (Y-Q(X)Z)^m Z^(J+1-m)

modulo the complete source prefix of centered total grade at most J.  All
rows and coefficients remain over F_101; no X-localization is used.  This is
a finite discriminator for a symbolic lemma, not a Full187 theorem.
"""

from __future__ import annotations

import argparse
import hashlib
from itertools import combinations
import json
from pathlib import Path
import resource
import sys
import time

sys.path.insert(0, ".experiments")
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402


P = 101
CASES = {
    "m4": (10, 4, 7, 4, 28, 1, 1, 6, 10),
    "m5": (10, 4, 7, 5, 35, 1, 1, 7, 11),
    "m6": (10, 4, 7, 6, 42, 1, 1, 8, 12),
}


def add_scaled(target, source, scale):
    answer = dict(target)
    for row, coefficient in source.items():
        value = (answer.get(row, 0) + scale * coefficient) % P
        if value:
            answer[row] = value
        else:
            answer.pop(row, None)
    return answer


def quotient_rank(columns):
    echelon = M.ColumnEchelon()
    for index, column in enumerate(columns):
        echelon.add(column, index)
    return echelon.rank


def quotient_defects(columns, targets):
    echelon = M.ColumnEchelon()
    for index, column in enumerate(columns):
        echelon.add(column, index)
    base_rank = echelon.rank
    individual = tuple(
        quotient_rank(columns + (target,)) - base_rank for target in targets)
    joint = quotient_rank(columns + targets) - base_rank
    return individual, joint


def proportional_scalar(left, right):
    """Return c for left=c*right, or None when they are not proportional."""
    if not left and not right:
        return 0
    if not left or not right:
        return None
    pivot = min(right)
    scalar = left.get(pivot, 0) * pow(right[pivot], -1, P) % P
    return scalar if not add_scaled(left, right, -scalar) else None


def analyze(label):
    case = CASES[label]
    n, w, g, m, degree, slope, curvature, jet, seed = case
    assert (n, w, g, degree, slope, curvature) == (
        10, 4, 7, m * g, 1, 1)
    literal = M.build_case(
        f"{label}_matched_exact_F3_pure_centered_connector",
        case,
        actual_agreement_count=g,
        anchor_count=g,
        normal_coordinates=4,
    )

    prefix = tuple(
        index for index, monomial in enumerate(literal.monomials)
        if sum(monomial[1:]) <= jet)
    prefix_echelon = M.ColumnEchelon()
    for index in prefix:
        prefix_echelon.add(literal.columns[index], index)

    target_residues = tuple(
        prefix_echelon.reduce(target) for target in literal.targets)
    packet_rank = quotient_rank(target_residues)

    centered = F.sparse_add(
        F.Y, F.sparse_mul(F.Z, F.sparse_embed_x(literal.q)), -1)
    carrier_seed = jet + 1 - m
    carrier = F.sparse_mul(
        F.sparse_pow(centered, m), F.sparse_pow(F.Z, carrier_seed))
    support_index = {
        monomial: index for index, monomial in enumerate(literal.monomials)}
    assert all(monomial in support_index for monomial in carrier)
    carrier_image = {}
    for monomial, coefficient in carrier.items():
        carrier_image = add_scaled(
            carrier_image, literal.columns[support_index[monomial]], coefficient)
    carrier_residue = prefix_echelon.reduce(carrier_image)

    target_over_carrier = tuple(
        proportional_scalar(target, carrier_residue)
        for target in target_residues)
    joint_rank = quotient_rank(target_residues + (carrier_residue,))

    shell_groups = {}
    for index, monomial in enumerate(literal.monomials):
        if sum(monomial[1:]) == jet + 1:
            shell_groups.setdefault((monomial[2], monomial[3]), []).append(index)
    shell_groups = {
        shape: tuple(indices) for shape, indices in sorted(shell_groups.items())}
    shell_residues = {
        shape: tuple(prefix_echelon.reduce(literal.columns[index])
                     for index in indices)
        for shape, indices in shell_groups.items()
    }
    group_rows = []
    for shape, indices in shell_groups.items():
        residues = shell_residues[shape]
        defects = quotient_defects(residues, target_residues)
        r, s = shape
        centered_shape_seed = jet + 1 - m - r - s
        centered_shape = None
        if centered_shape_seed >= 0:
            centered_shape = F.sparse_mul(
                F.sparse_pow(centered, m), F.sparse_pow(F.R, r))
            centered_shape = F.sparse_mul(
                centered_shape, F.sparse_pow(F.S, s))
            centered_shape = F.sparse_mul(
                centered_shape, F.sparse_pow(F.Z, centered_shape_seed))
            assert all(monomial in support_index for monomial in centered_shape)
            centered_image = {}
            for monomial, coefficient in centered_shape.items():
                centered_image = add_scaled(
                    centered_image,
                    literal.columns[support_index[monomial]], coefficient)
            centered_residue = prefix_echelon.reduce(centered_image)
            centered_shape = {
                "formula": (
                    f"R^{r}*S^{s}*(Y-QZ)^{m}*Z^{centered_shape_seed}"),
                "support_size": len(centered_shape),
                "residue_nonzero": bool(centered_residue),
                "packet_plus_this_carrier_quotient_rank": quotient_rank(
                    target_residues + (centered_residue,)),
            }
        group_rows.append({
            "derivative_shape_r_s": shape,
            "shell_column_count": len(indices),
            "shell_quotient_rank": quotient_rank(residues),
            "packet_defects_after_this_shape": defects,
            "canonical_centered_shape_carrier": centered_shape,
        })

    shape_subset_rows = []
    shapes = tuple(shell_groups)
    for size in range(1, len(shapes) + 1):
        for subset in combinations(shapes, size):
            residues = tuple(
                residue for shape in subset for residue in shell_residues[shape])
            individual, joint = quotient_defects(residues, target_residues)
            shape_subset_rows.append({
                "shapes": subset,
                "packet_individual_and_joint_defects": (individual, joint),
            })
    closing_subsets = tuple(
        row["shapes"] for row in shape_subset_rows
        if row["packet_individual_and_joint_defects"][1] == 0)
    inclusion_minimal_closing_subsets = tuple(
        subset for subset in closing_subsets
        if not any(set(other) < set(subset) for other in closing_subsets))
    return {
        "label": label,
        "parameters_n_w_g_m_D_s_t_J_L": case,
        "prefix_columns_rank": (len(prefix), prefix_echelon.rank),
        "packet_individual_defects": tuple(bool(x) for x in target_residues),
        "packet_quotient_rank": packet_rank,
        "pure_carrier_formula": f"(Y-QZ)^{m}*Z^{carrier_seed}",
        "pure_carrier_support_size": len(carrier),
        "pure_carrier_residue_nonzero": bool(carrier_residue),
        "packet_scalars_relative_to_pure_carrier": target_over_carrier,
        "packet_plus_carrier_quotient_rank": joint_rank,
        "pure_carrier_spans_entire_packet_residue": (
            carrier_residue != {} and packet_rank == joint_rank == 1
            and all(scalar is not None for scalar in target_over_carrier)
        ),
        "target_residue_support_sizes": tuple(map(len, target_residues)),
        "pure_carrier_residue_support_size": len(carrier_residue),
        "first_post_prefix_shell_shape_groups": tuple(group_rows),
        "shape_subset_packet_defects": tuple(shape_subset_rows),
        "inclusion_minimal_shell_shape_subsets_closing_packet": (
            inclusion_minimal_closing_subsets),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", choices=tuple(CASES), action="append")
    args = parser.parse_args()
    labels = tuple(args.case or CASES)
    started = time.monotonic()
    M.PRIME = M.T.PRIME = M.F.PRIME = F.PRIME = P
    rows = tuple(analyze(label) for label in labels)
    stable = {
        "scope": (
            "exact coefficientwise F101 matched four-packet quotient modulo "
            "the complete grade-J prefix; finite controls only"
        ),
        "field": P,
        "rows": rows,
        "decision": (
            "PURE_CENTERED_CONNECTOR_UNIVERSAL_ACROSS_TESTED_M"
            if all(row["pure_carrier_spans_entire_packet_residue"]
                   for row in rows)
            else "PURE_CENTERED_CONNECTOR_NOT_UNIVERSAL_ACROSS_TESTED_M"
        ),
        "scope_guard": (
            "A repeated finite-field pattern does not prove nonvanishing or "
            "the target Full187 connecting/confluence statement."
        ),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    print(json.dumps({
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "runtime_receipt": {
            "elapsed_seconds": round(time.monotonic() - started, 6),
            "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            "external_memory_cap_bytes": 4 * 1024**3,
        },
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
