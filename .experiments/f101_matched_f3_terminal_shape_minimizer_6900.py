#!/usr/bin/env python3
"""Exact grade-7 connecting residues for the matched four-packet control.

The complete grade-6 prefix obstructs F0,F1,F2,F3 by one joint quotient
class.  This executable reduces all exact target columns and all grade-7
source columns modulo that prefix, partitions the shell by derivative shape,
and solves the remaining coefficientwise equation without localization.

It is a finite structural control, not a Full187 target theorem.
"""

from __future__ import annotations

from collections import defaultdict
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402


P = 101
CASE = (10, 4, 7, 4, 28, 1, 1, 6, 10)
TARGET_SAFE103_SHAPES = {
    (r, s)
    for s in range(11)
    for r in range(22 - s)
    if r + s <= 16
    and r + 4 * s <= 33
    and (s <= 6 or r + 4 * s <= 32)
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


def contains(columns, target):
    echelon = M.ColumnEchelon()
    for index, column in enumerate(columns):
        echelon.add(column, index)
    return not echelon.reduce(target)


def solve(columns, target):
    rows = tuple(sorted(
        {row for column in columns for row in column} | set(target)))
    row_index = {row: index for index, row in enumerate(rows)}
    width = len(columns) + 1
    matrix = nmod_mat(len(rows), width, [
        (columns[column].get(row, 0)
         if column < len(columns) else -target.get(row, 0))
        for row in rows for column in range(width)
    ], P)
    kernel, nullity = matrix.nullspace()
    witness = next(
        column for column in range(nullity)
        if int(kernel[len(columns), column]) % P)
    scale = pow(int(kernel[len(columns), witness]) % P, -1, P)
    coefficients = tuple(
        int(kernel[index, witness]) * scale % P
        for index in range(len(columns)))
    reconstructed = {}
    for coefficient, column in zip(coefficients, columns):
        reconstructed = add_scaled(reconstructed, column, coefficient)
    assert reconstructed == target
    return coefficients


def support_summary(indices, coefficients, monomials):
    support = tuple(
        (monomials[index], coefficient)
        for index, coefficient in zip(indices, coefficients) if coefficient)
    layers = defaultdict(list)
    for (xpower, y, r, s, z), coefficient in support:
        layers[(y, r, s, z)].append((xpower, coefficient))
    layer_summary = []
    for shape, entries in sorted(layers.items()):
        xvalues = tuple(x for x, _coefficient in entries)
        layer_summary.append({
            "Y_R_S_Z": shape,
            "nonzero_coefficient_count": len(entries),
            "minimum_maximum_X": (min(xvalues), max(xvalues)),
            "X_support_contiguous": xvalues == tuple(range(
                min(xvalues), max(xvalues) + 1)),
            "coefficient_sha256": hashlib.sha256(
                repr(tuple(entries)).encode()).hexdigest(),
        })
    return {
        "support_size": len(support),
        "support_sha256": hashlib.sha256(repr(support).encode()).hexdigest(),
        "layer_summary": tuple(layer_summary),
    }


def scaled_sparse_equality(left, right):
    """Return c when left=c*right, requiring identical nonzero support."""
    left = {monomial: coefficient % P for monomial, coefficient in left.items()
            if coefficient % P}
    right = {monomial: coefficient % P for monomial, coefficient in right.items()
             if coefficient % P}
    if set(left) != set(right) or not right:
        return None
    first = min(right)
    scalar = left[first] * pow(right[first], -1, P) % P
    if all(left[monomial] == scalar * coefficient % P
           for monomial, coefficient in right.items()):
        return scalar
    return None


def deletion_minimize(indices, residues, target):
    live = list(range(len(indices)))
    for candidate in tuple(reversed(live)):
        trial = [position for position in live if position != candidate]
        if contains(tuple(residues[position] for position in trial), target):
            live = trial
    selected_indices = tuple(indices[position] for position in live)
    selected_residues = tuple(residues[position] for position in live)
    assert contains(selected_residues, target)
    assert all(not contains(
        selected_residues[:position] + selected_residues[position + 1:], target)
        for position in range(len(selected_residues)))
    return tuple(live), selected_indices, selected_residues


def main() -> None:
    started = time.monotonic()
    M.PRIME = M.T.PRIME = M.F.PRIME = F.PRIME = P
    literal = M.build_case(
        "matched_m4_exact_F3_terminal_quotient",
        CASE,
        actual_agreement_count=7,
        anchor_count=7,
        normal_coordinates=4,
    )
    prefix = tuple(
        index for index, monomial in enumerate(literal.monomials)
        if sum(monomial[1:]) <= CASE[7])
    assert len(prefix) == 1351
    prefix_echelon = M.ColumnEchelon()
    for index in prefix:
        assert prefix_echelon.add(literal.columns[index], index)
    assert prefix_echelon.rank == 1351

    target_residues = tuple(
        prefix_echelon.reduce(target) for target in literal.targets)
    assert all(target_residues)
    assert quotient_rank(target_residues) == 1
    pivot = min(target_residues[0])
    target_scalars = []
    for target in target_residues:
        scalar = target[pivot] * pow(target_residues[0][pivot], -1, P) % P
        assert not add_scaled(target, target_residues[0], -scalar)
        target_scalars.append(scalar)
    target_scalars = tuple(target_scalars)

    groups = defaultdict(list)
    for index, monomial in enumerate(literal.monomials):
        if sum(monomial[1:]) == CASE[7] + 1:
            groups[(monomial[2], monomial[3])].append(index)
    groups = {shape: tuple(indices) for shape, indices in sorted(groups.items())}
    assert tuple(groups) == ((0, 0), (0, 1), (1, 0))
    assert all(shape in TARGET_SAFE103_SHAPES for shape in groups)

    centered_value = F.sparse_add(
        F.Y, F.sparse_mul(F.Z, F.sparse_embed_x(literal.q)), -1)

    group_receipts = []
    for shape, indices in groups.items():
        residues = tuple(prefix_echelon.reduce(literal.columns[index])
                         for index in indices)
        rank = quotient_rank(residues)
        assert contains(residues, target_residues[0])
        live_positions, minimal_indices, minimal_residues = deletion_minimize(
            indices, residues, target_residues[0])
        coefficients = solve(minimal_residues, target_residues[0])
        solution_source = {
            literal.monomials[index]: coefficient
            for index, coefficient in zip(minimal_indices, coefficients)
            if coefficient}
        r, s = shape
        carrier = F.sparse_pow(centered_value, CASE[3])
        carrier = F.sparse_mul(carrier, F.sparse_pow(F.R, r))
        carrier = F.sparse_mul(carrier, F.sparse_pow(F.S, s))
        carrier_seed = CASE[7] + 1 - CASE[3] - r - s
        assert carrier_seed >= 0
        carrier = F.sparse_mul(carrier, F.sparse_pow(F.Z, carrier_seed))
        carrier_scalar = scaled_sparse_equality(solution_source, carrier)
        assert carrier_scalar is not None
        minimal = support_summary(minimal_indices, coefficients,
                                  literal.monomials)
        minimal["inclusion_minimal_column_count"] = len(minimal_indices)
        minimal["selected_source_column_indices_sha256"] = hashlib.sha256(
            repr(minimal_indices).encode()).hexdigest()
        minimal["selected_positions_within_group_sha256"] = hashlib.sha256(
            repr(live_positions).encode()).hexdigest()
        minimal["exact_centered_carrier_formula"] = (
            f"R^{r}*S^{s}*(Y-QZ)^{CASE[3]}*Z^{carrier_seed}")
        minimal["solution_equals_scalar_times_centered_carrier"] = (
            carrier_scalar)
        minimal["centered_carrier_support_sha256"] = hashlib.sha256(
            repr(tuple(sorted(carrier.items()))).encode()).hexdigest()
        group_receipts.append({
            "derivative_shape_r_s": shape,
            "lies_in_target_conservative_safe103": True,
            "grade7_group_column_count": len(indices),
            "grade7_group_quotient_rank": rank,
            "all_four_target_residues_contained": True,
            "minimal_F0_residue_solution": minimal,
            "F0_F1_F2_F3_solution_scalars_relative_to_F0": target_scalars,
        })

    stable = {
        "scope": (
            "exact coefficientwise F101 matched-m4 grade7 connecting "
            "quotient for the four named packets; finite control only"
        ),
        "parameters_n_w_g_m_D_s_t_J_L": CASE,
        "prefix_columns_rank": (len(prefix), prefix_echelon.rank),
        "prefix_individual_and_joint_packet_defects": ((1, 1, 1, 1), 1),
        "target_residue_support_sizes": tuple(map(len, target_residues)),
        "target_residue_quotient_rank": 1,
        "F0_F1_F2_F3_residue_scalars_relative_to_F0": target_scalars,
        "terminal_group_receipts": tuple(group_receipts),
        "agreement_four_normal_determinant_formula": (
            "unit*Lambda_G^(4m-3)*(Q-q_H)/Lambda_H"
        ),
        "connecting_interface_shape": (
            "one-dimensional target residue, so the terminal interface is "
            "a 1x4 nonzero scalar row, not four independent terminal classes"
        ),
        "decision": (
            "GREEN_EACH_SINGLE_DERIVATIVE_SHAPE_GROUP_CLOSES_ALL_FOUR_PACKETS"
        ),
        "scope_guard": (
            "The entire legal X/passive group is used.  This does not show "
            "that one monomial, a localized multiplier, or the target safe103 "
            "recurrence closes coefficientwise."
        ),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    payload = {
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "runtime_receipt": {
            "elapsed_seconds": round(time.monotonic() - started, 6),
            "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            "external_memory_cap_bytes": 4 * 1024**3,
        },
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
