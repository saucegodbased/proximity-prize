#!/usr/bin/env python3
"""Exact m=7 gate for the proposed first-shell mixed lift.

The m=5 and m=6 arbitrary-error-direction controls close the three locator
normal right-hand sides after adjoining total grade ``J+1``.  The structural
extractor previously assumed that this remained true and crashed at m=7.
This executable turns that crash into an explicit rank receipt: it compares
the complete literal source through grades ``J`` and ``J+1`` and reports the
three individual and joint target defects.

This is finite F101 discovery evidence, not a target theorem.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import f101_n10_grade7_centered_wronskian_universality_6900 as U  # noqa: E402
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402


P = 101
OFFSETS = (3, 5, 7)
CASE = (10, 4, 7, 7, 49, 1, 1, 9, 13)


def trimmed_nullspace(matrix):
    basis, dimension = matrix.nullspace()
    return nmod_mat(basis.nrows(), dimension, [
        int(basis[row, column]) % P
        for row in range(basis.nrows()) for column in range(dimension)
    ], P), dimension


def target_defects(image, target_columns):
    rank = image.rank()
    rows = image.nrows()
    columns = image.ncols()
    individual = []
    for target in target_columns:
        augmented = nmod_mat(rows, columns + 1, [
            (int(image[row, column]) % P if column < columns
             else target[row])
            for row in range(rows) for column in range(columns + 1)
        ], P)
        individual.append(augmented.rank() - rank)
    joint = nmod_mat(rows, columns + len(target_columns), [
        (int(image[row, column]) % P if column < columns
         else target_columns[column - columns][row])
        for row in range(rows)
        for column in range(columns + len(target_columns))
    ], P).rank() - rank
    return tuple(individual), joint


def prefix_receipt(literal, maximum_grade):
    indices = tuple(
        index for index, monomial in enumerate(literal.monomials)
        if sum(monomial[1:]) <= maximum_grade)
    contact_rows = tuple(
        index for index, row in enumerate(literal.row_keys) if row[0] == "C")
    j_rows = tuple(sorted(
        {index for source_index in indices
         for index in literal.columns[source_index]
         if literal.row_keys[index][0] == "J"}
        | {index for target in literal.targets[:3] for index in target}
    ))
    contact = U.matrix_from_columns(
        contact_rows, literal.columns, indices)
    kernel, nullity = trimmed_nullspace(contact)
    j_matrix = U.matrix_from_columns(j_rows, literal.columns, indices)
    image = j_matrix * kernel
    target_columns = tuple(tuple(
        target.get(row, 0) % P for row in j_rows
    ) for target in literal.targets[:3])
    individual, joint = target_defects(image, target_columns)
    return {
        "maximum_total_grade": maximum_grade,
        "source_columns": len(indices),
        "contact_rows_rank_nullity": (
            len(contact_rows), contact.rank(), nullity),
        "vertical_rows_image_rank": (len(j_rows), image.rank()),
        "individual_F0_F1_F2_defects": individual,
        "joint_F0_F1_F2_defect": joint,
    }


def main():
    M.PRIME = M.T.PRIME = M.F.PRIME = F.PRIME = U.PRIME = P
    literal = M.build_case(
        "m7_first_shell_target_gate", CASE, 7, 7, 3,
        error_direction_offsets=OFFSETS)
    before = prefix_receipt(literal, CASE[7])
    after = prefix_receipt(literal, CASE[7] + 1)
    payload = {
        "scope": (
            "complete literal grade-J versus grade-(J+1) target gate in one "
            "fixed n10 arbitrary-error-direction F101 chamber"
        ),
        "field": P,
        "case_n_w_g_m_D_s_t_J_L": CASE,
        "error_direction_offsets": OFFSETS,
        "prefix_receipts": (before, after),
        "first_shell_closes_three_rhs": (
            after["joint_F0_F1_F2_defect"] == 0),
        "honest_interpretation": (
            "A nonzero defect refutes uniform extrapolation of the m5/m6 "
            "first-shell closure in this finite family; it does not prove "
            "the literal Full187 target impossible."
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(
        canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
