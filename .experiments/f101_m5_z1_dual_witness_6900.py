#!/usr/bin/env python3
"""Extract a sparse exact dual witness for the persistent m5 Z1 defect.

This reuses the literal contact translator and the coefficientwise transpose
semantics of ``f101_transposed_four_residue_mapping_cone_gate_6900.py``.  It
does not generate an ambient contact cokernel: after contact RREF it builds
only the four boundary-coordinate image, then finds a left annihilator whose
constant-Z coefficient is one.  The output is finite F101 discovery evidence.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import f101_transposed_four_residue_mapping_cone_gate_6900 as G  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402


P = 101
CASE = G.CASES["m5"]


def coefficient_image(literal, maximum_grade):
    grades = tuple(sum(monomial[1:]) for monomial in literal.monomials)
    terminal = tuple(i for i, grade in enumerate(grades)
                     if grade == maximum_grade)
    prefix = tuple(i for i, grade in enumerate(grades)
                   if grade < maximum_grade)
    source_indices = terminal + prefix
    source_position = {index: position
                       for position, index in enumerate(source_indices)}

    active_contact_rows = {
        row
        for source_index in source_indices
        for row in literal.columns[source_index]
        if literal.row_keys[row][0] == "C"
    }
    top_rows = tuple(sorted(
        (row for row in active_contact_rows
         if sum(literal.row_keys[row][2][1:]) == maximum_grade),
        key=lambda row: repr(literal.row_keys[row]),
    ))
    lower_rows = tuple(sorted(active_contact_rows - set(top_rows),
                              key=lambda row: repr(literal.row_keys[row])))
    contact_rows = top_rows + lower_rows
    contact = G.matrix_from_contact_rows(
        literal, source_indices, contact_rows)
    contact, contact_rank = contact.rref(inplace=True)

    pivots = []
    next_column = 0
    for row in range(contact_rank):
        pivot = G.first_nonzero_in_rref_row(contact, row, next_column)
        pivots.append(pivot)
        next_column = pivot + 1
    pivot_to_row = {pivot: row for row, pivot in enumerate(pivots)}
    free_columns = tuple(column for column in range(len(source_indices))
                         if column not in pivot_to_row)
    free_position = {column: index
                     for index, column in enumerate(free_columns)}

    units = ((1, 0, 0, 0), (0, 1, 0, 0),
             (0, 0, 1, 0), (0, 0, 0, 1))
    monomial_index = {monomial: index
                      for index, monomial in enumerate(literal.monomials)}
    boundary_positions = []
    rows = []
    for coordinate, unit in enumerate(units):
        for degree in range(literal.parameters[4]):
            source_index = monomial_index.get((degree,) + unit)
            if source_index is None or source_index not in source_position:
                continue
            boundary_positions.append((coordinate, degree))
            column = source_position[source_index]
            values = [0] * len(free_columns)
            if column in free_position:
                values[free_position[column]] = 1
            else:
                pivot_row = pivot_to_row[column]
                for free_index, free_column in enumerate(free_columns):
                    values[free_index] = -int(
                        contact[pivot_row, free_column]) % P
            rows.append(values)
    image = nmod_mat(len(rows), len(free_columns),
                     [entry for row in rows for entry in row], P)
    return boundary_positions, image, contact_rank, len(source_indices)


def sparse_z1_annihilator(positions, image):
    """Return a <= rank+1 support annihilator normalized at constant Z."""
    zrow = positions.index((3, 0))
    row_order = tuple(i for i in range(len(positions)) if i != zrow)
    other = nmod_mat(len(row_order), image.ncols(), [
        int(image[row, column]) % P
        for row in row_order for column in range(image.ncols())
    ], P)
    # Pivot rows of ``other`` form a row basis.  RREF of the transpose makes
    # those source-row indices explicit as pivot columns.
    transposed, rank = other.transpose().rref(inplace=False)
    pivots = []
    next_column = 0
    for row in range(rank):
        pivot = G.first_nonzero_in_rref_row(transposed, row, next_column)
        pivots.append(pivot)
        next_column = pivot + 1
    basis_rows = tuple(row_order[pivot] for pivot in pivots)
    basis = nmod_mat(rank, image.ncols(), [
        int(image[row, column]) % P
        for row in basis_rows for column in range(image.ncols())
    ], P)
    # Solve c * basis = -zrow on a square nonsingular column minor, then
    # validate on every column below.
    reduced_basis, reduced_rank = basis.rref(inplace=False)
    assert reduced_rank == rank
    pivot_columns = []
    next_column = 0
    for row in range(rank):
        pivot = G.first_nonzero_in_rref_row(
            reduced_basis, row, next_column)
        pivot_columns.append(pivot)
        next_column = pivot + 1
    square = nmod_mat(rank, rank, [
        int(basis[row, column]) % P
        for row in range(rank) for column in pivot_columns
    ], P)
    rhs = nmod_mat(rank, 1, [
        -int(image[zrow, column]) % P for column in pivot_columns
    ], P)
    coefficients = square.transpose().solve(rhs)
    witness = {positions[zrow]: 1}
    for index, row in enumerate(basis_rows):
        coefficient = int(coefficients[index, 0]) % P
        if coefficient:
            witness[positions[row]] = coefficient
    # Check the exact annihilation and target pairing.
    for column in range(image.ncols()):
        assert sum(coefficient * int(image[positions.index(position), column])
                   for position, coefficient in witness.items()) % P == 0
    assert witness[(3, 0)] == 1
    return tuple(sorted((coordinate, degree, coefficient)
                        for (coordinate, degree), coefficient
                        in witness.items())), rank


def main():
    started = time.monotonic()
    M.PRIME = M.T.PRIME = M.F.PRIME = F.PRIME = P
    literal = M.build_case(
        "m5_z1_dual_witness", CASE,
        actual_agreement_count=7, anchor_count=7, normal_coordinates=3,
        error_direction_offsets=G.OFFSETS,
    )
    grades = []
    for grade in range(CASE[7] + 1, CASE[8] + 1):
        positions, image, contact_rank, source_count = coefficient_image(
            literal, grade)
        witness, non_z_row_rank = sparse_z1_annihilator(positions, image)
        z_rows_nonzero = tuple(
            (degree, sum(int(image[row, column]) != 0
                         for column in range(image.ncols())))
            for row, (coordinate, degree) in enumerate(positions)
            if coordinate == 3 and any(int(image[row, column]) % P
                                       for column in range(image.ncols()))
        )
        grades.append({
            "grade": grade,
            "contact_rank_nullity": (
                contact_rank, source_count - contact_rank),
            "boundary_rows_columns_rank": (
                image.nrows(), image.ncols(), image.rank()),
            "non_z_row_rank": non_z_row_rank,
            "nonzero_z_rows_and_support_sizes": z_rows_nonzero,
            "normalized_constant_z_dual_support": witness,
            "witness_sha256": hashlib.sha256(
                repr(witness).encode()).hexdigest(),
        })
    payload = {
        "case": CASE,
        "field": P,
        "grades": grades,
        "scope": (
            "Exact coefficientwise dual witnesses in one finite literal m5 "
            "control; discovery evidence, not a Full187 theorem."),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["runtime_receipt"] = {
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "external_memory_cap_bytes": 4 * 1024**3,
    }
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
