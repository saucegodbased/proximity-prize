#!/usr/bin/env python3
"""Exact full-band audit for the eight order-four terminal carriers.

The previously proposed 24-by-24 selected-row block is correct for one
coefficient layer, but it does not repeat diagonally after Z shifts: the
selected seed of (a,c) is b+a+c, so adjacent carriers and adjacent shifts
share rows.  This script keeps the *complete* one-node contact image and
compares it to the union of those selected rows.

It also factors each column by its own lowest Z seed and checks the constant
coefficient matrix after that column-delay normalization.  Finally, in the
legal n=4,m=8 chamber, it reduces two complete carrier layers modulo every
source column of grade at most J.  Thus the script distinguishes a local-row
projection failure from something the lower-grade base really kills.

This is a finite exact F101 discriminator.  It is not a target theorem and
does not assert that a forced residual belongs to the carrier module.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import f101_order4_eight_carrier_local_jet_block_6900 as LB  # noqa: E402
import f101_terminal_seed_trellis_three_carrier_6900 as TT  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402


P = 101
MULTIPLICITIES = (4, 5, 6, 8)
PAIRS = LB.PAIRS


def sparse_rank(columns):
    return M.modular_rank_sparse(columns)


def shift_contact_z(contact, shift):
    return {
        (*row[:-1], row[-1] + shift): coefficient
        for row, coefficient in contact.items()
    }


def shift_source_z(source, shift):
    return {
        (x, y, r, s, z + shift): coefficient
        for (x, y, r, s, z), coefficient in source.items()
    }


def add_scaled(target, source, scale):
    for row, coefficient in source.items():
        value = (target.get(row, 0) + scale * coefficient) % P
        if value:
            target[row] = value
        else:
            target.pop(row, None)


def coefficient_sources(literal, case, node):
    """The 24 carrier columns p=(X-node)^j, j=0,1,2."""
    old_case = LB.CASE
    try:
        LB.CASE = case
        out = []
        for jet in range(3):
            polynomial = LB.local_x_power(node, jet)
            for a, c in PAIRS:
                source = LB.scale_by_poly(LB.carrier(literal, a, c), polynomial)
                out.append(((jet, a, c), source))
        return tuple(out)
    finally:
        LB.CASE = old_case


def local_columns(literal, case, node, offset, delta=1):
    m = case[3]
    q_at_node = F.poly_eval(literal.q, node)
    received_direction = (q_at_node + offset) % P
    out = []
    for label, source in coefficient_sources(literal, case, node):
        out.append((label, LB.local_contact(
            source, node, delta, received_direction, m)))
    return tuple(out)


def selected_rows(case, shifts):
    b = case[7] + 1 - case[3]
    return tuple(sorted({
        (jet, 0, c, 0, b + a + c + shift)
        for shift in range(shifts)
        for jet in range(3)
        for a, c in PAIRS
    }))


def restricted_rank(columns, rows):
    row_set = set(rows)
    return sparse_rank(tuple(
        {row: value for row, value in column.items() if row in row_set}
        for column in columns
    ))


def relation_witness(columns, rows, labels):
    """Deterministic selected-kernel vector with nonzero complete leakage."""
    matrix = nmod_mat(len(rows), len(columns), [
        column.get(row, 0) for row in rows for column in columns
    ], P)
    kernel, nullity = matrix.nullspace()
    assert nullity == len(columns) - matrix.rank()

    candidates = []
    for basis_index in range(nullity):
        coefficients = tuple(
            int(kernel[column, basis_index]) % P
            for column in range(len(columns)))
        assert any(coefficients)
        leakage = {}
        for coefficient, column in zip(coefficients, columns):
            if coefficient:
                add_scaled(leakage, column, coefficient)
        if not leakage:
            continue
        selected_leakage = {row: value for row, value in leakage.items()
                            if row in set(rows)}
        assert not selected_leakage
        candidates.append((len(leakage), coefficients, leakage))
    assert candidates
    _size, coefficients, leakage = min(candidates,
                                       key=lambda item: (item[0], item[1]))
    coefficient_support = tuple(
        (label, coefficient)
        for label, coefficient in zip(labels, coefficients) if coefficient)
    leakage_support = tuple(sorted(leakage.items()))
    return {
        "selected_kernel_dimension": nullity,
        "coefficient_support_size": len(coefficient_support),
        "coefficient_support": coefficient_support,
        "coefficient_sha256": hashlib.sha256(
            repr(coefficient_support).encode()).hexdigest(),
        "complete_leakage_support_size": len(leakage_support),
        "complete_leakage_seed_histogram": tuple(sorted({
            seed: sum(1 for row, _value in leakage_support if row[-1] == seed)
            for seed in {row[-1] for row, _value in leakage_support}
        }.items())),
        "complete_leakage_sha256": hashlib.sha256(
            repr(leakage_support).encode()).hexdigest(),
        "selected_projection_is_zero": True,
        "complete_contact_is_nonzero": True,
    }


def normalized_lowest_seed_block(local, case):
    """Drop each column's own delay b+a+c and retain its leading slice."""
    b = case[7] + 1 - case[3]
    columns = []
    for (jet, a, c), contact in local:
        seed = b + a + c
        leading = {
            row[:-1]: coefficient
            for row, coefficient in contact.items() if row[-1] == seed
        }
        assert leading
        columns.append(leading)
    channels = tuple(sorted({row for column in columns for row in column}))
    matrix = nmod_mat(len(channels), len(columns), [
        column.get(row, 0) for row in channels for column in columns
    ], P)
    rank = matrix.rank()
    result = {
        "row_channels_after_column_delay_normalization": len(channels),
        "columns": len(columns),
        "rank": rank,
    }
    if rank == len(columns):
        echelon = M.ColumnEchelon()
        pivot_channels = []
        for row_index, row in enumerate(channels):
            row_vector = {
                column: columns[column].get(row, 0)
                for column in range(len(columns))
                if columns[column].get(row, 0)
            }
            if echelon.add(row_vector, row_index):
                pivot_channels.append(row)
        assert len(pivot_channels) == len(columns)
        minor = nmod_mat(len(columns), len(columns), [
            column.get(row, 0)
            for row in pivot_channels for column in columns
        ], P)
        determinant = int(minor.det()) % P
        assert determinant
        result.update({
            "first_lexicographic_full_rank_row_minor":
                tuple(pivot_channels),
            "minor_determinant_mod_101": determinant,
        })
    return result


def chamber(m):
    case = (4, 1, 3, m, 3 * m, 1, 1, m + 2, m + 6)
    literal = M.build_case(
        f"banded_n4_m{m}", case, actual_agreement_count=3,
        anchor_count=3, normal_coordinates=3,
        error_direction_offsets=(3,))
    local = local_columns(literal, case, node=3, offset=3)
    leading = normalized_lowest_seed_block(local, case)

    band_rows = []
    for shifts in range(1, 5):
        columns = tuple(
            shift_contact_z(contact, shift)
            for shift in range(shifts)
            for _label, contact in local)
        rows = selected_rows(case, shifts)
        band_rows.append({
            "number_of_Z_layers": shifts,
            "columns": len(columns),
            "distinct_selected_rows": len(rows),
            "selected_projection_rank": restricted_rank(columns, rows),
            "complete_contact_rank": sparse_rank(columns),
        })

    result = {
        "parameters_n_w_g_m_D_s_t_J_L": case,
        "normalized_lowest_seed_block": leading,
        "band_ranks": tuple(band_rows),
    }

    if m == 4:
        shifts = 2
        columns = tuple(
            shift_contact_z(contact, shift)
            for shift in range(shifts)
            for _label, contact in local)
        labels = tuple(
            (shift, *label)
            for shift in range(shifts) for label, _contact in local)
        result["two_layer_selected_invisible_witness"] = relation_witness(
            columns, selected_rows(case, shifts), labels)

    if m == 8:
        # Here all 24 coefficient columns and both shifts are literal/legal.
        source_index = {monomial: index
                        for index, monomial in enumerate(literal.monomials)}
        base = [
            literal.columns[index]
            for index, monomial in enumerate(literal.monomials)
            if sum(monomial[1:]) <= case[7]
        ]
        base_echelon = M.ColumnEchelon()
        for index, column in enumerate(base):
            base_echelon.add(column, index)
        global_columns = []
        for shift in range(2):
            for _label, source in coefficient_sources(literal, case, 3):
                shifted = shift_source_z(source, shift)
                assert all(monomial in source_index for monomial in shifted)
                global_columns.append(TT.indexed_image(
                    literal, shifted, source_index))
        quotient_columns = tuple(base_echelon.reduce(column)
                                 for column in global_columns)
        quotient_rank = sparse_rank(quotient_columns)
        assert quotient_rank == 48
        result["legal_two_layer_global_base_quotient"] = {
            "base_columns": len(base),
            "base_rank": base_echelon.rank,
            "carrier_columns": len(global_columns),
            "carrier_rank_modulo_complete_lower_grade_base": quotient_rank,
            "selected_projection_rank_at_the_error_node":
                band_rows[1]["selected_projection_rank"],
            "selected_invisible_modes_surviving_base_quotient":
                quotient_rank - band_rows[1]["selected_projection_rank"],
        }
    return result


def main():
    M.PRIME = M.T.PRIME = M.F.PRIME = F.PRIME = P
    payload = {
        "scope": (
            "finite exact full-band and column-delay leading-matrix audit; "
            "no forced-residual membership or finite endpoint theorem"
        ),
        "field": P,
        "carrier_order": tuple((jet, a, c)
                               for jet in range(3) for a, c in PAIRS),
        "multiplicity_chambers": tuple(chamber(m)
                                       for m in MULTIPLICITIES),
        "verdict": (
            "the repeated selected-row Toeplitz argument is false; at m=8 "
            "a full-rank column-delay-normalized leading matrix exists, but "
            "the extra complete-contact modes survive the lower-grade base"
        ),
        "remaining_gate": (
            "characterize the forced terminal residual in the full banded "
            "carrier module and close the finite top-tail endpoint"
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
