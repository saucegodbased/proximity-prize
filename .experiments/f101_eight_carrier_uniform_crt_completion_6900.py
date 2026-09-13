#!/usr/bin/env python3
"""Exact global CRT completion for the eight order-four carriers.

The tiny n=10 extraction used tapered multiplier caps

    deg p[a,c] <= 3e - 1 - (a+c),

which leave 24e-16 coefficients.  Full187 does not require this taper: its
independently checked raw-width inequalities allow the uniform cap

    deg p[a,c] < 3e

for all eight carriers.  This script checks, over the literal F101 m=4
control with arbitrary received-direction offsets, that the sixteen newly
admitted top coefficients raise the *global* selected error-contact map from
rank 56 to rank 72.  It also checks that every one of the sixteen columns is
necessary relative to the tapered space, and that passive Z shifts preserve
the matrix exactly after shifting the selected seed rows.

This is an exact finite receipt for the CRT/local-contact interface.  It does
not prove that these selected rows exhaust the complete terminal residual or
that higher-seed leakage is globally confluent.
"""

from __future__ import annotations

import hashlib
import json
import sys

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import f101_order4_eight_carrier_local_jet_block_6900 as E  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402


P = 101
CASE = E.CASE
PAIRS = E.PAIRS
ERRORS = tuple(range(7, 10))
UNIFORM_MAX_DEGREE = 3 * len(ERRORS) - 1


def x_monomial(power):
    return (0,) * power + (1,)


def shift_z(source, shift):
    return {
        (x, y, r, s, z + shift): coefficient
        for (x, y, r, s, z), coefficient in source.items()
    }


def selected_rows(shift=0):
    """Rows grouped by error, Hasse order, then local carrier pivot."""
    b = CASE[7] + 1 - CASE[3]
    return tuple(
        (node, jet, 0, c, 0, b + a + c + shift)
        for node in ERRORS
        for jet in range(3)
        for a, c in PAIRS
    )


def contact_column(literal, pair, power, offsets, deltas, shift=0):
    source = E.carrier(literal, *pair)
    source = E.scale_by_poly(source, x_monomial(power))
    source = shift_z(source, shift)
    result = {}
    for node, offset, delta in zip(ERRORS, offsets, deltas):
        received_direction = (F.poly_eval(literal.q, node) + offset) % P
        local = E.local_contact(
            source, node, delta, received_direction, CASE[3])
        for row, coefficient in local.items():
            result[(node,) + row] = coefficient
    return result


def matrix_from_columns(rows, columns):
    matrix = nmod_mat(len(rows), len(columns), [
        column.get(row, 0)
        for row in rows
        for column in columns
    ], P)
    return matrix


def columns_for_tags(literal, tags, offsets, deltas, shift=0):
    return tuple(
        contact_column(literal, pair, power, offsets, deltas, shift)
        for pair, power in tags
    )


def entries(matrix):
    return tuple(
        int(matrix[i, j]) % P
        for i in range(matrix.nrows())
        for j in range(matrix.ncols())
    )


def one_sweep(offsets, deltas):
    literal = M.build_case(
        "eight_carrier_uniform_global_crt", CASE, 7, 7, 4,
        error_direction_offsets=offsets)

    tapered_tags = tuple(
        ((a, c), power)
        for a, c in PAIRS
        for power in range(3 * len(ERRORS) - (a + c))
    )
    added_tags = tuple(
        ((a, c), power)
        for a, c in PAIRS
        for power in range(3 * len(ERRORS) - (a + c),
                           3 * len(ERRORS))
    )
    uniform_tags = tapered_tags + added_tags

    assert len(tapered_tags) == 56
    assert len(added_tags) == sum(a + c for a, c in PAIRS) == 16
    assert len(uniform_tags) == 72
    assert len(set(uniform_tags)) == 72

    uniform_columns = columns_for_tags(
        literal, uniform_tags, offsets, deltas)
    tapered_columns = uniform_columns[:len(tapered_tags)]
    added_columns = uniform_columns[len(tapered_tags):]
    rows = selected_rows()
    tapered = matrix_from_columns(rows, tapered_columns)
    completed = matrix_from_columns(rows, uniform_columns)
    assert (tapered.nrows(), tapered.ncols(), tapered.rank()) == (72, 56, 56)
    assert (completed.nrows(), completed.ncols(), completed.rank()) == \
        (72, 72, 72)
    determinant = int(completed.det()) % P
    assert determinant

    # Sixteen columns close a rank-sixteen deficit.  Consequently each one
    # is necessary, but check every ablation directly rather than infer it.
    ablation_ranks = []
    for omitted in range(len(added_tags)):
        columns = tapered_columns + tuple(
            column for index, column in enumerate(added_columns)
            if index != omitted)
        rank = matrix_from_columns(rows, columns).rank()
        assert rank == 71
        ablation_ranks.append((added_tags[omitted], rank))

    # Multiplication by Z merely shifts all selected seed exponents.  Check
    # the whole matrix, not just its rank, through every small-control layer.
    shift_checks = []
    base_entries = entries(completed)
    for shift in range(CASE[8] - CASE[7]):
        shifted_columns = columns_for_tags(
            literal, uniform_tags, offsets, deltas, shift=shift)
        shifted = matrix_from_columns(selected_rows(shift), shifted_columns)
        assert entries(shifted) == base_entries
        shift_checks.append((shift, shifted.rank(), int(shifted.det()) % P))

    return {
        "offsets": offsets,
        "deltas": deltas,
        "tapered_shape_rank": (
            tapered.nrows(), tapered.ncols(), tapered.rank()),
        "uniform_shape_rank": (
            completed.nrows(), completed.ncols(), completed.rank()),
        "uniform_determinant": determinant,
        "added_tags_pair_and_X_power": added_tags,
        "added_column_ablation_ranks": tuple(ablation_ranks),
        "all_sixteen_added_columns_individually_necessary": True,
        "passive_Z_shift_matrix_checks_shift_rank_det": tuple(shift_checks),
    }


def main():
    M.T.PRIME = M.F.PRIME = F.PRIME = P

    # Use distinct arbitrary offsets and residual values, plus a second
    # nondegenerate chamber, to catch accidental cancellation in one sample.
    sweeps = (
        one_sweep((3, 5, 7), (1, 9, 17)),
        one_sweep((11, 19, 23), (2, 13, 29)),
    )

    target_e = 81731
    target_max_degree = 3 * target_e - 1
    old_dimensions = tuple(
        3 * target_e - (a + c) for a, c in PAIRS)
    new_dimensions = (3 * target_e,) * len(PAIRS)
    restored_by_pair = tuple(
        ((a, c), new - old)
        for (a, c), old, new in zip(PAIRS, old_dimensions, new_dimensions)
    )
    assert sum(old_dimensions) == 24 * target_e - 16
    assert sum(new_dimensions) == 24 * target_e
    assert sum(new - old for old, new in zip(
        old_dimensions, new_dimensions)) == 16
    assert target_max_degree == 245192

    payload = {
        "scope": (
            "exact global F101 three-jet/contact completion and target "
            "dimension/width join; complete terminal-state identification "
            "and higher-seed confluence remain separate"
        ),
        "field": P,
        "small_case_n_w_g_m_D_s_t_J_L": CASE,
        "carrier_pairs_a_c": PAIRS,
        "sweeps": sweeps,
        "target_error_count": target_e,
        "old_tapered_dimensions": old_dimensions,
        "uniform_dimensions": new_dimensions,
        "restored_dimensions_by_pair": restored_by_pair,
        "restored_total": 16,
        "target_uniform_inclusive_max_degree": target_max_degree,
        "target_uniform_worst_endpoint_margin_from_71a3e44": 704064,
        "conclusion": (
            "the sixteen-dimensional CRT deficit is eliminated by the "
            "smallest possible adjustment: admit the a+c already-width-safe "
            "top coefficients in carrier (a,c); no new carrier and no "
            "forced-residual compatibility hypothesis is needed"
        ),
        "honest_remaining_gate": (
            "prove that the complete terminal residual is exactly the "
            "selected 24e three-jet state and control all strictly "
            "higher-seed leakage in the 2621-layer assembly"
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(
        canonical.encode()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
