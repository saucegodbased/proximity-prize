#!/usr/bin/env python3
"""Exact q=0 terminal matrix on the unresolved Full187 low-T corner.

This is a deliberately narrow discriminator.  The complete terminal source
has one active-grade-82 shape for every ``(r,s)`` with ``r+s<=21,s<=10``.
After the agreement-Hermite capacity test and the already proved sharp local
order-two pivots, the only unlicensed q=0 rows obey

  T < max(0,E+R+S-21) + 2*max(E+S-10,0).

The script forms their literal multinomial coefficient matrix.  Columns are
the 187 terminal shapes, rows retain ``(T,E,R,S,h)``, and coefficients are
computed in the benchmark characteristic.  Its rank is a necessary local
fact about the terminal connecting map; it is not a global Hermite or
THREE-RHS theorem.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from math import comb
import hashlib
import json
from pathlib import Path
import resource


P = 2_130_706_433
N = 262_144
W = 131_071
G = 180_413
M = 60
D = M * G
J = 82
SLOPE = 21
CURVATURE = 10
FULL_SOURCE_SURPLUS = 9_757_693


def width(y: int, r: int, s: int) -> int:
    return D - W * y - (W - 1) * r - (W - 2) * s


def multinomial3(total: int, a: int, c: int) -> int:
    return comb(total, a) * comb(total - a, c)


def sparse_rank(columns: tuple[dict[tuple, int], ...]):
    """Exact column echelon rank and pivot rows over F_P."""
    pivots: dict[tuple, dict[tuple, int]] = {}
    dependencies = []
    for column_index, source in enumerate(columns):
        vector = {row: value % P for row, value in source.items() if value % P}
        while vector:
            pivot = min(vector)
            old = pivots.get(pivot)
            if old is None:
                inverse = pow(vector[pivot], -1, P)
                pivots[pivot] = {
                    row: value * inverse % P
                    for row, value in vector.items() if value * inverse % P
                }
                break
            scale = vector[pivot]
            for row, value in old.items():
                new = (vector.get(row, 0) - scale * value) % P
                if new:
                    vector[row] = new
                else:
                    vector.pop(row, None)
        else:
            dependencies.append(column_index)
    return len(pivots), tuple(pivots), tuple(dependencies)


def main() -> None:
    shapes = tuple(
        (r, s)
        for s in range(CURVATURE + 1)
        for r in range(SLOPE - s + 1)
    )
    assert len(shapes) == 187
    inverse_two = pow(2, -1, P)
    columns = []
    row_origins = defaultdict(list)
    entry_count = 0
    deficit_histogram = Counter()

    for shape_index, (r, s) in enumerate(shapes):
        y = J - r - s
        top_width = width(y, r, s)
        column = {}
        for f in range(M):
            h = y - f
            lower_width = width(f, r, s)
            for a_e in range(f + 1):
                for c_s in range(f - a_e + 1):
                    contact_weight = f + 2 * a_e + c_s
                    if contact_weight >= M:
                        continue
                    depth = M - contact_weight
                    if lower_width >= G * depth:
                        continue
                    T = f - a_e + c_s
                    E = a_e
                    R = f - a_e - c_s + r
                    S = s + c_s
                    d = E + R + S
                    residual = max(E + S - CURVATURE, 0)
                    minimum_a0 = max(0, d - SLOPE)
                    maximum_a0 = min(R, T - 2 * residual)
                    if minimum_a0 <= maximum_a0:
                        continue
                    assert R >= minimum_a0
                    assert T < minimum_a0 + 2 * residual
                    deficit = minimum_a0 + 2 * residual - T
                    row = (T, E, R, S, h)
                    coefficient = (
                        comb(y, f)
                        * multinomial3(f, a_e, c_s)
                        * pow(-inverse_two % P, c_s, P)
                    ) % P
                    assert coefficient
                    assert row not in column
                    column[row] = coefficient
                    row_origins[row].append(
                        (shape_index, r, s, f, a_e, c_s, deficit)
                    )
                    deficit_histogram[deficit] += 1
                    entry_count += 1
        columns.append(column)

    columns = tuple(columns)
    rows = tuple(sorted(row_origins))
    assert entry_count == 15_338
    assert len(rows) == 7_726
    rank, pivot_rows, dependent_columns = sparse_rank(columns)
    zero_columns = tuple(
        index for index, column in enumerate(columns) if not column
    )
    safe_shapes = tuple(
        shape for shape in shapes
        if shape[0] + shape[1] <= 16
        and shape[0] + 4 * shape[1] <= 33
    )
    assert len(safe_shapes) == 105
    assert tuple(shapes[index] for index in zero_columns) == safe_shapes
    # Every unsafe shape owns a pivot after the exact lower-prefix reduction;
    # there are no further q=0 cancellations between unsafe shapes.
    assert rank == len(columns) - len(zero_columns) == 82
    assert dependent_columns == zero_columns
    safe_top_width = sum(width(J - r - s, r, s) for r, s in safe_shapes)
    unsafe_top_width = sum(
        width(J - r - s, r, s)
        for r, s in shapes if (r, s) not in safe_shapes
    )
    assert (safe_top_width, unsafe_top_width) == (8_081_883, 6_312_464)
    assert safe_top_width + unsafe_top_width == 14_394_347
    restricted_surplus = FULL_SOURCE_SURPLUS - unsafe_top_width
    assert restricted_surplus == 3_445_229
    assert restricted_surplus - 4 == 3_445_225
    multiplicity_histogram = Counter(len(origins) for origins in row_origins.values())
    support_histogram = Counter(len(column) for column in columns)
    stable = {
        "scope": (
            "exact q=0 low-T associated-graded terminal discriminator; "
            "not a global confluence, Hermite, or THREE-RHS theorem"
        ),
        "field_and_target_P_N_w_g_m_D_J_slope_curvature":
            (P, N, W, G, M, D, J, SLOPE, CURVATURE),
        "terminal_shape_count": len(shapes),
        "row_and_entry_counts": (len(rows), entry_count),
        "row_origin_multiplicity_histogram": tuple(sorted(
            multiplicity_histogram.items())),
        "column_support_histogram": tuple(sorted(support_histogram.items())),
        "zero_column_shapes": tuple(shapes[index] for index in zero_columns),
        "zero_corner_shape_characterization": (
            "r+s<=16 and r+4s<=33"
        ),
        "zero_corner_shape_count": len(safe_shapes),
        "matrix_rank_nullity": (rank, len(columns) - rank),
        "target_dimension_receipt": {
            "full_source_surplus": FULL_SOURCE_SURPLUS,
            "safe_terminal_top_width": safe_top_width,
            "pruned_unsafe_terminal_top_width": unsafe_top_width,
            "surplus_after_pruning_unsafe_shapes": restricted_surplus,
            "surplus_after_four_boundary_linear_conditions":
                restricted_surplus - 4,
            "warning": (
                "Positive Euler surplus is not a contact-rank or boundary-"
                "surjectivity theorem."
            ),
        },
        "dependent_column_shapes": tuple(
            shapes[index] for index in dependent_columns),
        "pivot_row_count": len(pivot_rows),
        "deficit_histogram_by_occurrence": tuple(sorted(
            deficit_histogram.items())),
        "decision": (
            "Q0_CORNER_MAP_PRUNES_EXACTLY_82_AND_LEAVES_105_SHAPES"
        ),
        "scope_guard": (
            "The 105-shape coordinate kernel follows only after quotienting "
            "by the capacity and sharp local leading rows.  Global tail "
            "orientation and the four target residues are still unproved."
        ),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    payload = {
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
