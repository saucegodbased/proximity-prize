#!/usr/bin/env python3
"""Exact all-Hasse audit of the Full187 terminal locally free shapes.

The q=0 low-T matrix is built by
``full187_terminal_lowT_corner_matrix_6900.py``.  This independent audit
reconstructs its obstruction predicate, characterizes its 105 individually
zero agreement-only columns, then repeats the test with the stronger affine
CRT threshold needed to retain arbitrary error-node values.  Finally it checks
every surviving coefficient-Hasse order q on the resulting 103 shapes.

An origin is called locally licensed when either its scalar agreement-Hermite
capacity is nonnegative or the sharp order-two leading pivot exists.  This is
strictly a local statement.  It does not assert confluence of pivot tails,
four-packet containment, or the THREE-RHS theorem.
"""

from __future__ import annotations

from collections import Counter
import hashlib
import json
from pathlib import Path
import resource


N = 262_144
W = 131_071
G = 180_413
M = 60
D = M * G
J = 82
SLOPE = 21
CURVATURE = 10
ERRORS = N - G


def width(f: int, r: int, s: int) -> int:
    return D - W * f - (W - 1) * r - (W - 2) * s


def compact_free_shape(r: int, s: int) -> bool:
    """Closed form for the 105 agreement-only locally free columns."""
    return (
        0 <= s <= 8
        and 0 <= r
        and r + s <= SLOPE
        and r + s + max(0, 3 * s - 17) <= 16
    )


def compact_affine_free_shape(r: int, s: int) -> bool:
    """Closed form for the 103 arbitrary-error locally free columns."""
    return compact_free_shape(r, s) and (s <= 6 or r + 4 * s <= 32)


def origin_status(r: int, s: int, f: int, a_e: int, c_s: int, q: int,
                  required_margin: int):
    """Return capacity, pivot, or obstruction for one surviving origin."""
    base_weight = f + 2 * a_e + c_s
    assert min(r, s, f, a_e, c_s, q) >= 0
    assert a_e + c_s <= f
    assert base_weight + q < M

    depth = M - (base_weight + q)
    margin = width(f, r, s) - G * depth
    T = q + f - a_e + c_s
    E = a_e
    R = f - a_e - c_s + r
    S = s + c_s
    h = J - r - s - f
    row = (T, E, R, S, h)
    if margin >= required_margin:
        return "capacity", row, margin

    d = E + R + S
    residual = max(E + S - CURVATURE, 0)
    minimum_a0 = max(0, d - SLOPE)
    maximum_a0 = min(R, T - 2 * residual)
    if minimum_a0 <= maximum_a0:
        return "pivot", row, margin
    return "obstruction", row, margin


def q0_obstruction_shapes(shapes, required_margin):
    obstruction_shapes = set()
    zero_shapes = set()
    for r, s in shapes:
        has_obstruction = False
        y = J - r - s
        for f in range(M):
            assert f <= y
            for a_e in range(f + 1):
                for c_s in range(f - a_e + 1):
                    if f + 2 * a_e + c_s >= M:
                        continue
                    status, _, _ = origin_status(
                        r, s, f, a_e, c_s, 0, required_margin)
                    has_obstruction |= status == "obstruction"
        (obstruction_shapes if has_obstruction else zero_shapes).add((r, s))
    return zero_shapes, obstruction_shapes


def lost_shape_witnesses(lost_shapes):
    records = []
    for r, s in sorted(lost_shapes):
        y = J - r - s
        for f in range(M):
            for a_e in range(f + 1):
                for c_s in range(f - a_e + 1):
                    if f + 2 * a_e + c_s >= M:
                        continue
                    status, row, margin = origin_status(
                        r, s, f, a_e, c_s, 0, ERRORS)
                    if status == "obstruction":
                        records.append((r, s, f, a_e, c_s, y - f,
                                        margin, row))
    assert records == [
        (1, 8, 3, 3, 0, 70, 50_882, (0, 3, 1, 8, 70)),
        (5, 7, 4, 4, 0, 66, 67_839, (0, 4, 5, 7, 66)),
    ]
    return tuple(records)


def all_hasse_receipt(free_shapes, required_margin):
    counts = Counter()
    q0_rows = set()
    positive_rows = set()
    q0_structured_rows = set()
    positive_structured_rows = set()
    maximum_q = 0
    minimum_positive_capacity_margin = None
    minimum_positive_pivot_margin = None

    for r, s in sorted(free_shapes):
        y = J - r - s
        for f in range(M):
            assert f <= y
            for a_e in range(f + 1):
                for c_s in range(f - a_e + 1):
                    base_weight = f + 2 * a_e + c_s
                    if base_weight >= M:
                        continue
                    for q in range(M - base_weight):
                        status, row, margin = origin_status(
                            r, s, f, a_e, c_s, q, required_margin)
                        # u1^h is retained as part of the row key.  There is
                        # no division by this passive factor.
                        assert row[-1] == y - f >= 0
                        q_class = "q0" if q == 0 else "q_positive"
                        counts[(q_class, "origins")] += 1
                        counts[(q_class, status)] += 1
                        maximum_q = max(maximum_q, q)
                        if q == 0:
                            q0_rows.add(row)
                            if status == "pivot":
                                q0_structured_rows.add(row)
                        else:
                            positive_rows.add(row)
                            if status == "capacity":
                                minimum_positive_capacity_margin = (
                                    margin if minimum_positive_capacity_margin is None
                                    else min(minimum_positive_capacity_margin, margin)
                                )
                            elif status == "pivot":
                                positive_structured_rows.add(row)
                                minimum_positive_pivot_margin = (
                                    margin if minimum_positive_pivot_margin is None
                                    else min(minimum_positive_pivot_margin, margin)
                                )

    assert counts[("q0", "obstruction")] == 0
    assert counts[("q_positive", "obstruction")] == 0
    assert required_margin == ERRORS
    assert counts == Counter({
        ("q0", "origins"): 697_825,
        ("q0", "capacity"): 676_776,
        ("q0", "pivot"): 21_049,
        ("q_positive", "origins"): 10_547_200,
        ("q_positive", "capacity"): 10_498_193,
        ("q_positive", "pivot"): 49_007,
    })
    assert (len(q0_rows), len(positive_rows)) == (200_080, 289_765)
    assert len(q0_rows & positive_rows) == 184_885
    assert len(positive_rows - q0_rows) == 104_880
    assert (len(q0_structured_rows), len(positive_structured_rows)) == (
        8_133, 6_358)
    assert len(q0_structured_rows & positive_structured_rows) == 6_327
    assert len(positive_structured_rows - q0_structured_rows) == 31
    assert maximum_q == 59

    return {
        "origin_counts_by_q_class_and_license": tuple(
            (q_class, status, counts[(q_class, status)])
            for q_class in ("q0", "q_positive")
            for status in ("origins", "capacity", "pivot", "obstruction")
        ),
        "maximum_surviving_q": maximum_q,
        "distinct_contact_rows_q0_qpositive_intersection_new_positive": (
            len(q0_rows), len(positive_rows), len(q0_rows & positive_rows),
            len(positive_rows - q0_rows)),
        "distinct_structured_pivot_rows_q0_qpositive_intersection_new_positive": (
            len(q0_structured_rows), len(positive_structured_rows),
            len(q0_structured_rows & positive_structured_rows),
            len(positive_structured_rows - q0_structured_rows)),
        "minimum_margin_among_positive_q_capacity_origins":
            minimum_positive_capacity_margin,
        "minimum_margin_among_positive_q_pivot_origins":
            minimum_positive_pivot_margin,
    }


def main() -> None:
    shapes = tuple(
        (r, s)
        for s in range(CURVATURE + 1)
        for r in range(SLOPE - s + 1)
    )
    assert len(shapes) == 187
    q0_zero, q0_nonzero = q0_obstruction_shapes(shapes, required_margin=0)
    agreement_closed_form = {
        shape for shape in shapes if compact_free_shape(*shape)}
    assert q0_zero == agreement_closed_form
    assert (len(q0_zero), len(q0_nonzero)) == (105, 82)

    affine_zero, affine_nonzero = q0_obstruction_shapes(
        shapes, required_margin=ERRORS)
    affine_closed_form = {
        shape for shape in shapes if compact_affine_free_shape(*shape)}
    assert affine_zero == affine_closed_form
    assert (len(affine_zero), len(affine_nonzero)) == (103, 84)
    assert q0_zero - affine_zero == {(5, 7), (1, 8)}

    row_lengths = tuple(
        sum((r, s) in q0_zero for r in range(SLOPE - s + 1))
        for s in range(CURVATURE + 1)
    )
    assert row_lengths == (17, 16, 15, 14, 13, 12, 10, 6, 2, 0, 0)
    affine_row_lengths = tuple(
        sum((r, s) in affine_zero for r in range(SLOPE - s + 1))
        for s in range(CURVATURE + 1)
    )
    assert affine_row_lengths == (17, 16, 15, 14, 13, 12, 10, 5, 1, 0, 0)

    stable = {
        "scope": (
            "exact local affine-CRT/order-two-pivot closure of the 103 "
            "strongly q=0-zero terminal columns through every surviving q; "
            "not global pivot-tail confluence or THREE-RHS containment"
        ),
        "target_P_N_w_g_m_D_J_slope_curvature": (
            2_130_706_433, N, W, G, M, D, J, SLOPE, CURVATURE),
        "agreement_only_105_shape_inequality": (
            "0<=s<=8 and r+s+max(0,3s-17)<=16"
        ),
        "agreement_only_shape_count_and_s_row_lengths":
            (len(q0_zero), row_lengths),
        "affine_103_shape_inequality": (
            "agreement inequality and (s<=6 or r+4s<=32)"
        ),
        "affine_shape_count_and_s_row_lengths":
            (len(affine_zero), affine_row_lengths),
        "agreement_safe_but_not_affine_safe_shapes": tuple(
            sorted(q0_zero - affine_zero)),
        "unique_q0_affine_obstruction_witnesses_r_s_f_aE_cS_h_margin_row":
            lost_shape_witnesses(q0_zero - affine_zero),
        "all_hasse_affine_receipt": all_hasse_receipt(
            affine_zero, required_margin=ERRORS),
        "monotonicity": {
            "capacity": (
                "margin(q)=margin(0)+g*q, so margin(q)<ERRORS implies "
                "margin(0)<ERRORS"
            ),
            "local_pivot": (
                "only T changes, as T(q)=T(0)+q; hence pivot failure at q "
                "implies pivot failure at q=0"
            ),
            "survival": (
                "q+f+2aE+cS<m implies f+2aE+cS<m"
            ),
        },
        "verdict": {
            "GREEN": (
                "Every origin from each of the 103 strong shapes is locally "
                "licensed for arbitrary error values or by the sharp pivot, "
                "for every surviving q=0..59."
            ),
            "NOT_CLOSED": (
                "Positive Hasse tails create 104880 contact-row keys absent "
                "from the q=0 row set (31 are new structured-pivot keys). "
                "They are locally licensed, but a global triangular/confluence "
                "proof is still required before calling this a closed terminal "
                "subspace."
            ),
        },
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
