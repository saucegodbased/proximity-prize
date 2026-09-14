#!/usr/bin/env python3
"""Exact all-defect interval gate for the m69 reciprocal model.

This script generalizes the symbolic Pascal-stratum calculation used by the
old m60 Full187 construction to the robust profile

    (M, slope, curvature, J, L) = (69, 24, 10, 94, 2369).

It enumerates every stratum where the literal coefficient windows fail to
span the raw Pascal block.  For every absent raw associated direction it then
collects every capacity-deficient physical coefficient which could be needed.

The deliberately hostile scalar model is the reciprocal monomial

    R(X) = X^(-e) in F[X]/(X^N - 1),

for e=2049 (the old W133119 endpoint) and e=2151 (the W133221 endpoint).
Multiplication by R^t cyclically shifts a degree-prefix window by -t*e.  The
gate checks that the prefix windows of all higher-contact predecessors cover
all N coefficient coordinates.  It also records the first power at which
coverage becomes complete.

This is an exact GREEN for the monomial interval model only.  It is not a
rank theorem for an arbitrary rational N0/E0, and it does not prove that the
same predecessor freedom can be allocated simultaneously across all missing
physical coefficients.
"""

from __future__ import annotations

from collections import Counter
import hashlib
import json
import resource


N = 262_144
W = 131_071
G = 180_413
M = 69
SLOPE = 24
CURVATURE = 10
J = 94
L = 2_369
D = M * G


def width(y: int, r: int, s: int) -> int:
    return D - W * y - (W - 1) * r - (W - 2) * s


def raw_y_interval(active: int, n: int, s: int) -> tuple[int, ...]:
    if not 0 <= s <= CURVATURE or n + s >= M:
        return ()
    lower = max(0, active - SLOPE)
    upper = min(M - 1, active - s, n + s)
    if upper < lower:
        return ()
    return tuple(range(lower, upper + 1))


def counts(active: int, n: int, legal: bool) -> tuple[int, ...]:
    answer = []
    for s in range(CURVATURE + 1):
        count = 0
        for y in raw_y_interval(active, n, s):
            r = active - y - s
            q = n - y + s
            depth = min(M - y, width(y, r, s) // N)
            if not legal or q < depth:
                count += 1
        answer.append(count)
    return tuple(answer)


def jset(multiplicities: tuple[int, ...], h: int) -> tuple[int, ...]:
    return tuple(sorted(
        h - s for s, count in enumerate(multiplicities)
        if 0 <= h - s < count
    ))


def target_dimension(active: int, n: int, h: int) -> int:
    if not 0 <= h <= min(active, M - n - 1):
        return 0
    return min(h + 1, M - n - h)


def defect_census():
    defects = []
    deficient_shapes = set()
    deficient_coefficients = set()
    for active in range(J):
        for n in range(-CURVATURE, M):
            raw_counts = counts(active, n, False)
            legal_counts = counts(active, n, True)
            if not any(raw_counts):
                continue
            for h in range(min(active, M - n - 1) + 1):
                raw_j = jset(raw_counts, h)
                legal_j = jset(legal_counts, h)
                dimension = target_dimension(active, n, h)
                raw_rank = min(len(raw_j), dimension)
                legal_rank = min(len(legal_j), dimension)
                if legal_rank >= raw_rank:
                    continue
                record = (
                    active, n, h, dimension, raw_j, legal_j,
                    raw_rank - legal_rank,
                )
                defects.append(record)

                # This is intentionally a rank-insensitive superset: retain
                # every absent raw J-direction, even if another choice of a
                # saturated target minor might avoid it.  Passing the larger
                # set makes the interval conclusion safer.
                for j in set(raw_j) - set(legal_j):
                    s = h - j
                    for y in raw_y_interval(active, n, s):
                        r = active - y - s
                        q = n - y + s
                        depth = min(M - y, width(y, r, s) // N)
                        if q >= depth:
                            deficient_shapes.add((y, r, s))
                            deficient_coefficients.add((y, r, s, q))
    return (
        tuple(defects), tuple(sorted(deficient_shapes)),
        tuple(sorted(deficient_coefficients)),
    )


def circular_union_length(intervals: list[tuple[int, int]]) -> int:
    linear = []
    for start, length in intervals:
        assert 0 <= start < N and 0 <= length < N
        end = start + length
        if end <= N:
            linear.append((start, end))
        else:
            linear.append((start, N))
            linear.append((0, end - N))
    linear.sort()
    union = []
    for start, end in linear:
        if not union or start > union[-1][1]:
            union.append([start, end])
        elif end > union[-1][1]:
            union[-1][1] = end
    return sum(end - start for start, end in union)


def first_covering_power(shape: tuple[int, int, int], exponent: int):
    y, r, s = shape
    intervals = []
    fringe_trace = []
    for power in range(M - y):
        fringe = width(y + power, r, s) % N
        shift = (-power * exponent) % N
        intervals.append((shift, fringe))
        fringe_trace.append(fringe)
        if circular_union_length(intervals) == N:
            return power, tuple(fringe_trace)
    return None, tuple(fringe_trace)


def exponent_gate(shapes, exponent: int):
    histogram = Counter()
    witnesses = {}
    failures = []
    receipts = []
    for shape in shapes:
        power, fringes = first_covering_power(shape, exponent)
        histogram[power] += 1
        witnesses.setdefault(power, (shape, fringes))
        receipts.append((shape, power, fringes))
        if power is None:
            failures.append((shape, fringes))
    assert not failures
    assert set(histogram) <= {2, 3}
    return {
        "exponent": exponent,
        "first_covering_power_histogram": tuple(sorted(histogram.items())),
        "representative_witnesses": tuple(sorted(witnesses.items())),
        "all_shapes_cover_by_cubic_power": True,
        "receipt_sha256": hashlib.sha256(
            repr(tuple(receipts)).encode()
        ).hexdigest(),
    }


def full_exponent_range_gate(shapes):
    """Sweep the whole scalar-leaf reciprocal-monomial exponent range.

    The hard-corner inequalities give 2049 <= e <= 18414 even before the
    W133221 improvement raises the lower endpoint to 2151.  Every deficient
    shape has y <= 43, so four predecessor windows are always available.
    Their fringes depend only on the initial fringe because increasing y by
    one subtracts W from the width.
    """
    assert max(y for y, _r, _s in shapes) == 43
    fringes = tuple(sorted({width(y, r, s) % N for y, r, s in shapes}))
    assert len(fringes) == 189
    for y, r, s in shapes:
        initial = width(y, r, s) % N
        assert tuple(width(y + power, r, s) % N for power in range(4)) == (
            tuple((initial - power * W) % N for power in range(4))
        )

    maximum_power_histogram = Counter()
    for exponent in range(2_049, 18_415):
        maximum_power = 0
        for initial in fringes:
            intervals = []
            first = None
            for power in range(4):
                intervals.append((
                    (-power * exponent) % N,
                    (initial - power * W) % N,
                ))
                if circular_union_length(intervals) == N:
                    first = power
                    break
            assert first is not None
            maximum_power = max(maximum_power, first)
        maximum_power_histogram[maximum_power] += 1
    assert maximum_power_histogram == Counter({2: 15_073, 3: 1_293})
    return {
        "reciprocal_exponent_range": (2_049, 18_414),
        "unique_initial_fringes": len(fringes),
        "initial_fringe_ranges": (
            (127_729, 127_729), (127_731, 127_821),
            (127_823, 127_823), (258_802, 258_896),
            (258_898, 258_898),
        ),
        "maximum_power_histogram_over_exponents":
            tuple(sorted(maximum_power_histogram.items())),
        "every_allowed_reciprocal_monomial_covers_by_cubic_power": True,
    }


def main():
    defects, shapes, coefficients = defect_census()
    first_descending = max(defects, key=lambda record: record[0])
    assert first_descending == (63, 44, 24, 1, (14,), (), 1)
    assert len(defects) == 13_093
    assert sum(record[-1] for record in defects) == 54_498
    assert len(shapes) == 6_930
    assert len(coefficients) == 140_153
    assert (39, 14, 10) in shapes
    assert width(39, 14, 10) == 4_191_058
    assert width(39, 14, 10) == 15 * N + 258_898
    assert hashlib.sha256(repr(defects).encode()).hexdigest() == (
        "f9efb41d3fbdd9ca367289cb5cf0467cb849dcc36951efade8bab14be741c4e0"
    )
    assert hashlib.sha256(repr(shapes).encode()).hexdigest() == (
        "e789d4d983053ed615c9c706c87a004f6c96f2c66cc51d6625507cafb0dedeeb"
    )
    assert hashlib.sha256(repr(coefficients).encode()).hexdigest() == (
        "3897a7fa22779bbba328c4a75abeab46c4e193cc05b70e99b60623283aa94f35"
    )

    result = {
        "profile": (M, SLOPE, CURVATURE, J, L),
        "constants": (N, W, G, D),
        "defect_stratum_count": len(defects),
        "total_literal_rank_defect": sum(record[-1] for record in defects),
        "rank_insensitive_deficient_shape_superset_count": len(shapes),
        "rank_insensitive_deficient_coefficient_superset_count":
            len(coefficients),
        "first_descending_defect": first_descending,
        "first_defect_physical_coefficient": (39, 14, 10, 15),
        "first_defect_width_full_levels_fringe_quotient":
            (4_191_058, 15, 258_898, N - 258_898),
        "defect_receipt_sha256": hashlib.sha256(
            repr(defects).encode()
        ).hexdigest(),
        "shape_receipt_sha256": hashlib.sha256(
            repr(shapes).encode()
        ).hexdigest(),
        "coefficient_receipt_sha256": hashlib.sha256(
            repr(coefficients).encode()
        ).hexdigest(),
        "exponent_gates": tuple(
            exponent_gate(shapes, exponent) for exponent in (2_049, 2_151)
        ),
        "full_exponent_range_gate": full_exponent_range_gate(shapes),
        "scope": (
            "exact cyclic interval coverage for the reciprocal monomial; "
            "arbitrary rational rank and simultaneous confluence remain open"
        ),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
