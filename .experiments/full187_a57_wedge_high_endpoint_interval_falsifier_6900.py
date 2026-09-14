#!/usr/bin/env python3
"""Exact cyclic-interval falsifier for the strengthened A57 endpoint.

This deliberately grants all 300 mixed direct channels independent residual
windows.  It compares the favorable boundary monomial pair with a second pair
which satisfies the same two degree lower bounds but retains a large suffix
defect.  It is a support-envelope test, not a rank claim for the correlated
physical source and not an inhabitant of the complete DataEleven leaf.
"""

from __future__ import annotations

import json


N = 262_144


def fringe(total_power: int) -> int:
    return (208_036 + total_power if total_power % 2 == 0
            else 76_964 + total_power)


def cyclic_intervals(start: int, length: int) -> list[tuple[int, int]]:
    """Half-open ordinary intervals for a cyclic interval in Z/N."""
    end = start + length
    if end <= N:
        return [(start, end)]
    return [(start, N), (0, end - N)]


def envelope(degree0: int, degree1: int) -> tuple[int, tuple[tuple[int, int], ...]]:
    intervals: list[tuple[int, int]] = []
    for total_power in range(24):
        width = fringe(total_power)
        for power0 in range(total_power + 1):
            shift = (power0 * degree0
                     + (total_power - power0) * degree1) % N
            intervals.extend(cyclic_intervals(shift, width))
    intervals.sort()
    merged: list[list[int]] = []
    for start, end in intervals:
        if not merged or start > merged[-1][1]:
            merged.append([start, end])
        elif end > merged[-1][1]:
            merged[-1][1] = end
    covered = sum(end - start for start, end in merged)
    missing: list[tuple[int, int]] = []
    cursor = 0
    for start, end in merged:
        if cursor < start:
            missing.append((cursor, start))
        cursor = end
    if cursor < N:
        missing.append((cursor, N))
    return covered, tuple(missing)


def main() -> None:
    favorable = envelope(237_212, 133_222)
    hostile = envelope(262_143, 262_142)
    assert favorable == (N, ())
    assert hostile == (208_082, ((208_036, 262_098),))
    assert 133_222 <= 262_142
    assert 237_212 + 24_931 <= 262_143
    print(json.dumps({
        "scope": "independent 300-channel cyclic support envelope",
        "favorable_pair_degrees": (237_212, 133_222),
        "favorable_covered_and_missing": favorable,
        "hostile_pair_degrees": (262_143, 262_142),
        "hostile_covered_and_missing": hostile,
        "hostile_defect": N - hostile[0],
        "degree_guards": {
            "every_nonzero_direction_at_least": 262_142,
            "projective_threshold": 133_222,
            "wedge_base_plus_max_feasible_ell": 237_212 + 24_931,
            "maximum_row_degree": 262_143,
        },
        "decision": (
            "RED: projective-high plus wedge-wrap degree inequalities do not "
            "force direct A57 envelope surjectivity"
        ),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
