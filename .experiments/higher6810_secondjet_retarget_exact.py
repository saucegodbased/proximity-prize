#!/usr/bin/env python3
"""Exact 6810 -> 6900 retarget audit for the accepted second-jet roots.

The formulas are literal integer transcriptions of the definitions used by
`HigherRootInterpolation6810` and `HigherRootSources6810` at accepted commit
09d8a2a.  This is a cheap falsifier for a proposed direct retarget; it does no
large finite evaluation and normally finishes in under one second.
"""

from dataclasses import dataclass


N = 262_144
W = 131_071
ACCEPTED_A = 181_294
TARGET_A = 180_413


def nsub(a: int, b: int) -> int:
    return max(a - b, 0)


def rectangle(a: int, b: int, c: int) -> int:
    return a * b * c - b * a * (a - 1) // 2 - a * b * (b - 1) // 2


def clipped_rectangle(a: int, b: int, c: int, cap: int) -> int:
    corner = nsub(a + b, 2 + cap)
    outside = 0
    for i in range(corner):
        for j in range(corner - i):
            outside += nsub(nsub(c, nsub(a - 1, i)), nsub(b - 1, j))
    return nsub(rectangle(a, b, c), outside)


def q_value(m: int, s: int, r: int, h: int) -> int:
    return max((m - r + 1) // 2, nsub(nsub(m, r), nsub(s, h)))


def relaxed_rank_bound(m: int, L: int, B: int, s: int, U: int) -> int:
    source = 0
    kernel = 0
    for r in range(m):
        for h in range(s + 1):
            source += clipped_rectangle(r + 1, nsub(B, 2 * h) + 1,
                                        nsub(L + 1, h), nsub(U, h))
            q = q_value(m, s, r, h)
            if q <= r and nsub(m, r) + 2 * h <= B:
                kernel += clipped_rectangle(
                    nsub(r, q) + 1,
                    nsub(nsub(B, 2 * h), q) + 1,
                    nsub(nsub(L + 1, h), q),
                    nsub(nsub(U, h), q),
                )
    return source - kernel


def reserve(k: int, n0: int, h: int) -> int:
    return h if h < n0 else k


def cutoff(agreement: int, m: int, k: int, n0: int, h: int) -> int:
    # 50225 in the accepted source is 181294 - 131071 + 2.
    return nsub(m * agreement, reserve(k, n0, h) * (agreement - W + 2))


def coefficient_count(agreement: int, m: int, L: int, B: int,
                      s: int, U: int, k: int, n0: int) -> int:
    answer = 0
    for h in range(s + 1):
        for r in range(nsub(B, 2 * h) + 1):
            budget = nsub(
                nsub(cutoff(agreement, m, k, n0, h), (W - 2) * h),
                (W - 1) * r,
            )
            width = nsub(nsub(L + 1, h), r)
            columns = min(nsub(budget, 1) // W + 1,
                          nsub(nsub(U + 1, h), r))
            answer += (
                columns * budget * width
                + W * columns * (columns - 1) * (2 * columns - 1) // 6
                - (budget + W * width) * columns * (columns - 1) // 2
            )
    return answer


def cap_slack(agreement: int, p: "Profile", h: int) -> int:
    return (cutoff(agreement, p.m, p.k, p.n0, h) + p.B - 1) // W - p.U


def margin(agreement: int, p: "Profile") -> int:
    return coefficient_count(agreement, p.m, p.L, p.B, p.s, p.U,
                             p.k, p.n0) - N * relaxed_rank_bound(
                                 p.m, p.L, p.B, p.s, p.U)


@dataclass(frozen=True)
class Profile:
    name: str
    m: int
    B: int
    s: int
    U: int
    L: int
    k: int
    n0: int
    accepted_coefficient: int
    accepted_rank: int
    accepted_margin: int
    target_margin: int


PROFILES = (
    Profile("P0", 132, 54, 24, 180, 1800, 5, 7,
            2_102_627_697_450_660, 8_019_382_406, 394_716_012_196,
            -22_425_433_492_499),
    Profile("P1", 134, 56, 25, 180, 2749, 6, 8,
            3_566_543_683_158_980, 13_605_267_182, 4_523_000_772,
            -38_371_960_126_026),
    Profile("P2", 136, 56, 25, 185, 2526, 6, 8,
            3_384_947_870_141_283, 12_912_535_762, 4_095_347_555,
            -36_795_509_129_843),
    Profile("P3", 116, 46, 21, 158, 2695, 5, 7,
            1_844_470_489_720_046, 7_036_093_956, 675_718_382,
            -19_989_964_001_229),
)


NEARBY_SOURCE_ONLY = (
    Profile("same-P0-k2", 132, 54, 24, 180, 1800, 2, 3,
            0, 0, 0, 76_488_022_735),
    Profile("scan-first-k4", 148, 66, 30, 200, 5360, 4, 5,
            0, 0, 0, 5_559_679_537),
    Profile("scan-best-top-cell-k4", 148, 64, 30, 200, 5465, 4, 5,
            0, 0, 0, 3_553_593_355),
)


def audit() -> None:
    assert N - TARGET_A == 81_731
    assert TARGET_A - W == 49_342
    print(f"target agreement={TARGET_A} errors={N-TARGET_A} gap={TARGET_A-W}")
    for p in PROFILES:
        rank = relaxed_rank_bound(p.m, p.L, p.B, p.s, p.U)
        accepted_coefficient = coefficient_count(
            ACCEPTED_A, p.m, p.L, p.B, p.s, p.U, p.k, p.n0)
        assert rank == p.accepted_rank
        assert accepted_coefficient == p.accepted_coefficient
        assert accepted_coefficient - N * rank == p.accepted_margin
        target = margin(TARGET_A, p)
        assert target == p.target_margin
        slacks = [cap_slack(TARGET_A, p, h) for h in range(p.s + 1)]
        first_bad = next((h for h, x in enumerate(slacks) if x < 0), None)
        # In the stable affine chamber, this difference is the exact L slope.
        p_next = Profile(p.name, p.m, p.B, p.s, p.U, p.L + 1, p.k,
                         p.n0, 0, 0, 0, 0)
        slope = margin(TARGET_A, p_next) - target
        print(
            f"{p.name}: accepted={p.accepted_margin} target={target} "
            f"cap_min={min(slacks)} first_bad_h={first_bad} L_slope={slope}"
        )
        assert target < 0 and slope < 0

    print("source-positive nearby profiles (existence gate only):")
    for p in NEARBY_SOURCE_ONLY:
        got = margin(TARGET_A, p)
        slack = min(cap_slack(TARGET_A, p, h) for h in range(p.s + 1))
        assert got == p.target_margin and slack >= 0
        print(f"{p.name}: params={(p.m,p.B,p.s,p.U,p.L,p.k,p.n0)} "
              f"margin={got} cap_min={slack}")

    # Exact scalar-list source gate, independently reproduced by the companion
    # checker higher6810_to_6900_numeric_retarget.py.
    assert 44_576_389_865 - N * 171_885 == -482_231_575
    print("scalar (113,156,34): target margin=-482231575")


if __name__ == "__main__":
    audit()
