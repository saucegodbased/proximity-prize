#!/usr/bin/env python3
"""Exact arithmetic audit of the accepted Higher*6810 interpolation profiles.

This is intentionally independent of Lean evaluation and uses only Python
integers.  The formulas are direct transcriptions of `RCN100.coefficientCount`,
`RCN119.localRankBound`, and the seedless `RCN279`/`RCN285` analogues imported
by commit 09d8a2a.  It answers the first retarget question: can the accepted
6810 profiles simply be replayed at agreement 180413 (score 6900)?

`--search` additionally checks a large, explicitly bounded seedless-profile
family.  That finite search is evidence about nearby/scaled profiles, not a
theorem about every possible interpolation support.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass


N = 262_144
W = 131_071
FIELD_ORDER = 2_130_706_433
ACCEPTED_AGREEMENT = 181_294
TARGET_AGREEMENT = 180_413
TARGET_ERRORS = N - TARGET_AGREEMENT


def sum1(k: int) -> int:
    return k * (k + 1) // 2


def sum2(k: int) -> int:
    return k * (k + 1) * (2 * k + 1) // 6


def rectangular_triangle_count(M: int, L: int, s: int) -> int:
    """sum_{i=0..M,j=0..s} (L+1-i-j), in the nontruncated regime."""
    if M < 0 or s < 0:
        return 0
    if M + s > L:
        # This fallback is not reached by any accepted profile.  Keeping it
        # makes the checker truthful on arbitrary small exploratory inputs.
        answer = 0
        for j in range(s + 1):
            top = min(M, L - j)
            if top >= 0:
                answer += (top + 1) * (L + 1 - j) - sum1(top)
        return answer
    return (
        (M + 1) * (s + 1) * (L + 1)
        - (s + 1) * sum1(M)
        - (M + 1) * sum1(s)
    )


def coefficient_count(D: int, L: int, s: int) -> int:
    """`RCN100.coefficientCount D W L s`, evaluated in O(s)."""
    answer = 0
    for j in range(s + 1):
        height = L + 1 - j
        weight = D - (W - 1) * j
        if height <= 0 or weight <= 0:
            continue
        top = min(height - 1, (weight - 1) // W)
        if top < 0:
            continue
        count = top + 1
        answer += (
            count * height * weight
            - (height * W + weight) * sum1(top)
            + W * sum2(top)
        )
    return answer


def local_rank_bound(m: int, L: int, s: int) -> int:
    """`RCN119.localRankBound m L s`, evaluated in O(m)."""
    answer = 0
    for r in range(m):
        M = min(r, L)
        h = min(r + 1, m - r)
        block_input = rectangular_triangle_count(M, L, s)
        reduced_M = M + 1 - h
        reduced_s = s + 1 - h
        kernel = (
            0
            if reduced_M <= 0 or reduced_s <= 0
            else rectangular_triangle_count(reduced_M - 1, L - h, reduced_s - 1)
        )
        answer += block_input - kernel
    return answer


def signed_nullity(agreement: int, m: int, L: int, s: int) -> int:
    return coefficient_count(m * agreement, L, s) - N * local_rank_bound(m, L, s)


def first_positive_agreement(m: int, L: int, s: int) -> tuple[int, int, int]:
    """First a>w with positive signed nullity, plus values at a and a-1."""
    rank = local_rank_bound(m, L, s)

    def value(a: int) -> int:
        return coefficient_count(m * a, L, s) - N * rank

    lo, hi = W, N
    assert value(lo) <= 0 and value(hi) > 0
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if value(mid) > 0:
            hi = mid
        else:
            lo = mid
    return hi, value(hi), value(hi - 1)


@dataclass(frozen=True)
class Profile:
    name: str
    m: int
    L: int
    s: int
    middle_cap: int
    accepted_nullity: int


PROFILES = (
    Profile("A", 113, 157_823, 34, 156, 2_415_525),
    Profile("B", 119, 38_980, 37, 164, 14_080_615),
    Profile("T", 223, 8_870, 69, 308, 1_575_567_595),
    Profile("Source00", 64_000, 3_840_000, 19_840, 88_523, 112_368_330_339_950_765_247_528),
    Profile("Source01", 32_000, 3_200_000, 9_888, 44_261, 13_986_869_220_384_145_651_984),
    Profile("Source02", 32_000, 2_880_000, 9_888, 44_261, 12_234_685_572_049_001_011_984),
    Profile("Source03", 16_000, 1_062_000, 4_940, 22_130, 502_972_248_297_244_942_575),
    Profile("Source04", 8_000, 531_000, 2_470, 11_065, 31_126_202_584_300_507_075),
    Profile("Source05", 1_000, 88_902, 308, 1_383, 9_873_296_301_718_971),
    Profile("Source06", 14_000, 3_640_000, 4_267, 19_364, 1_507_744_192_739_885_167_111),
)


def seedless_input_count(M: int, L: int, s: int) -> int:
    """`RCN285.seedlessInputCount`, in O(1)."""
    if M < 0 or L < 0 or s < 0:
        return 0
    M = min(M, L)
    flat = min(M + 1, max(0, L - s + 1))
    answer = flat * (s + 1)
    if flat <= M:
        count = M - flat + 1
        answer += count * (L + 1) - (flat + M) * count // 2
    return answer


def seedless_local_rank_bound(m: int, L: int, s: int) -> int:
    """Seedless `RCN279.localRankBound`, evaluated in O(m)."""
    answer = 0
    for r in range(m):
        M = min(r, L)
        h = m - r
        block_input = seedless_input_count(M, L, s)
        kernel = (
            seedless_input_count(M - h, L - h, s - h)
            if h <= M and h <= L and h <= s
            else 0
        )
        answer += block_input - kernel
    return answer


def seedless_coefficient_count(D: int, L: int, s: int) -> int:
    """Seedless `RCN279.coefficientCount`, evaluated in O(s)."""
    answer = 0
    for j in range(min(s, L) + 1):
        weight = D - (W - 1) * j
        if weight <= 0:
            break
        top = min(L - j, (weight - 1) // W)
        count = top + 1
        answer += count * weight - W * sum1(top)
    return answer


def seedless_signed_nullity(agreement: int, m: int, L: int, s: int) -> int:
    return seedless_coefficient_count(m * agreement, L, s) - N * seedless_local_rank_bound(m, L, s)


def scalar_list_budget(agreement: int, y_cap: int = 156, slope_cap: int = 34) -> int:
    gap = agreement - W
    cap_y = 1 + 2 * W * y_cap
    cap_r = W * (2 * slope_cap - 1)
    regular = (N - W) * (cap_y * slope_cap + cap_r * y_cap)
    singular = (2 * slope_cap - 1) * y_cap
    numerator = regular + singular * gap
    return numerator // gap + 1


def flat_seedless_rank(m: int, s: int) -> int:
    """Closed rank formula when L >= m-1+s (the accepted support regime)."""
    k = min(s, m // 2)
    block_sum = (s + 1) * m * (m + 1) // 2
    kernel_sum = (
        k * (m + 1) * (s + 1)
        - (m + 2 * s + 3) * k * (k + 1) // 2
        + k * (k + 1) * (2 * k + 1) // 3
    )
    return block_sum - kernel_sum


def bounded_seedless_search(max_m: int = 5_000) -> tuple[int, tuple[int, int, int], int]:
    """Exhaust the minimal-shape, nontruncated seedless family through max_m.

    For each m, all s with L=ceil((m*A+s)/W)-1 and L>=m-1+s are
    checked.  This includes 4,714,130 profiles when max_m=5000.
    """
    best = -(1 << 200)
    argbest = (0, 0, 0)
    checked = 0
    for m in range(1, max_m + 1):
        D = m * TARGET_AGREEMENT
        coefficients = 0
        # The flat regime ends near (A/W-1)m.  The loose upper bound avoids
        # any floating-point decision at the actual boundary.
        max_s = min(W - 1, (D + W - 1) // W - m + 2)
        for s in range(max_s + 1):
            weight = D - (W - 1) * s
            if weight <= 0:
                break
            top = (weight - 1) // W
            coefficients += (top + 1) * weight - W * sum1(top)
            L = (D + s + W - 1) // W - 1
            if L < m - 1 + s:
                continue
            value = coefficients - N * flat_seedless_rank(m, s)
            checked += 1
            if value > best:
                best, argbest = value, (m, L, s)
    return best, argbest, checked


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--search", action="store_true", help="run the 4.7M-profile bounded search")
    args = parser.parse_args()

    print(f"target: agreement={TARGET_AGREEMENT}, errors={TARGET_ERRORS}, gap={TARGET_AGREEMENT-W}")
    print("fixed Higher*6810 profiles:")
    for p in PROFILES:
        accepted = signed_nullity(ACCEPTED_AGREEMENT, p.m, p.L, p.s)
        assert accepted == p.accepted_nullity, (p.name, accepted, p.accepted_nullity)
        target = signed_nullity(TARGET_AGREEMENT, p.m, p.L, p.s)
        threshold, at_threshold, below_threshold = first_positive_agreement(p.m, p.L, p.s)
        max_shape_m = (W * (p.middle_cap + 1) - p.s) // TARGET_AGREEMENT
        shape_max_value = signed_nullity(TARGET_AGREEMENT, max_shape_m, p.L, p.s)
        print(
            f"  {p.name:8s} target_signed={target:>27d} "
            f"first_positive={threshold} values=({below_threshold},{at_threshold}) "
            f"shape_max_m={max_shape_m} shape_max_signed={shape_max_value}"
        )
        assert target <= 0

    scalar_accepted = seedless_signed_nullity(ACCEPTED_AGREEMENT, 113, 156, 34)
    scalar_target = seedless_signed_nullity(TARGET_AGREEMENT, 113, 156, 34)
    assert scalar_accepted == 3_464_475
    assert scalar_target == -482_231_575
    scalar_threshold = None
    for agreement in range(TARGET_AGREEMENT, ACCEPTED_AGREEMENT + 1):
        if seedless_signed_nullity(agreement, 113, 156, 34) > 0:
            scalar_threshold = agreement
            break
    assert scalar_threshold == 181_288
    print(
        "scalar   "
        f"target_signed={scalar_target:>27d} first_positive={scalar_threshold} "
        f"accepted_signed={scalar_accepted}"
    )

    accepted_list = scalar_list_budget(ACCEPTED_AGREEMENT)
    target_list = scalar_list_budget(TARGET_AGREEMENT)
    assert accepted_list == 7_204_041_463
    field_capacity = FIELD_ORDER**6 // 2**128
    accepted_ledger_bound = 274_736_416_276_891_560
    accepted_mca = field_capacity - accepted_list
    target_mca = field_capacity - target_list
    print("MCA/list ledger (secondary, since interpolation already fails):")
    print(f"  field_capacity={field_capacity}")
    print(f"  accepted_list={accepted_list} accepted_mca={accepted_mca}")
    print(f"  target_list={target_list} target_mca={target_mca}")
    print(f"  target_budget_minus_accepted_ledger={target_mca-accepted_ledger_bound}")

    if args.search:
        best, profile, checked = bounded_seedless_search()
        print("bounded alternative seedless search:")
        print(f"  checked={checked} best_signed={best} at m,L,s={profile}")
        assert checked == 4_714_130
        assert (best, profile) == (-32_389, (1, 1, 0))


if __name__ == "__main__":
    main()
