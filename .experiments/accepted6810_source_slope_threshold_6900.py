#!/usr/bin/env python3
"""Exact RED/GO gate for retargeting the accepted 6810 source to 6900.

This uses integer arithmetic only.  In the nontruncated L chamber it computes
the coefficient of L in the accepted RCN119 coefficient and contact-rank
counts.  It also checks the asymptotic obstruction and the existing Full187
curvature-source receipt.
"""

from fractions import Fraction

W = 131_071
N = 262_144
ACCEPTED_AGREEMENT = 181_294
TARGET_AGREEMENT = 180_413


def triangular_weight_slope(D: int, j: int) -> int:
    """Sum_i max(D-W*i-(W-1)*j,0), i >= 0."""
    top = D - (W - 1) * j
    if top <= 0:
        return 0
    q = (top - 1) // W
    return (q + 1) * top - W * q * (q + 1) // 2


def coefficient_slope(m: int, s: int, agreement: int) -> int:
    D = m * agreement
    return sum(triangular_weight_slope(D, j) for j in range(s + 1))


def rank_slope(m: int, s: int) -> int:
    """Exact L-slope of RCN119.localRankBound when L+1 >= m+s.

    This formula remains valid for every 0 <= s < m, not only the closed-rank
    theorem's 2*s <= m chamber.  The late rows are indexed by
    k=m-r=1,...,min(s,floor(m/2)).
    """
    t = min(s, m // 2)
    sum_k = t * (t + 1) // 2
    sum_k2 = t * (t + 1) * (2 * t + 1) // 6
    source = (s + 1) * m * (m + 1) // 2
    removed = (
        (s + 1) * (m + 1) * t
        - (2 * (s + 1) + (m + 1)) * sum_k
        + 2 * sum_k2
    )
    return source - removed


def nullity_slope(m: int, s: int, agreement: int) -> int:
    return coefficient_slope(m, s, agreement) - N * rank_slope(m, s)


def coefficient_count(m: int, s: int, total_cap: int, agreement: int) -> int:
    """Closed inner-i evaluation of the literal RCN119 coefficientCount."""
    D = m * agreement
    answer = 0
    for j in range(s + 1):
        top = D - (W - 1) * j
        if top <= 0 or total_cap < j:
            continue
        q = min(total_cap - j, (top - 1) // W)
        sum_value = (q + 1) * top - W * q * (q + 1) // 2
        sum_i_value = (
            top * q * (q + 1) // 2
            - W * q * (q + 1) * (2 * q + 1) // 6
        )
        answer += (total_cap + 1 - j) * sum_value - sum_i_value
    return answer


def _triangle(n: int) -> int:
    return n * (n - 1) // 2


def _rectangle(a: int, b: int, base: int) -> int:
    """Sum_{i<a,j<b} (base-i-j), in every call below nonnegative."""
    return a * b * base - b * _triangle(a) - a * _triangle(b)


def local_rank_count(m: int, s: int, total_cap: int) -> int:
    """Literal RCN119 localRankBound, with each rectangular sum closed."""
    answer = 0
    for r in range(m):
        M = min(r, total_cap)
        h = min(r + 1, m - r)
        source = _rectangle(M + 1, s + 1, total_cap + 1)
        a = max(M + 1 - h, 0)
        b = max(s + 1 - h, 0)
        removed = _rectangle(a, b, total_cap + 1 - h) if a and b else 0
        answer += source - removed
    return answer


def signed_excess(m: int, s: int, total_cap: int, agreement: int) -> int:
    return coefficient_count(m, s, total_cap, agreement) - N * local_rank_count(m, s, total_cap)


# These are exactly the profiles in accepted commit 09d8a2a,
# ProximityPrize/SubmissionLower/HigherKernels80850.lean.
PROFILES = (
    ("A", 113, 34, 157_823),
    ("B", 119, 37, 38_980),
    ("T", 223, 69, 8_870),
    ("Source00", 64_000, 19_840, 3_840_000),
    ("Source01", 32_000, 9_888, 3_200_000),
    ("Source02", 32_000, 9_888, 2_880_000),
    ("Source03", 16_000, 4_940, 1_062_000),
    ("Source04", 8_000, 2_470, 531_000),
    ("Source05", 1_000, 308, 88_902),
    ("Source06", 14_000, 4_267, 3_640_000),
)

EXPECTED_ACCEPTED = {
    "A": 3_464_475,
    "B": 17_439_226,
    "T": 942_296_810,
    "Source00": 44_009_595_957_267_554,
    "Source01": 5_475_573_901_047_327,
    "Source02": 5_475_573_901_047_327,
    "Source03": 681_584_000_624_865,
    "Source04": 84_615_720_487_095,
    "Source05": 148_947_874_404,
    "Source06": 449_603_508_027_916,
}

EXPECTED_TARGET = {
    "A": -482_231_575,
    "B": -565_193_304,
    "T": -2_822_631_875,
    "Source00": -43_684_927_597_335_735,
    "Source01": -5_455_965_401_118_023,
    "Source02": -5_455_965_401_118_023,
    "Source03": -684_047_863_829_196,
    "Source04": -86_127_167_413_056,
    "Source05": -184_888_376_958,
    "Source06": -455_009_375_948_556,
}

EXPECTED_ACCEPTED_EXCESS = {
    "A": 2_415_525,
    "B": 14_080_615,
    "T": 1_575_567_595,
    "Source00": 112_368_330_339_950_765_247_528,
    "Source01": 13_986_869_220_384_145_651_984,
    "Source02": 12_234_685_572_049_001_011_984,
    "Source03": 502_972_248_297_244_942_575,
    "Source04": 31_126_202_584_300_507_075,
    "Source05": 9_873_296_301_718_971,
    "Source06": 1_507_744_192_739_885_167_111,
}

EXPECTED_TARGET_EXCESS = {
    "A": -76_612_802_872_130,
    "B": -22_658_732_083_671,
    "T": -32_756_551_753_835,
    "Source00": -220_090_056_863_886_727_062_784,
    "Source01": -20_726_846_964_163_996_398_886,
    "Source02": -18_980_938_035_806_229_038_886,
    "Source03": -930_640_210_049_624_524_047,
    "Source04": -58_495_105_198_091_600_080,
    "Source05": -19_550_893_759_173_647,
    "Source06": -1_775_385_389_804_909_385_811,
}


def scan_box(agreement: int, max_m: int = 1_200) -> tuple[tuple[int, int, int], int]:
    """Exhaust all 1 <= s < m <= max_m, incrementing the j-sum."""
    best = None
    positive = 0
    for m in range(1, max_m + 1):
        D = m * agreement
        columns = 0
        for s in range(m):
            columns += triangular_weight_slope(D, s)
            if s == 0:
                continue
            delta = columns - N * rank_slope(m, s)
            if best is None or delta > best[0]:
                best = (delta, m, s)
            positive += delta > 0
    assert best is not None
    return best, positive


def low_chamber_max(agreement: int) -> tuple[Fraction, Fraction]:
    """Vertex and max of the beta <= 1/2 leading slope factor.

    Up to the positive factor beta*m^3/6, the factor is
      (W-2N)b^2 + 3(N-A)b + 3(A^2/W-N).
    """
    qa = W - 2 * N
    qb = 3 * (N - agreement)
    qc = 3 * (Fraction(agreement * agreement, W) - N)
    beta = Fraction(-qb, 2 * qa)
    value = qa * beta * beta + qb * beta + qc
    return beta, value


def high_chamber_value(agreement: int, beta: Fraction) -> Fraction:
    """Leading m^3 slope for 1/2 <= beta < 1."""
    alpha = Fraction(agreement, W)
    columns = Fraction(W, 6) * (alpha**3 - (alpha - beta) ** 3)
    rank = N * (beta / 4 + Fraction(1, 24))
    return columns - rank


def main() -> None:
    print("accepted RCN119 profiles: exact nontruncated L-slopes")
    for name, m, s, L in PROFILES:
        max_active_total_degree = max(
            j + max(-1, (m * ACCEPTED_AGREEMENT - (W - 1) * j - 1) // W)
            for j in range(s + 1)
        )
        assert L >= max_active_total_degree
        assert L + 1 >= m + s
        accepted = nullity_slope(m, s, ACCEPTED_AGREEMENT)
        target = nullity_slope(m, s, TARGET_AGREEMENT)
        accepted_excess = signed_excess(m, s, L, ACCEPTED_AGREEMENT)
        target_excess = signed_excess(m, s, L, TARGET_AGREEMENT)
        assert accepted == EXPECTED_ACCEPTED[name]
        assert target == EXPECTED_TARGET[name]
        assert accepted_excess == EXPECTED_ACCEPTED_EXCESS[name]
        assert target_excess == EXPECTED_TARGET_EXCESS[name]
        assert accepted > 0 and target < 0
        assert accepted_excess > 0 and target_excess < 0
        print(
            f"{name:8s} slope: {accepted:>24d} -> {target:>25d}; "
            f"signed excess: {accepted_excess:>25d} -> {target_excess:>26d}"
        )

    target_scan = scan_box(TARGET_AGREEMENT)
    before_scan = scan_box(180_893)
    transition_scan = scan_box(180_894)
    assert target_scan == ((-293_014, 2, 1), 0)
    assert before_scan == ((-288_214, 2, 1), 0)
    assert transition_scan == ((561_573_060, 1_200, 371), 160)
    print("finite box 1<=s<m<=1200:")
    print("  A=180413", target_scan)
    print("  A=180893", before_scan)
    print("  A=180894", transition_scan)

    beta, value = low_chamber_max(TARGET_AGREEMENT)
    assert beta == Fraction(245_193, 786_434)
    assert value == Fraction(-663_688_416_451_941, 206_157_381_628)
    assert value < 0
    # Above beta=1/2 the derivative is already negative and decreases up to 1.
    half = Fraction(1, 2)
    derivative_half = Fraction((2 * TARGET_AGREEMENT - W) ** 2, 8 * W) - Fraction(N, 4)
    assert derivative_half == Fraction(-15_931_592_423, 1_048_568)
    assert derivative_half < 0
    assert high_chamber_value(TARGET_AGREEMENT, half) == Fraction(-8_991_469_861, 6_291_408)
    assert high_chamber_value(TARGET_AGREEMENT, half) < 0
    first_asymptotic_positive = next(
        agreement
        for agreement in range(TARGET_AGREEMENT, ACCEPTED_AGREEMENT + 1)
        if low_chamber_max(agreement)[1] > 0
    )
    assert first_asymptotic_positive == 180_852
    print("asymptotic:")
    print(f"  low beta vertex={beta}; maximum={value} (<0)")
    print(f"  high beta H(1/2)={high_chamber_value(TARGET_AGREEMENT, half)}; H'(1/2)={derivative_half}")
    print(f"  first agreement with positive low-chamber asymptotic maximum={first_asymptotic_positive}")

    # Existing Full187 source: (m,M,slopeCap,curvatureCap,seedCap)
    # = (60,82,21,10,2703), D=60*180413.
    full187_columns = 162_963_415_163_901
    full187_one_node_rank = 621_656_057
    full187_margin = full187_columns - N * full187_one_node_rank
    assert full187_margin == 9_757_693 > 0
    print("Full187 curvature/passive source:")
    print(f"  columns={full187_columns}; global rank={N*full187_one_node_rank}; margin={full187_margin}")

    print("RED: no accepted fixed-P4 profile can be retargeted by enlarging L.")
    print("GO(source only): existing Full187 restores positive target nullity.")
    print("RED(adapter): no proved Full187 -> accepted Higher strict-phase adapter exists.")


if __name__ == "__main__":
    main()
