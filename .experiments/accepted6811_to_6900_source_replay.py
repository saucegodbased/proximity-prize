#!/usr/bin/env python3
"""Exact low-memory replay of accepted-6811 source shapes at score 6900.

This mirrors the Nat formulas in LowerGeometry/LowerFoundation.  Every
published 6811 coefficient count/rank is asserted before its 6900 value is
used, so a transcription error makes the replay fail rather than silently
producing a plausible table.
"""

from math import comb

N = 262_144
W = 131_071
A6811 = 181_284
A6900 = 180_413


def nsub(a: int, b: int) -> int:
    return max(0, a - b)


def choose(n: int, k: int) -> int:
    return comb(n, k) if n >= k else 0


def one_residue_coefficient_count(D: int, L: int, s: int) -> int:
    """RCN100.coefficientCount, via oneResidueCoefficientCount."""
    q, r = divmod(D, W)
    assert s <= q <= L and r + s <= W
    U = nsub(L + 1, q)
    c1 = U * (r + q)
    c2 = U * (W - 2) + r + q + (W - 1)
    c3 = 2 * (W - 2) + 1
    return (
        c1 * (choose(q + 2, 2) - choose(nsub(q + 1, s), 2))
        + c2 * (choose(q + 2, 3) - choose(nsub(q + 1, s), 3))
        + c3 * (choose(q + 2, 4) - choose(nsub(q + 1, s), 4))
    )


def coefficient_count(D: int, L: int, s: int) -> int:
    """Exact RCN100.coefficientCount, one closed arithmetic row per slope.

    Unlike ``one_residue_coefficient_count``, this remains valid when the
    target residue crosses a row boundary.  That happens for phase source 00:
    ``(64000 * 180413) % 131071 + 19840 > 131071``.
    """
    total = 0
    for j in range(s + 1):
        t = nsub(D, (W - 1) * j)
        if t == 0 or j > L:
            continue
        last_i = min(L - j, (t - 1) // W)
        rows = last_i + 1
        sum_i = rows * (rows - 1) // 2
        sum_i_sq = rows * (rows - 1) * (2 * rows - 1) // 6
        total += (
            rows * (L + 1 - j) * t
            - ((L + 1 - j) * W + t) * sum_i
            + W * sum_i_sq
        )
    return total


def scalar_coefficient_count(D: int, L: int, s: int) -> int:
    """Literal RCN279.coefficientCount used by MovingFiberScalar6811."""
    total = 0
    for i in range(L + 1):
        for j in range(s + 1):
            if i + j <= L:
                total += nsub(nsub(D, W * i), (W - 1) * j)
    return total


def seedless_input_count(M: int, L: int, s: int) -> int:
    return sum(min(s + 1, nsub(L + 1, i)) for i in range(M + 1))


def scalar_local_rank(m: int, L: int, s: int) -> int:
    """Literal RCN285/RCN279 seedless localRankBound."""
    total = 0
    for r in range(m):
        M = min(r, L)
        h = m - r
        source = seedless_input_count(M, L, s)
        kernel = (
            seedless_input_count(M - h, L - h, s - h)
            if h <= M and h <= L and h <= s
            else 0
        )
        total += source - kernel
    return total


def reserve(k: int, n0: int, h: int) -> int:
    return h if h < n0 else k


def relaxed_caps(p: tuple[int, ...], agreement: int) -> list[int]:
    m, B, s, _U, _L, k, n0, _old_rank, _old_count = p
    penalty = agreement - (W - 2)
    return [
        (m * agreement - reserve(k, n0, h) * penalty + B - 1) // W
        for h in range(s + 1)
    ]


def relaxed_global_count(p: tuple[int, ...], agreement: int) -> int:
    """SecondJetRelaxedGlobalCounts.coefficientCount."""
    m, B, s, U, L, k, n0, _old_rank, _old_count = p
    penalty = agreement - (W - 2)
    total = 0
    for h in range(s + 1):
        D = m * agreement - reserve(k, n0, h) * penalty
        for r in range(nsub(B, 2 * h) + 1):
            q = nsub(nsub(D, (W - 2) * h), (W - 1) * r)
            count_y = min(nsub(q, 1) // W + 1, nsub(U + 1, h + r))
            C = nsub(L + 1, h + r)
            total += (
                count_y * q * C
                + W * (count_y * (count_y - 1) * (2 * count_y - 1) // 6)
                - (q + W * C) * (count_y * (count_y - 1) // 2)
            )
    return total


def sum_descending(C: int, last: int) -> int:
    """sum_{j=0}^last (C-j)."""
    return (last + 1) * C - last * (last + 1) // 2


def relaxed_rank(p: tuple[int, ...], agreement: int) -> int:
    """Exact SecondJetRelaxedGlobalMap.rankBound for the induced caps."""
    m, B, s, U, L, _k, _n0, _old_rank, _old_count = p
    caps = relaxed_caps(p, agreement)
    source = 0
    kernel = 0
    for r in range(m):
        for h in range(s + 1):
            j_cap = nsub(B, 2 * h)
            middle_cap = min(U, caps[h])
            remainder = nsub(middle_cap, h)
            for i in range(min(r, remainder) + 1):
                last_j = min(j_cap, remainder - i)
                source += sum_descending(L + 1 - h - i, last_j)

            mr = nsub(m, r)
            q = max((mr + 1) // 2, nsub(mr, nsub(s, h)))
            a = nsub(mr, q)
            if q <= r and mr + 2 * h <= B:
                block_cap = min(U, min(caps[h : h + a + 1]))
                x_cap = nsub(r, q)
                y_cap = nsub(nsub(B, 2 * h), q)
                remainder = nsub(block_cap, h + q)
                for x in range(min(x_cap, remainder) + 1):
                    last_y = min(y_cap, remainder - x)
                    kernel += sum_descending(L + 1 - h - q - x, last_y)
    return source - kernel


def deficit(coefficients: int, rank: int) -> int:
    return N * rank - coefficients


def minimum_rank_reduction(d: int) -> int:
    # Strict nullity requires coefficients > N * rank.
    return (d + 1 + N - 1) // N


def row(label: str, coefficients: int, rank: int) -> None:
    d = deficit(coefficients, rank)
    status = "FAIL" if d >= 0 else "PASS"
    print(
        f"{label:>8} {status:>4} coeff={coefficients} rank={rank} "
        f"signed_deficit={d} min_rank_drop={minimum_rank_reduction(d) if d >= 0 else 0}"
    )


# (name, multiplicity, total cap, slope cap, accepted rank, accepted count)
principal = [
    ("A", 115, 274_277, 35, 50_068_355_280, 13_125_118_927_898_685),
    ("B", 134, 18_992, 40, 5_360_249_390, 1_405_157_241_467_798),
    ("T", 226, 9_281, 70, 12_636_646_882, 3_312_623_460_539_726),
]

# Seven sources feeding the native phase recurrence.
phase = [
    ("phase00", 64_000, 3_840_000, 19_840, 116_784_455_894_414_962_240,
     30_722_928_958_268_011_253_484_378),
    ("phase01", 32_000, 3_200_000, 9_888, 12_172_764_924_613_929_328,
     3_204_609_069_314_829_266_599_520),
    ("phase02", 32_000, 2_880_000, 9_888, 10_950_008_283_031_849_328,
     2_882_358_382_235_592_200_999_520),
    ("phase03", 16_000, 1_062_000, 4_940, 503_593_395_806_461_590,
     132_500_643_163_012_151_609_895),
    ("phase04", 8_000, 531_000, 2_470, 31_483_869_872_329_770,
     8_283_413_780_004_746_471_235),
    ("phase05", 1_000, 88_902, 308, 10_336_494_078_526,
     2_719_188_214_935_638_715),
    ("phase06", 14_000, 3_640_000, 4_267, 1_150_877_542_707_512_224,
     303_166_020_158_767_900_703_085),
]

# (m,B,s,U,L,k,n0, accepted exact rank, accepted global count)
additional = [
    (132,54,24,180,1786,5,7,7954748802,2085297060568560),
    (134,56,25,180,2819,6,8,13960022702,3659541008959570),
    (136,56,25,185,2584,6,8,13216860660,3464727181592755),
    (116,46,21,158,2772,5,7,7241280630,1898259608736359),
    (114,45,21,155,3078,5,7,7498129960,1965591832836709),
    (158,63,29,215,3013,7,10,26506952089,6948643832078647),
    (166,73,34,226,3117,8,9,38892833461,10195525571648254),
    (114,47,21,154,2781,5,7,7191547636,1885223559218890),
    (142,56,26,193,2744,6,9,15629093580,4097078687674896),
    (174,76,36,236,2736,8,9,40513371311,10620344577971942),
    (170,71,32,231,3105,8,10,39019336035,10228691439847595),
    (98,41,19,132,2387,4,6,3522727725,923462732585523),
    (142,59,27,193,2415,6,9,14852041121,3893377684989207),
    (158,69,32,214,2416,7,8,24390886813,6393939096190481),
    (146,58,27,198,2498,6,9,16001770476,4194771043943235),
    (98,41,19,133,2289,4,6,3375264212,884806673741073),
    (150,60,28,204,2288,6,9,16420856314,4304640567595772),
    (162,71,33,218,2338,7,8,26142431686,6853094634711026),
    (114,47,22,155,2711,5,7,7053684309,1849082264981388),
    (166,66,31,226,2667,7,10,28292381157,7416680657483088),
    (174,76,36,237,2716,8,9,40208136171,10540329886663022),
    (111,46,22,151,3089,5,7,7337935450,1923596440947592),
    (189,83,39,256,3112,9,10,64415619986,16886177860853516),
    (114,45,20,155,3066,5,7,7414588980,1943690857433990),
    (190,84,40,258,3048,9,10,65130073176,17073478385944741),
    (111,46,21,151,3071,5,7,7256688379,1902298102281753),
    (189,83,39,257,3084,9,10,63818941246,16729782789508276),
]


def main() -> None:
    print("scalar-list source")
    scalar_old = scalar_coefficient_count(115 * A6811, 159, 35)
    assert scalar_old == 47_864_396_310
    scalar_rank = scalar_local_rank(115, 159, 35)
    assert scalar_rank == 182_580
    row("scalar", scalar_coefficient_count(115 * A6900, 159, 35), scalar_rank)

    print("principal MCA kernels")
    for name, m, L, s, rank, accepted_count in principal:
        assert one_residue_coefficient_count(m * A6811, L, s) == accepted_count
        assert coefficient_count(m * A6811, L, s) == accepted_count
        row(name, coefficient_count(m * A6900, L, s), rank)

    print("phase kernels")
    for name, m, L, s, rank, accepted_count in phase:
        assert one_residue_coefficient_count(m * A6811, L, s) == accepted_count
        assert coefficient_count(m * A6811, L, s) == accepted_count
        row(name, coefficient_count(m * A6900, L, s), rank)

    print("27 moving-fiber interpolants")
    for i, p in enumerate(additional):
        assert relaxed_global_count(p, A6811) == p[-1]
        assert relaxed_rank(p, A6811) == p[-2]
        coefficients = relaxed_global_count(p, A6900)
        rank = relaxed_rank(p, A6900)
        row(f"P{i}", coefficients, rank)


if __name__ == "__main__":
    main()
