#!/usr/bin/env python3
"""Exact low-memory audit of truncated RCN279/RCN285 scalar supports.

The accepted seedless scalar interpolation source has parameters ``m,L,s``.
The earlier bounded search covered the chamber ``L >= m - 1 + s``, where the
local support is rectangular at every Taylor block.  This script covers the
complementary chamber ``L < m - 1 + s``.  It uses exact integer closed forms
for the literal definitions

* ``RCN279.coefficientCount (m*A) W L s``; and
* ``RCN285.localRankBound m L s``.

For fixed ``m,s``, the global coefficient count is already saturated once
``m*A+s <= W*(L+1)``.  Increasing ``L`` thereafter can only enlarge each local
input space and its rank upper bound, so the first saturated value
``L=floor((m*A+s-1)/W)`` is the only potentially best value.  The search below
checks every such truncated profile through an explicit ``m`` bound.

This is a finite search receipt, not a theorem about unbounded multiplicity.
Every arithmetic operation is a Python integer and memory use is O(1).
"""

from __future__ import annotations

import argparse
import resource
import time


N = 262_144
W = 131_071
A = 180_413
GAP = A - W
FIELD_ORDER = 2_130_706_433
PROTOCOL_CAPACITY = FIELD_ORDER**6 // 2**128


def sum1(k: int) -> int:
    """1+...+k, with k >= 0."""
    return k * (k + 1) // 2


def sum2(k: int) -> int:
    """1^2+...+k^2, with k >= 0."""
    return k * (k + 1) * (2 * k + 1) // 6


def input_count(M: int, L: int, s: int) -> int:
    """Literal ``RCN285.seedlessInputCount``, in O(1)."""
    M = min(M, L)
    if M < 0 or L < 0 or s < 0:
        return 0
    flat = min(M + 1, max(0, L - s + 1))
    answer = flat * (s + 1)
    if flat <= M:
        count = M - flat + 1
        answer += count * (L + 1) - (flat + M) * count // 2
    return answer


def local_rank_slow(m: int, L: int, s: int) -> int:
    """Direct O(m) transcription, retained as a test oracle."""
    answer = 0
    for r in range(m):
        M = min(r, L)
        h = m - r
        base = input_count(M, L, s)
        kernel = input_count(M - h, L - h, s - h) if h <= M and h <= L and h <= s else 0
        answer += base - kernel
    return answer


def _range_sums(lo: int, hi: int) -> tuple[int, int, int]:
    if lo > hi:
        return 0, 0, 0
    return (
        hi - lo + 1,
        sum1(hi) - sum1(lo - 1),
        sum2(hi) - sum2(lo - 1),
    )


def local_rank_general(m: int, L: int, s: int) -> int:
    """O(1) closed form for all relevant ``0 <= s <= L`` shapes."""
    assert m >= 1 and 0 <= s <= L
    q = L - s
    R = min(m - 1, L)
    if R <= q:
        base = (s + 1) * (R + 1) * (R + 2) // 2
    else:
        K = R - q
        base = (s + 1) * (q + 1) * (q + 2) // 2
        base += K * (q + 1) * (s + 1)
        base += ((2 * s + 1) * sum1(K) - sum2(K)) // 2
    if L < m - 1:
        base += (m - 1 - L) * input_count(L, L, s)

    H = min(m // 2, L, s)
    kernel = 0

    # Here m-2h > L-h, so the cap L-h supplies M and the whole triangular
    # seedless support is counted.
    cap_hi = min(H, m - L - 1)
    count, sh, sh2 = _range_sums(1, cap_hi)
    if count:
        twice = 2 * (q + 1) * (count * (s + 1) - sh)
        twice += count * s * (s + 1) - (2 * s + 1) * sh + sh2
        assert twice % 2 == 0
        kernel += twice // 2

    # Here M=m-2h comes from Taylor order and still lies above q.
    tail_lo = max(1, m - L)
    tail_hi = min(H, (m - q - 1) // 2)
    count, sh, _ = _range_sums(tail_lo, tail_hi)
    if count:
        c = m - q
        factor = 2 * s - c + 1
        twice = 2 * (q + 1) * (count * (s + 1) - sh)
        twice += factor * (count * c - 2 * sh)
        assert twice % 2 == 0
        kernel += twice // 2

    # Remaining h have M=m-2h <= q.
    rectangle_lo = max(1, m - L, tail_hi + 1)
    count, sh, sh2 = _range_sums(rectangle_lo, H)
    if count:
        kernel += count * (m + 1) * (s + 1)
        kernel -= (m + 2 * s + 3) * sh
        kernel += 2 * sh2
    return base - kernel


def local_rank_fast(m: int, L: int, s: int) -> int:
    """Closed form for the exact rank bound in the saturated search chamber.

    Saturation gives L >= m for all searched m.  Put q=L-s.  The input count
    changes formula only when r crosses q.  In the kernel sum h=m-r, q remains
    invariant after replacing (M,L,s) by (M-h,L-h,s-h), making its first piece
    linear and its second piece quadratic in h.
    """
    assert m >= 1 and 0 <= s <= L and L >= m
    q = L - s
    rmax = m - 1

    # Sum_{r=0}^{m-1} input_count(r,L,s).
    if rmax <= q:
        base = (s + 1) * m * (m + 1) // 2
    else:
        K = rmax - q
        base = (s + 1) * (q + 1) * (q + 2) // 2
        base += K * (q + 1) * (s + 1)
        base += ((2 * s + 1) * sum1(K) - sum2(K)) // 2

    H = min(s, m // 2)
    if H == 0:
        return base

    # For h <= HA, M=m-2h is above q.  The tail width c-2h and its
    # complementary factor 2s-c+1 make this summand linear in h.
    c = m - q
    HA = min(H, max(0, (c - 1) // 2))
    kernel = 0
    if HA:
        factor = 2 * s - c + 1
        kernel += HA * ((q + 1) * (s + 1) + c * factor // 2)
        kernel -= sum1(HA) * ((q + 1) + factor)

    # Remaining h have M <= q and input=(m-2h+1)*(s-h+1).
    lo = HA + 1
    if lo <= H:
        count = H - lo + 1
        sh = sum1(H) - sum1(lo - 1)
        sh2 = sum2(H) - sum2(lo - 1)
        kernel += count * (m + 1) * (s + 1)
        kernel -= (m + 2 * s + 3) * sh
        kernel += 2 * sh2
    return base - kernel


def coefficient_term(D: int, j: int) -> int:
    """Contribution of one slope exponent after the total cap is saturated."""
    weight = D - (W - 1) * j
    if weight <= 0:
        return 0
    top = (weight - 1) // W
    return (top + 1) * weight - W * top * (top + 1) // 2


def coefficient_count_slow(D: int, L: int, s: int) -> int:
    answer = 0
    for j in range(min(s, L) + 1):
        weight = D - (W - 1) * j
        if weight <= 0:
            break
        top = min(L - j, (weight - 1) // W)
        if top >= 0:
            answer += (top + 1) * weight - W * top * (top + 1) // 2
    return answer


def coefficient_count_general(D: int, L: int, s: int) -> int:
    """Exact O(1+s/W) coefficient count, including clipped total caps."""
    assert D >= 1 and 0 <= s <= L
    Q, R = divmod(D - 1, W)
    answer = 0
    lo = 0
    stop = min(s, L, (D - 1) // (W - 1))
    while lo <= stop:
        b = (R + lo) // W
        hi = min(stop, (b + 1) * W - R - 1)
        count = hi - lo + 1
        sj = sum1(hi) - sum1(lo - 1)
        sj2 = sum2(hi) - sum2(lo - 1)
        a = min(L, Q + b)
        # top exponent is a-j throughout this residue interval.
        assert a >= hi
        weighted_sum = count * (a + 1) * D
        weighted_sum -= ((a + 1) * (W - 1) + D) * sj
        weighted_sum += (W - 1) * sj2
        triangle_sum = count * (a * a + a) - (2 * a + 1) * sj + sj2
        assert triangle_sum % 2 == 0
        answer += weighted_sum - W * (triangle_sum // 2)
        lo = hi + 1
    return answer


def coefficient_count_saturated(D: int, s: int) -> int:
    """Sum all slope slices in O(1+s/W) rather than O(s).

    If ``D+s <= W*(L+1)``, the total-degree cap does not clip any slice.
    Write ``D-1=Q*W+R``.  On a maximal interval where
    ``b=floor((R+j)/W)`` is fixed, the top y exponent is ``Q-j+b`` and
    the slice count is a quadratic polynomial in j.
    """
    Q, R = divmod(D - 1, W)
    answer = 0
    lo = 0
    while lo <= s:
        b = (R + lo) // W
        hi = min(s, (b + 1) * W - R - 1)
        count = hi - lo + 1
        sj = sum1(hi) - sum1(lo - 1)
        sj2 = sum2(hi) - sum2(lo - 1)
        a = Q + b
        weighted_sum = count * (a + 1) * D
        weighted_sum -= ((a + 1) * (W - 1) + D) * sj
        weighted_sum += (W - 1) * sj2
        triangle_sum = count * (a * a + a) - (2 * a + 1) * sj + sj2
        assert triangle_sum % 2 == 0
        answer += weighted_sum - W * (triangle_sum // 2)
        lo = hi + 1
    return answer


def list_budget(L: int, s: int) -> int:
    """The standard RCN281 scalar consumer bound for caps L,s."""
    cap_y = 1 + 2 * W * L
    cap_r = W * (2 * s - 1)
    regular = (N - W) * (cap_y * s + cap_r * L)
    singular = (2 * s - 1) * L
    return (regular + singular * GAP) // GAP + 1


def self_test() -> None:
    # Literal accepted-6811 profile at its accepted agreement.
    old_D = 115 * 181_284
    assert coefficient_count_slow(old_D, 159, 35) == 47_864_396_310
    assert local_rank_fast(115, 159, 35) == local_rank_slow(115, 159, 35) == 182_580

    # Exhaustively cross-check the closed form on small saturated shapes,
    # including both sides of the truncation wall.
    for m in range(1, 40):
        D = m * A
        smax = (D - 1) // (W - 1)
        for s in range(smax + 1):
            L = (D + s - 1) // W
            assert L >= m and s <= L
            assert local_rank_fast(m, L, s) == local_rank_slow(m, L, s), (m, L, s)
            saturated = sum(coefficient_term(D, j) for j in range(s + 1))
            assert saturated == coefficient_count_slow(D, L, s), (m, L, s)
            assert saturated == coefficient_count_saturated(D, s), (m, L, s)

    # General clipped-support formulas, including L<m.
    for m in range(1, 25):
        D = m * A
        for L in range(30):
            for s in range(L + 1):
                assert local_rank_general(m, L, s) == local_rank_slow(m, L, s), (m, L, s)
                assert coefficient_count_general(D, L, s) == coefficient_count_slow(D, L, s), (m, L, s)

    assert PROTOCOL_CAPACITY == 274_980_728_111_395_087


def first_truncated_profile(m: int) -> tuple[int, int]:
    """Least ``(L,s)`` satisfying saturation and ``L < m-1+s``.

    Combining the two inequalities gives

        (W-1)*s >= m*(A-W)+W.

    At the least such s, L=m+s-2 (equivalently q=L-s=m-2).
    """
    s = (m * (A - W) + W + (W - 2)) // (W - 1)
    L = m + s - 2
    assert m * A + s <= W * (L + 1)
    assert L < m - 1 + s
    if s:
        previous_s = s - 1
        previous_L = (m * A + previous_s - 1) // W
        assert previous_L >= m - 1 + previous_s
    return L, s


def last_viable_multiplicity() -> tuple[int, int]:
    """Last m whose *least* truncated scalar list budget fits capacity."""
    lo, hi = 2, 1
    while hi <= lo or list_budget(*first_truncated_profile(hi)) < PROTOCOL_CAPACITY:
        hi *= 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if list_budget(*first_truncated_profile(mid)) < PROTOCOL_CAPACITY:
            lo = mid
        else:
            hi = mid
    return lo, hi


def search_all_viable_frontiers() -> dict[str, int]:
    """Check the first truncated profile at every viable multiplicity.

    The note accompanying this script proves that, at fixed m, every later
    truncated slope slice strictly decreases signed nullity.  Consequently
    these frontier checks cover all profiles whose scalar budget can fit the
    protocol capacity, without an infeasible quadratic enumeration.
    """
    last_viable, first_unviable = last_viable_multiplicity()
    assert (last_viable, first_unviable) == (617_277, 617_278)
    best: tuple[int, int, int, int] | None = None
    last: tuple[int, int, int, int] | None = None
    for m in range(2, last_viable + 1):
        L, s = first_truncated_profile(m)
        coefficients = coefficient_count_saturated(m * A, s)
        delta = coefficients - N * local_rank_fast(m, L, s)
        row = (delta, m, L, s)
        if best is None or row > best:
            best = row
        last = row
    assert best is not None and last is not None
    lv_L, lv_s = first_truncated_profile(last_viable)
    uv_L, uv_s = first_truncated_profile(first_unviable)
    return {
        "protocol_capacity": PROTOCOL_CAPACITY,
        "checked_viable_frontiers": last_viable - 1,
        "last_viable_m": last_viable,
        "last_viable_L": lv_L,
        "last_viable_s": lv_s,
        "last_viable_budget": list_budget(lv_L, lv_s),
        "last_viable_delta": last[0],
        "first_unviable_m": first_unviable,
        "first_unviable_L": uv_L,
        "first_unviable_s": uv_s,
        "first_unviable_budget": list_budget(uv_L, uv_s),
        "best_frontier_delta": best[0],
        "best_frontier_m": best[1],
        "best_frontier_L": best[2],
        "best_frontier_s": best[3],
    }


def search(max_m: int) -> dict[str, int | None]:
    checked = positive = 0
    best_delta: int | None = None
    best_profile: tuple[int, int, int] | None = None
    best_budget: int | None = None
    best_budget_profile: tuple[int, int, int] | None = None
    closest_by_m: tuple[int, int, int, int] | None = None

    for m in range(1, max_m + 1):
        D = m * A
        smax = (D - 1) // (W - 1)
        coefficients = 0
        for s in range(smax + 1):
            coefficients += coefficient_term(D, s)
            L = (D + s - 1) // W
            # The complementary chamber was already searched elsewhere.
            if L >= m - 1 + s:
                continue
            checked += 1
            rank = local_rank_fast(m, L, s)
            delta = coefficients - N * rank
            if best_delta is None or delta > best_delta:
                best_delta = delta
                best_profile = (m, L, s)
            if closest_by_m is None or delta * closest_by_m[0] > closest_by_m[3] * m:
                closest_by_m = (m, L, s, delta)
            if delta > 0:
                positive += 1
                budget = list_budget(L, s)
                if best_budget is None or budget < best_budget:
                    best_budget = budget
                    best_budget_profile = (m, L, s)

    assert best_profile is not None and closest_by_m is not None
    return {
        "max_m": max_m,
        "checked_truncated_profiles": checked,
        "positive_profiles": positive,
        "best_delta": best_delta,
        "best_m": best_profile[0],
        "best_L": best_profile[1],
        "best_s": best_profile[2],
        "least_positive_list_budget": best_budget,
        "least_budget_m": None if best_budget_profile is None else best_budget_profile[0],
        "least_budget_L": None if best_budget_profile is None else best_budget_profile[1],
        "least_budget_s": None if best_budget_profile is None else best_budget_profile[2],
        "best_delta_per_m_numerator": closest_by_m[3],
        "best_delta_per_m_denominator": closest_by_m[0],
        "best_delta_per_m_L": closest_by_m[1],
        "best_delta_per_m_s": closest_by_m[2],
    }


def search_general_clipped(max_m: int) -> dict[str, int | None]:
    """Exhaust all clipped boxes ``L-s <= m-2`` through ``max_m``.

    Write q=L-s.  Values s beyond the last positive weighted slice add no
    columns, so they cannot improve the dimension gate and are omitted.
    Unlike ``search``, this includes unsaturated total caps L<L_min.
    """
    checked = positive = 0
    best: tuple[int, int, int, int] | None = None
    for m in range(2, max_m + 1):
        D = m * A
        smax = (D - 1) // (W - 1)
        for q in range(m - 1):
            for s in range(smax + 1):
                L = q + s
                checked += 1
                delta = coefficient_count_general(D, L, s) - N * local_rank_general(m, L, s)
                row = (delta, m, L, s)
                if best is None or row > best:
                    best = row
                positive += delta > 0
    if best is None:
        return {
            "general_max_m": max_m,
            "general_checked_profiles": 0,
            "general_positive_profiles": 0,
            "general_best_delta": None,
            "general_best_m": None,
            "general_best_L": None,
            "general_best_s": None,
        }
    return {
        "general_max_m": max_m,
        "general_checked_profiles": checked,
        "general_positive_profiles": positive,
        "general_best_delta": best[0],
        "general_best_m": best[1],
        "general_best_L": best[2],
        "general_best_s": best[3],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-m", type=int, default=5_000)
    parser.add_argument(
        "--general-max-m",
        type=int,
        default=0,
        help="also exhaust every unsaturated/clipped truncated box through this m",
    )
    args = parser.parse_args()
    assert 1 <= args.max_m
    # Hard cap protects the shared verifier-research host from accidental
    # unbounded runs.  The algorithm normally stays below 20 MiB.
    resource.setrlimit(resource.RLIMIT_AS, (512 * 1024**2, 512 * 1024**2))
    resource.setrlimit(resource.RLIMIT_CPU, (600, 600))
    self_test()
    started = time.monotonic()
    receipt = search(args.max_m)
    receipt.update(search_all_viable_frontiers())
    if args.general_max_m:
        receipt.update(search_general_clipped(args.general_max_m))
    receipt["elapsed_milliseconds"] = round((time.monotonic() - started) * 1000)
    receipt["maximum_rss_kib"] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    print(receipt)


if __name__ == "__main__":
    main()
