#!/usr/bin/env python3
"""Exact arithmetic gate for the low-seed zero-reserve P5 profile at 6900.

This is a cheap integer receipt.  It proves source-dimension and conditional
consumer arithmetic only; it does not prove the missing conormal-rank theorem.
"""

from higher6810_secondjet_retarget_exact import (
    N,
    Profile,
    TARGET_A,
    cap_slack,
    coefficient_count,
    margin,
    relaxed_rank_bound,
)


W = 131_071
ERRORS = N - TARGET_A
ALLOWANCE = 254_684_620_614_660_120


def profile(total_cap: int) -> Profile:
    return Profile(
        "k0-low-seed", 148, 64, 30, 200, total_cap, 0, 1,
        0, 0, 0, 0,
    )


def audit() -> None:
    p905 = profile(905)
    p906 = profile(906)
    p907 = profile(907)

    margin_905 = margin(TARGET_A, p905)
    margin_906 = margin(TARGET_A, p906)
    slope = margin(TARGET_A, p907) - margin_906
    assert margin_905 == -24_645_800_597
    assert margin_906 == 11_661_627_713
    assert slope == 36_307_428_310

    # The last small-cap transition ends at L=210; from L=211 onward both the
    # column count and local closed rank are affine in L.  Exhaustively checking
    # the finite transition/range makes L=906 the exact first positive integer
    # cap, not a sampled hit.
    assert margin(TARGET_A, profile(200)) == -25_621_130_838_763
    assert margin(TARGET_A, profile(210)) == -25_258_308_476_047
    assert (margin(TARGET_A, profile(211)) -
            margin(TARGET_A, profile(210))) == slope
    assert all(margin(TARGET_A, profile(total_cap)) < 0
               for total_cap in range(200, 906))
    assert margin_905 < 0 < margin_906

    columns = coefficient_count(
        TARGET_A, p906.m, p906.L, p906.B, p906.s, p906.U,
        p906.k, p906.n0,
    )
    local_rank = relaxed_rank_bound(
        p906.m, p906.L, p906.B, p906.s, p906.U,
    )
    assert columns == 1_738_293_650_805_057
    assert local_rank == 6_631_019_551
    assert N * local_rank == 1_738_281_989_177_344
    assert columns - N * local_rank == margin_906
    assert min(cap_slack(TARGET_A, p906, h)
               for h in range(p906.s + 1)) == 3

    # Conditional geometry ledger.  Four rows have boundary bidegree at most
    # (M,L)=(200,906).  The factor 4 is the sharp multihomogeneous number;
    # factor 40 is the existing coarse cofactor/generic-fibre budget.
    direct_per_stratum = 4 * 200**3 * 906
    coarse_per_stratum = 40 * 200**3 * 906
    strata = ERRORS + 1
    coarse_all_strata = strata * coarse_per_stratum
    assert direct_per_stratum == 28_992_000_000
    assert coarse_per_stratum == 289_920_000_000
    assert strata == 81_732
    assert coarse_all_strata == 23_695_741_440_000_000
    assert coarse_all_strata < ALLOWANCE
    assert ALLOWANCE - coarse_all_strata == 230_988_879_174_660_120

    print("target", (N, W, TARGET_A, ERRORS))
    print("profile", (148, 64, 30, 200, 906, 0, 1))
    print("L905_margin", margin_905)
    print("L906_columns_localRank_Nrank_margin",
          (columns, local_rank, N * local_rank, margin_906))
    print("affine_L_slope", slope)
    print("minimum_closed_cap_slack", 3)
    print("direct_and_coarse_per_stratum",
          (direct_per_stratum, coarse_per_stratum))
    print("coarse_all_exact_g_strata", coarse_all_strata)
    print("allowance_and_slack",
          (ALLOWANCE, ALLOWANCE - coarse_all_strata))
    print("verdict arithmetic-green_conormal-theorem-open")


if __name__ == "__main__":
    audit()
