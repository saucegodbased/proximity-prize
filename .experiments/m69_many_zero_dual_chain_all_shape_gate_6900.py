#!/usr/bin/env python3
"""Exact all-shape ledger for the m69 many-numerator-zero dual chain.

The algebraic input to this ledger is deliberately explicit.  For each
successive high/low pair of residual prefix windows, the proposed dual
normal form is

    H_high,j = E*K_j,       H_low,j = N*K_j,

and between successive pairs the nodal relation is

    N^2*K_j = E^2*K_(j+1).

This script checks every *numerical and combinatorial* premise needed by the
root/backward-recurrence argument.  It does not claim to derive that dual
normal form from the physical Full187 source map; that source adapter remains
a separate theorem obligation.
"""

from __future__ import annotations

from collections import Counter
import hashlib
import json
from pathlib import Path
import resource

import m69_reciprocal_all_defect_interval_gate_6900 as profile


E_MIN = 2_151
E_MAX = 18_414
N_DEG_MAX = 149_776
PROFILE_SHA256 = "9417a5797aa188cb6a1381b7c11e54f3df0ecf46908ad452d6dee925e1ae5069"


def prefix_trace(shape: tuple[int, int, int]) -> tuple[int, ...]:
    y, r, s = shape
    return tuple(
        profile.width(y + t, r, s) % profile.N
        for t in range(profile.M - y)
    )


def high_low_pairs(shape: tuple[int, int, int]):
    """Return every high-prefix index which is followed by a low prefix."""
    fringes = prefix_trace(shape)
    pairs = []
    for t in range(len(fringes) - 1):
        high, low = fringes[t], fringes[t + 1]
        if high > profile.W and low <= profile.W:
            pairs.append((t, high, low, profile.N - high, profile.N - low))
    return fringes, tuple(pairs)


def shape_record(shape: tuple[int, int, int]):
    fringes, pairs = high_low_pairs(shape)
    assert len(pairs) >= 2

    # Subtracting W=N/2-1 alternates high and low prefixes.  Across two
    # powers, a high fringe rises by exactly two, so its dual cap drops by
    # exactly two.  This fixes the orientation of the chain: K_j is on the
    # N^2 side and K_(j+1) is on the E^2 side.  There is no X^2 multiplier:
    # for the literal channels W^t*F_<f_t and W=N/E, the common nodal factor
    # x in the standard prefix-dual encoding cancels at each adjacent step.
    # Reversing the recurrence would not force K_(j+1) on Z(N).
    assert all(
        (fringes[t] > profile.W) != (fringes[t + 1] > profile.W)
        for t in range(len(fringes) - 1)
    )
    assert all(
        pairs[j + 1][0] == pairs[j][0] + 2
        and pairs[j + 1][1] == pairs[j][1] + 2
        and pairs[j + 1][3] == pairs[j][3] - 2
        for j in range(len(pairs) - 1)
    )

    # The adjacent high/low relation N*H_high=E*H_low is below the cyclic
    # modulus even at the exact DataEleven degree maxima.  Hence coprimality
    # can legitimately yield H_high=E*K and H_low=N*K.
    for _t, _high, _low, high_cap, low_cap in pairs:
        assert N_DEG_MAX + (high_cap - 1) < profile.N
        assert E_MAX + (low_cap - 1) < profile.N

    last = pairs[-1]
    last_cap = last[3]
    threshold_at_min_e = max(0, last_cap - E_MIN)
    assert E_MIN + threshold_at_min_e >= last_cap

    return {
        "shape": shape,
        "available_powers": len(fringes),
        "initial_parity": "high" if fringes[0] > profile.W else "low",
        "pair_count": len(pairs),
        "first_pair": pairs[0],
        "last_pair": last,
        "last_high_cap": last_cap,
        "zero_threshold_at_e2151": threshold_at_min_e,
        "maximum_pair_high_cap": max(pair[3] for pair in pairs),
        "maximum_pair_low_cap": max(pair[4] for pair in pairs),
    }


def main():
    profile_path = Path(profile.__file__)
    assert hashlib.sha256(profile_path.read_bytes()).hexdigest() == PROFILE_SHA256
    defects, shapes, coefficients = profile.defect_census()
    records = tuple(shape_record(shape) for shape in shapes)

    assert len(defects) == 13_093
    assert len(shapes) == 6_930
    assert len(coefficients) == 140_153

    initial_histogram = Counter(record["initial_parity"] for record in records)
    assert initial_histogram == Counter({"high": 3_546, "low": 3_384})

    pair_count_min = min(record["pair_count"] for record in records)
    pair_count_max = max(record["pair_count"] for record in records)
    assert (pair_count_min, pair_count_max) == (13, 34)

    last_cap_min = min(record["last_high_cap"] for record in records)
    last_cap_max = max(record["last_high_cap"] for record in records)
    assert (last_cap_min, last_cap_max) == (3_218, 3_276)
    assert max(record["zero_threshold_at_e2151"] for record in records) == 1_125

    # A nonzero numerator of degree <=149776 has at most that many distinct
    # domain zeros.  Thus its complement has at least 112368 nodes.  Every
    # earlier K_j has degree < high_cap-e <=3342-2151=1191, so restriction to
    # the complement kills it during backward induction.
    complement_min = profile.N - N_DEG_MAX
    maximum_earlier_kernel_degree_exclusive = (
        max(record["maximum_pair_high_cap"] for record in records) - E_MIN
    )
    no_wrap_NH_degree_upper = (
        N_DEG_MAX + max(record["maximum_pair_high_cap"] for record in records)
        - 1
    )
    no_wrap_EH_degree_upper = (
        E_MAX + max(record["maximum_pair_low_cap"] for record in records) - 1
    )
    assert complement_min == 112_368
    assert maximum_earlier_kernel_degree_exclusive == 1_191
    assert maximum_earlier_kernel_degree_exclusive <= complement_min
    assert no_wrap_NH_degree_upper == 153_117 < profile.N
    assert no_wrap_EH_degree_upper == 152_826 < profile.N

    # Literal controls requested in the route audit.
    by_shape = {record["shape"]: record for record in records}
    base = by_shape[(0, 0, 0)]
    first_defect = by_shape[(39, 14, 10)]
    assert base["last_high_cap"] == 3_276
    assert base["zero_threshold_at_e2151"] == 1_125
    assert first_defect["last_high_cap"] == 3_218
    assert first_defect["zero_threshold_at_e2151"] == 1_067

    # Uniform conclusion of the *conditional* recurrence theorem:
    # z>=1125 and e>=2151 imply e+z>=every last high cap.  High-initial
    # annihilators are killed outright.  Low-initial annihilators are killed
    # after the first channel and hence can only be supported on Z(N).
    zero_threshold = 1_125
    assert all(
        E_MIN + zero_threshold >= record["last_high_cap"]
        for record in records
    )

    receipt = tuple(
        (
            record["shape"], record["available_powers"],
            record["initial_parity"], record["pair_count"],
            record["first_pair"], record["last_pair"],
            record["zero_threshold_at_e2151"],
        )
        for record in records
    )
    result = {
        "status": "CONDITIONAL_M69_MANY_ZERO_DUAL_CHAIN_GREEN",
        "profile": (
            profile.M, profile.SLOPE, profile.CURVATURE, profile.J, profile.L
        ),
        "profile_source_sha256": PROFILE_SHA256,
        "defect_stratum_count": len(defects),
        "deficient_shape_count": len(shapes),
        "deficient_coefficient_count": len(coefficients),
        "initial_parity_histogram": tuple(sorted(initial_histogram.items())),
        "pair_count_range": (pair_count_min, pair_count_max),
        "last_high_cap_range": (last_cap_min, last_cap_max),
        "uniform_denominator_degree_lower": E_MIN,
        "uniform_many_zero_threshold": zero_threshold,
        "numerator_degree_upper": N_DEG_MAX,
        "domain_complement_lower": complement_min,
        "earlier_kernel_degree_exclusive_upper": (
            maximum_earlier_kernel_degree_exclusive
        ),
        "adjacent_high_low_no_wrap_degree_upper_NH_EH": (
            no_wrap_NH_degree_upper, no_wrap_EH_degree_upper
        ),
        "base_shape_000": base,
        "literal_first_defect_shape": first_defect,
        "high_initial_conclusion": (
            "conditional recurrence forces the whole dual annihilator to zero"
        ),
        "low_initial_conclusion": (
            "conditional recurrence forces the dual annihilator to be "
            "supported on numerator-zero nodes"
        ),
        "recurrence_orientation": "N^2*K_j = E^2*K_(j+1) on nodes",
        "receipt_sha256": hashlib.sha256(repr(receipt).encode()).hexdigest(),
        "scope": (
            "all-shape arithmetic plus consequences of the stated dual "
            "normal-form/recurrence assumptions; does not derive those "
            "assumptions from the physical Full187 source; explicitly "
            "rejects the unjustified X^2 normalization"
        ),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
