#!/usr/bin/env python3
"""Exact arithmetic receipt for the m69 numerator-zero rank countergate.

This does not construct a full DataEleven leaf.  It falsifies the proposed
*universal* arbitrary-rational prefix-rank theorem under its advertised
degree/root-free/coprime hypotheses.  The missing full-leaf input would have
to bound the number of N0 zeros on the NTT domain or provide another channel
which remains nonzero there.
"""

from __future__ import annotations

import hashlib
import json
import resource

import m69_reciprocal_all_defect_interval_gate_6900 as profile


def main():
    _defects, shapes, _coefficients = profile.defect_census()
    shape = (0, 0, 0)
    assert shape in shapes

    n = profile.N
    base_fringe = profile.width(*shape) % n
    traces = tuple(
        profile.width(power, 0, 0) % n for power in range(profile.M)
    )
    assert base_fringe == 127_729
    assert traces[:8] == (
        127_729, 258_802, 127_731, 258_804,
        127_733, 258_806, 127_735, 258_808,
    )

    # Choose N0 as the locator of any this-many NTT nodes.  Its degree is the
    # cardinality below.  Choose E0=X^2151-C(theta), with theta outside the
    # Frobenius-fixed base field, so E0 is nonzero on every NTT node and is
    # coprime to this split locator.  Existing repository lemmas also provide
    # E0's required conjugate-coprimality properties.
    zero_count = base_fringe + 1
    denominator_degree = 2_151
    cross_degree = 0
    homogeneous_degree = 0
    numerator_degree_cap = 131_071 + denominator_degree + cross_degree

    assert zero_count == 127_730
    assert zero_count <= numerator_degree_cap
    assert denominator_degree >= cross_degree + homogeneous_degree + 2_151
    assert denominator_degree < 18_415
    assert cross_degree + homogeneous_degree <= 8_328

    # On the zero set, W^t=0 for every t>=1.  Consequently every positive
    # predecessor block disappears after restriction.  The only surviving
    # block is an RS prefix with at most base_fringe dimensions, while the
    # restricted codomain has zero_count dimensions.
    restriction_rank_upper = base_fringe
    restriction_target_dimension = zero_count
    assert restriction_rank_upper < restriction_target_dimension

    chosen_node_indices = tuple(range(zero_count))
    result = {
        "status": "UNIVERSAL_ARBITRARY_RATIONAL_RANK_RED",
        "profile": (profile.M, profile.SLOPE, profile.CURVATURE,
                    profile.J, profile.L),
        "deficient_shape": shape,
        "available_power_count": profile.M,
        "first_eight_prefix_fringes": traces[:8],
        "base_prefix": base_fringe,
        "numerator_zero_count": zero_count,
        "restriction_rank_upper": restriction_rank_upper,
        "restriction_target_dimension": restriction_target_dimension,
        "forced_rank_defect_at_least": (
            restriction_target_dimension - restriction_rank_upper
        ),
        "denominator": "X^2151-C(theta), theta non-Frobenius-fixed",
        "denominator_degree": denominator_degree,
        "numerator": "locator of the selected NTT nodes",
        "numerator_degree": zero_count,
        "numerator_degree_cap": numerator_degree_cap,
        "numerator_degree_slack": numerator_degree_cap - zero_count,
        "cross_degree_s": cross_degree,
        "homogeneous_degree_q": homogeneous_degree,
        "excess": denominator_degree-cross_degree-homogeneous_degree,
        "selected_node_index_sha256": hashlib.sha256(
            repr(chosen_node_indices).encode()
        ).hexdigest(),
        "reason": (
            "all W^t channels for t>=1 vanish on 127730 nodes; the only "
            "remaining C_127729 prefix cannot surject onto those coordinates"
        ),
        "scope": (
            "falsifies the abstract arbitrary-rational rank claim; a full "
            "DataEleven incidence/source theorem might exclude this zero set"
        ),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
