#!/usr/bin/env python3
"""Audit the exact alternating high/low m69 dual-chain geometry.

This is deliberately independent of the rank implementation.  It enumerates
the already frozen deficient-shape superset, extracts every high-prefix / next
low-prefix pair, and records the low-degree K-chain forced by the exact
high-to-low relations.  The physical RS-dual anchor gives the corrected
recurrence N^2*K_j=E^2*K_(j+1), with no X^2 factor.  It is the numerical front
end for the small numerator-zero branch.
"""

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
D = M * G
E_MIN = 2_151


def width(y: int, r: int, s: int) -> int:
    return D - W * y - (W - 1) * r - (W - 2) * s


def raw_y_interval(active: int, n: int, s: int) -> tuple[int, ...]:
    if not 0 <= s <= CURVATURE or n + s >= M:
        return ()
    lower = max(0, active - SLOPE)
    upper = min(M - 1, active - s, n + s)
    return tuple(range(lower, upper + 1)) if lower <= upper else ()


def counts(active: int, n: int, legal: bool) -> tuple[int, ...]:
    out = []
    for s in range(CURVATURE + 1):
        count = 0
        for y in raw_y_interval(active, n, s):
            r = active - y - s
            q = n - y + s
            depth = min(M - y, width(y, r, s) // N)
            if not legal or q < depth:
                count += 1
        out.append(count)
    return tuple(out)


def jset(multiplicities: tuple[int, ...], h: int) -> tuple[int, ...]:
    return tuple(sorted(h - s for s, c in enumerate(multiplicities)
                        if 0 <= h - s < c))


def deficient_shapes() -> tuple[tuple[int, int, int], ...]:
    shapes = set()
    for active in range(J):
        for n in range(-CURVATURE, M):
            raw, legal = counts(active, n, False), counts(active, n, True)
            if not any(raw):
                continue
            for h in range(min(active, M - n - 1) + 1):
                dim = min(h + 1, M - n - h)
                rj, lj = jset(raw, h), jset(legal, h)
                if min(len(lj), dim) >= min(len(rj), dim):
                    continue
                for jj in set(rj) - set(lj):
                    s = h - jj
                    for y in raw_y_interval(active, n, s):
                        r = active - y - s
                        q = n - y + s
                        depth = min(M - y, width(y, r, s) // N)
                        if q >= depth:
                            shapes.add((y, r, s))
    return tuple(sorted(shapes))


def chain(shape: tuple[int, int, int]):
    y, r, s = shape
    fringes = tuple(width(y + t, r, s) % N for t in range(M - y))
    # A high prefix has small dual complement.  Pair it with the immediately
    # following low prefix; consecutive high pairs yield the square recurrence.
    high_indices = tuple(t for t in range(len(fringes) - 1)
                         if fringes[t] > N // 2 and fringes[t + 1] < N // 2)
    caps = tuple(N - fringes[t] for t in high_indices)
    k_caps = tuple(c - E_MIN for c in caps)
    return fringes, high_indices, caps, k_caps


def main():
    shapes = deficient_shapes()
    assert len(shapes) == 6_930
    rows = []
    for shape in shapes:
        fringes, inds, caps, kcaps = chain(shape)
        assert inds and all(k > 0 for k in kcaps)
        assert all(inds[i + 1] == inds[i] + 2 for i in range(len(inds) - 1))
        assert all(caps[i + 1] == caps[i] - 2 for i in range(len(caps) - 1))
        m = len(kcaps) - 1
        # If nonzero K_0,...,K_m obey all adjacent rank-one minors, UFD
        # rigidity writes K_j=C*A^(m-j)*B^j with gcd(A,B)=1.  Endpoint
        # degrees give these exact universal factor caps.
        a_cap = (kcaps[0] - 1) // m
        b_cap = (kcaps[-1] - 1) // m
        rows.append((shape, inds, caps, kcaps, fringes, a_cap, b_cap))

    min_pairs = min(len(r[1]) for r in rows)
    max_last_cap = max(r[2][-1] for r in rows)
    max_last_kcap = max(r[3][-1] for r in rows)
    max_penultimate_kcap = max(r[3][-2] for r in rows)
    max_a_degree = max(r[5] for r in rows)
    max_b_degree = max(r[6] for r in rows)
    # Optimize the *joint* UFD endpoint constraints, rather than combining
    # independent maxima which cannot occur in one chain.
    max_a_plus_c = -1
    max_b_plus_c = -1
    joint_witness = None
    for row in rows:
        shape, _inds, _caps, kcaps, _fringes, _acap, _bcap = row
        m = len(kcaps) - 1
        for a in range((kcaps[0] - 1) // m + 1):
            for b in range((kcaps[-1] - 1) // m + 1):
                c = min(kcaps[0] - 1 - m * a,
                        kcaps[-1] - 1 - m * b)
                if a + c > max_a_plus_c:
                    max_a_plus_c = a + c
                    joint_witness = (shape, m, kcaps[0], kcaps[-1], a, b, c)
                max_b_plus_c = max(max_b_plus_c, b + c)
    assert max_a_plus_c == 1_126
    assert max_b_plus_c == 1_124
    worst = [r for r in rows if r[2][-1] == max_last_cap]
    assert max_last_cap <= 3_276
    assert max_last_kcap <= 1_125
    assert max_penultimate_kcap <= 1_127
    # Degree(K_penultimate)<=1126, so the corrected last recurrence cannot
    # wrap at deg(N)<=130508.  At 130509 the same uniform proof becomes exact
    # degree 262144 and stops.
    assert 2 * 130_508 + (max_penultimate_kcap - 1) < N
    assert N <= 2 * 130_509 + (max_penultimate_kcap - 1)

    first = next(r for r in rows if r[0] == (39, 14, 10))
    low_hostile = next(r for r in rows if r[0] == (0, 0, 0))
    first_cutoff = (N - first[3][-2]) // 2
    assert first_cutoff == 130_537
    assert 2 * first_cutoff + first[3][-2] - 1 < N
    assert N <= 2 * (first_cutoff + 1) + first[3][-2] - 1
    result = {
        "shape_count": len(shapes),
        "shape_sha256": hashlib.sha256(repr(shapes).encode()).hexdigest(),
        "pair_count_histogram": sorted(Counter(len(r[1]) for r in rows).items()),
        "minimum_pair_count": min_pairs,
        "maximum_last_high_complement": max_last_cap,
        "maximum_last_K_dimension_cap_at_e2151": max_last_kcap,
        "maximum_penultimate_K_dimension_cap_at_e2151":
            max_penultimate_kcap,
        "maximum_geometric_denominator_degree": max_a_degree,
        "maximum_geometric_numerator_degree": max_b_degree,
        "maximum_joint_degree_A_plus_C": max_a_plus_c,
        "maximum_joint_degree_B_plus_C": max_b_plus_c,
        "joint_degree_witness_shape_m_K0cap_Kmcap_A_B_C": joint_witness,
        "large_zero_kill_threshold": max_last_kcap,
        "complementary_small_zero_regime": [0, max_last_kcap - 1],
        "corrected_recurrence": "N^2*K_j = E^2*K_(j+1) on nodes",
        "spurious_X2_recurrence": False,
        "uniform_corrected_no_wrap_numerator_cutoff": 130_508,
        "first_degree_not_closed_by_uniform_no_wrap": 130_509,
        "geometric_UFD_normal_form": (
            "if the chain is nonzero and has indices 0..m, then "
            "K_j=C*A^(m-j)*B^j with gcd(A,B)=1"
        ),
        "near_global_Pade_reduction": (
            "outside roots(C), N^2*A=E^2*B; equivalently "
            "Omega/gcd(Omega,C) divides N^2*A-E^2*B"
        ),
        "maximum_remaining_Pade_quotient_degree_at_degN149776":
            2 * 149_776 + max_a_plus_c - N,
        "worst_last_cap_examples": [
             {"shape": r[0], "high_indices": r[1], "high_caps": r[2],
             "K_caps": r[3], "A_degree_cap": r[5],
             "B_degree_cap": r[6]} for r in worst[:8]
        ],
        "first_defect": {
            "shape": first[0], "high_indices": first[1],
            "high_caps": first[2], "K_caps": first[3],
            "A_degree_cap": first[5], "B_degree_cap": first[6],
            "corrected_late_pair_no_wrap_numerator_cutoff": first_cutoff,
        },
        "low_hostile": {
            "shape": low_hostile[0], "high_indices": low_hostile[1],
            "high_caps": low_hostile[2], "K_caps": low_hostile[3],
            "A_degree_cap": low_hostile[5],
            "B_degree_cap": low_hostile[6],
        },
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
