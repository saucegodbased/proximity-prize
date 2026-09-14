#!/usr/bin/env python3
"""Maximal complete-depth Pascal/Hermite slide on the Full187 top shell.

This strengthens ``full187_all_noncapacity_pascal_hermite_slide_6900``.
For every one of the 187 physical terminal streams and every contact degree
``f=0,...,59``, use the entire complete all-node Hermite depth

    A(r,s,f) = floor(width(r,s,f) / N).

The legal correction coefficient P_f can prescribe Hasse jets 0 through
A-1 at every node.  A descending Pascal recurrence cancels those complete
homogeneous contact blocks simultaneously.  The executable counts the exact
provenance removed and proves that every residual origin has the stronger
mixed agreement-Hermite/error-value capacity license.

No claim is made about the simultaneous physical section for those residual
capacity blocks or about the lower-passive u0 connecting tails.
"""

from __future__ import annotations

from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import resource

import full187_terminal_lowT_hasse_closure_audit_6900 as H
import full187_all_noncapacity_pascal_hermite_slide_6900 as A


N = H.N
J = H.J
L = 2_703
M = H.M


def complete_qmax(r: int, s: int, f: int) -> int:
    depth = H.width(f, r, s) // N
    assert depth >= 1
    return min(depth - 1, M - f - 1)


def exact_origin_census():
    counts = Counter()
    residual_blocks = Counter()
    residual_rows = set()
    killed_rows = set()
    first_residual = {}

    for r, s in A.all_shapes():
        for f in range(M):
            qmax = complete_qmax(r, s, f)
            for a_e in range(f + 1):
                for c_s in range(f - a_e + 1):
                    base = f + 2 * a_e + c_s
                    if base >= M:
                        continue
                    for q in range(M - base):
                        status, row, _margin = H.origin_status(
                            r, s, f, a_e, c_s, q, H.ERRORS
                        )
                        counts["all"] += 1
                        if q <= qmax:
                            counts["complete_depth_cancelled"] += 1
                            killed_rows.add(row)
                        else:
                            # 7504148 proves every noncapacity q lies below
                            # the complete all-node depth.  Check the stronger
                            # conclusion literally on all residual origins.
                            assert status == "capacity"
                            counts["residual_strong_capacity"] += 1
                            residual_blocks[(r, s, f, q)] += 1
                            residual_rows.add(row)
                            first_residual.setdefault(
                                (r, s, f), (q, H.width(f, r, s) % N))

    assert counts == Counter({
        "all": 20_415_725,
        "complete_depth_cancelled": 17_793_064,
        "residual_strong_capacity": 2_622_661,
    })
    assert len(residual_blocks) == 126_315
    return counts, residual_blocks, residual_rows, killed_rows, first_residual


def formal_pascal_replay():
    """Replay all 11,220 blocks with adversarial unprescribed higher jets."""
    zero_checks = 0
    adversarial_symbols = 0
    maximum_terms = 0

    for r, s in A.all_shapes():
        terminal_y = J - r - s
        qmax_by_f = {f: complete_qmax(r, s, f) for f in range(M)}
        global_qmax = max(qmax_by_f.values())

        for q in range(global_qmax + 1):
            correction_jets = {}
            for f in range(M - 1, -1, -1):
                if q > qmax_by_f[f]:
                    correction_jets[f] = {(('U', f, q), 0): 1}
                    adversarial_symbols += 1
                    continue

                before = A.residual_expression(
                    terminal_y, f, correction_jets)
                correction_jets[f] = A.negate(before)
                after = A.residual_expression(
                    terminal_y, f, correction_jets)
                A.add_scaled_shifted(after, correction_jets[f], 1, 0)
                assert not after
                zero_checks += 1
                maximum_terms = max(maximum_terms,
                                    len(correction_jets[f]))

    assert zero_checks == sum(
        complete_qmax(r, s, f) + 1
        for r, s in A.all_shapes() for f in range(M)
    ) == 215_895
    return {
        "formal_zero_checks": zero_checks,
        "adversarial_unprescribed_higher_jet_symbols": adversarial_symbols,
        "maximum_sparse_expression_terms": maximum_terms,
    }


def window_and_source_receipt():
    depth_histogram = Counter()
    qmax_histogram = Counter()
    active_histogram = Counter()
    fringes = []
    for r, s in A.all_shapes():
        terminal_y = J - r - s
        for f in range(M):
            width = H.width(f, r, s)
            depth = width // N
            qmax = complete_qmax(r, s, f)
            fringe = width - depth * N
            assert depth * N <= width < (depth + 1) * N
            assert 0 <= qmax < M - f
            active = f + r + s
            correction_z = L - active
            assert active <= 80 < J
            assert correction_z == (L - J) + terminal_y - f
            depth_histogram[depth] += 1
            qmax_histogram[qmax] += 1
            active_histogram[active] += 1
            fringes.append((fringe, r, s, f, depth, qmax, width))

    assert len(fringes) == 187 * M == 11_220
    assert min(row[4] for row in fringes) == 1
    assert max(row[4] for row in fringes) == 41
    assert min(fringes) == (76_876, 0, 0, 0, 41, 40, 10_824_780)
    return {
        "physical_correction_block_count": len(fringes),
        "complete_depth_min_max": (
            min(depth_histogram), max(depth_histogram)),
        "complete_depth_histogram": tuple(sorted(depth_histogram.items())),
        "cancelled_qmax_min_max": (min(qmax_histogram), max(qmax_histogram)),
        "cancelled_qmax_histogram": tuple(sorted(qmax_histogram.items())),
        "minimum_full_depth_fringe_at_r_s_f_depth_qmax_width": min(fringes),
        "correction_active_degree_min_max": (
            min(active_histogram), max(active_histogram)),
    }


def main():
    counts, residual_blocks, residual_rows, killed_rows, first_residual = (
        exact_origin_census())
    formal = formal_pascal_replay()
    windows = window_and_source_receipt()

    residual_q_histogram = Counter(q for (_r, _s, _f, q)
                                   in residual_blocks)
    residual_contact_f_histogram = Counter(f for (_r, _s, f, _q)
                                           in residual_blocks)
    first_q_histogram = Counter(q for q, _fringe in first_residual.values())

    stable = {
        "scope": (
            "maximal complete-all-node Hermite/Pascal projection of every "
            "Full187 terminal u0-free top block; residual simultaneous "
            "capacity section, u0 tails, connecting map, and packets open"
        ),
        "target_N_w_g_errors_m_D_J_L_slope_curvature": (
            H.N, H.W, H.G, H.ERRORS, H.M, H.D, H.J, L,
            H.SLOPE, H.CURVATURE,
        ),
        "origin_counts": tuple(sorted(counts.items())),
        "cancelled_fraction_numerator_denominator": (
            counts["complete_depth_cancelled"], counts["all"]),
        "cancelled_fraction_decimal": (
            counts["complete_depth_cancelled"] / counts["all"]),
        "distinct_row_shapes_cancelled_residual_intersection": (
            len(killed_rows), len(residual_rows), len(killed_rows & residual_rows)),
        "residual_r_s_f_q_block_count": len(residual_blocks),
        "residual_provenance_multiplicity_min_max": (
            min(residual_blocks.values()), max(residual_blocks.values())),
        "residual_q_min_max": (
            min(residual_q_histogram), max(residual_q_histogram)),
        "residual_q_histogram": tuple(sorted(residual_q_histogram.items())),
        "residual_contact_f_min_max": (
            min(residual_contact_f_histogram),
            max(residual_contact_f_histogram)),
        "first_residual_q_histogram": tuple(sorted(first_q_histogram.items())),
        "every_residual_origin_is_strong_capacity": True,
        "window_and_source_receipt": windows,
        "pascal_recurrence": formal,
        "decision": "GREEN_COMPLETE_DEPTH_KILLS_87_PERCENT_OF_TOP_PROVENANCE",
        "remaining_exact_gate": (
            "Resolve the 2,622,661 residual strong-capacity provenance terms "
            "as reused physical source blocks, then propagate u0 tails into "
            "the exact low-Z F0..F3 connecting map.  The q26 ninth-difference "
            "bypass is the first structural extension beyond complete depth."
        ),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    print(json.dumps({
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
