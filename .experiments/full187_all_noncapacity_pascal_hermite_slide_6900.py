#!/usr/bin/env python3
"""Exact Full187 elimination of every non-strong-capacity top block.

Fix a terminal stream

    C(X) Y^(J-r-s) R^r S^s Z^(L-J).

At a node, its ``u0``-free term of contact-Y degree ``f`` and coefficient
Hasse order ``q`` has a common coefficient (before expanding contactY)

    binom(J-r-s,f) * u1^(J-r-s-f) * H_q(C).

For selected ``f`` add a legal lower-active source

    P_f(X) Y^f R^r S^s Z^(L-f-r-s).

Its top term at contact degree ``k <= f`` has the same passive exponent and
common coefficient ``binom(f,k) u1^(f-k) H_q(P_f)``.  Processing selected
``f`` downward therefore gives a unitriangular Pascal recurrence.  This
executable enumerates every literal Full187 origin and proves that every
origin which lacks the strong agreement-Hermite/error-value CRT license is
covered by such a recurrence inside a complete all-node Hermite window.

The formal sparse-expression replay treats every unprescribed higher jet of
an earlier correction as an independent symbol.  Hence the cancellation does
not assume those jets vanish or have a convenient canonical representative.

This is an exact theorem about the u0-free top diagonal.  Terms containing
u0 land at lower passive grade and define the still-open connecting map; the
script deliberately makes no packet-containment or full-kernel claim.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from math import comb, factorial
import hashlib
import json
from pathlib import Path
import resource

import full187_terminal_lowT_hasse_closure_audit_6900 as H


P = 2_130_706_433
N = H.N
J = H.J
L = 2_703
M = H.M
TERMINAL_Z = L - J


def all_shapes():
    return tuple(
        (r, s)
        for s in range(H.CURVATURE + 1)
        for r in range(H.SLOPE - s + 1)
    )


def enumerate_origin_licenses():
    """Return exact origin counts and noncapacity q sets by (r,s,f)."""
    counts = Counter()
    qsets = defaultdict(set)
    group_statuses = defaultdict(Counter)
    qclass_statuses = Counter()
    noncapacity_origins = 0

    for r, s in all_shapes():
        terminal_y = J - r - s
        for f in range(M):
            assert f <= terminal_y
            for a_e in range(f + 1):
                for c_s in range(f - a_e + 1):
                    base_weight = f + 2 * a_e + c_s
                    if base_weight >= M:
                        continue
                    for q in range(M - base_weight):
                        status, _row, _margin = H.origin_status(
                            r, s, f, a_e, c_s, q, H.ERRORS
                        )
                        counts[status] += 1
                        qclass_statuses[("q0" if q == 0 else "qpos",
                                         status)] += 1
                        if status != "capacity":
                            noncapacity_origins += 1
                            qsets[(r, s, f)].add(q)
                            group_statuses[(r, s, f)][status] += 1

                            # Expansion of contactY^f has a nonzero scalar
                            # on every surviving (aE,cS) monomial.  Thus
                            # killing its common coefficient kills the whole
                            # homogeneous contact block, including this row.
                            remaining = f - a_e - c_s
                            scalar = (
                                factorial(f)
                                // (factorial(a_e) * factorial(c_s)
                                    * factorial(remaining))
                            ) % P
                            scalar = scalar * pow(
                                -pow(2, -1, P) % P, c_s, P
                            ) % P
                            assert scalar != 0

    assert counts == Counter({
        "capacity": 20_083_846,
        "pivot": 294_912,
        "obstruction": 36_967,
    })
    assert sum(counts.values()) == 20_415_725
    assert noncapacity_origins == 331_879
    assert len(qsets) == 6_709
    return counts, qclass_statuses, qsets, group_statuses


def add_scaled_shifted(target, source, scalar, u_shift):
    """target += scalar * u^u_shift * source over the target field.

    Expressions are sparse in independent jet symbols and the formal node
    scalar u.  Keys are ``(symbol, exponent_of_u)``.
    """
    scalar %= P
    for (symbol, exponent), coefficient in source.items():
        key = (symbol, exponent + u_shift)
        value = (target.get(key, 0) + scalar * coefficient) % P
        if value:
            target[key] = value
        else:
            target.pop(key, None)


def residual_expression(terminal_y, contact_f, correction_jets):
    """Formal common coefficient at one fixed node and Hasse order."""
    answer = {(("C",), terminal_y - contact_f):
              comb(terminal_y, contact_f) % P}
    for source_f, expression in correction_jets.items():
        if source_f <= contact_f:
            continue
        add_scaled_shifted(
            answer, expression, comb(source_f, contact_f),
            source_f - contact_f,
        )
    return answer


def negate(expression):
    return {key: (-value) % P for key, value in expression.items() if value}


def replay_unitriangular_pascal(qsets):
    """Check cancellation formally, including arbitrary higher correction jets."""
    shapes_to_groups = defaultdict(dict)
    for (r, s, f), qs in qsets.items():
        shapes_to_groups[(r, s)][f] = max(qs)

    formal_zero_checks = 0
    arbitrary_higher_jet_symbols = 0
    maximum_expression_terms = 0
    for (r, s), qmax_by_f in sorted(shapes_to_groups.items()):
        terminal_y = J - r - s
        selected_f = tuple(sorted(qmax_by_f, reverse=True))
        global_qmax = max(qmax_by_f.values())

        for q in range(global_qmax + 1):
            correction_jets = {}
            for f in selected_f:
                if q > qmax_by_f[f]:
                    # This Hasse jet exists but was not prescribed by the
                    # depth-(Q_f+1) Hermite lift.  Treat it adversarially.
                    correction_jets[f] = {(('U', f, q), 0): 1}
                    arbitrary_higher_jet_symbols += 1
                    continue

                before = residual_expression(
                    terminal_y, f, correction_jets)
                correction_jets[f] = negate(before)
                after = residual_expression(
                    terminal_y, f, correction_jets)
                # residual_expression omits the diagonal P_f term by design;
                # add it explicitly.  Its coefficient is binom(f,f)=1.
                add_scaled_shifted(after, correction_jets[f], 1, 0)
                assert not after
                formal_zero_checks += 1
                maximum_expression_terms = max(
                    maximum_expression_terms, len(correction_jets[f]))

    assert formal_zero_checks == sum(len(qs) for qs in qsets.values())
    return {
        "formal_zero_checks": formal_zero_checks,
        "adversarial_unprescribed_higher_jet_symbols":
            arbitrary_higher_jet_symbols,
        "maximum_sparse_expression_terms": maximum_expression_terms,
    }


def group_receipt(qsets, group_statuses):
    qmax_histogram = Counter()
    group_status_mix = Counter()
    active_histogram = Counter()
    per_shape_group_counts = Counter()
    slacks = []
    legality_rows = []

    for (r, s, f), qs in sorted(qsets.items()):
        qmax = max(qs)
        # Noncapacity is a literal initial interval: later q has larger
        # Hermite margin, while the sharp-pivot T coordinate only increases.
        assert qs == set(range(qmax + 1))

        width = H.width(f, r, s)
        needed = (qmax + 1) * N
        slack = width - needed
        assert slack >= 0
        slacks.append((slack, r, s, f, qmax, width))
        qmax_histogram[qmax] += 1

        statuses = group_statuses[(r, s, f)]
        status_key = tuple(sorted(status for status in statuses if statuses[status]))
        group_status_mix[status_key] += 1

        active = f + r + s
        correction_z = L - active
        terminal_y = J - r - s
        terminal_top_passive = TERMINAL_Z + terminal_y - f
        assert correction_z == terminal_top_passive
        assert active < J
        assert correction_z >= 0
        assert active + correction_z == L
        active_histogram[active] += 1
        per_shape_group_counts[(r, s)] += 1
        legality_rows.append((active, correction_z, r, s, f, qmax))

    assert max(qmax_histogram) == 15
    assert min(slacks) == (339_119, 21, 0, 57, 0, 601_263)
    assert max(row[0] for row in legality_rows) == 78
    return {
        "qmax_histogram": tuple(sorted(qmax_histogram.items())),
        "group_status_mix": tuple(sorted(
            (("+".join(key), count) for key, count in group_status_mix.items())
        )),
        "minimum_window_slack_at_r_s_f_Q_width": min(slacks),
        "maximum_window_slack_at_r_s_f_Q_width": max(slacks),
        "correction_active_degree_min_max": (
            min(active_histogram), max(active_histogram)),
        "correction_active_degree_histogram": tuple(sorted(active_histogram.items())),
        "per_terminal_stream_correction_group_min_max": (
            min(per_shape_group_counts.values()),
            max(per_shape_group_counts.values()),
        ),
    }


def main():
    counts, qclass_statuses, qsets, group_statuses = enumerate_origin_licenses()
    groups = group_receipt(qsets, group_statuses)
    formal = replay_unitriangular_pascal(qsets)

    stable = {
        "scope": (
            "exact all-187-shape u0-free terminal-top projection: every "
            "origin lacking the strong agreement-Hermite/error-value CRT "
            "license is canceled by a legal descending Pascal/all-node "
            "Hermite slide; lower-passive u0 tails and packet containment "
            "are not claimed"
        ),
        "target_p_N_w_g_errors_m_D_J_L_slope_curvature": (
            P, H.N, H.W, H.G, H.ERRORS, H.M, H.D, H.J, L,
            H.SLOPE, H.CURVATURE,
        ),
        "terminal_derivative_shape_count": len(all_shapes()),
        "all_surviving_origin_count": sum(counts.values()),
        "origin_license_counts": tuple(sorted(counts.items())),
        "origin_qclass_license_counts": tuple(sorted(
            (qclass, status, count)
            for (qclass, status), count in qclass_statuses.items()
        )),
        "non_strong_capacity_origin_count": sum(
            counts[status] for status in ("pivot", "obstruction")),
        "noncapacity_r_s_f_group_count": len(qsets),
        "every_noncapacity_q_set_is_initial_interval": True,
        "maximum_noncapacity_Hasse_order": max(max(qs) for qs in qsets.values()),
        "every_group_complete_all_node_Hermite_window_fits": True,
        "group_receipt": groups,
        "pascal_recurrence": {
            "terminal_common_coefficient":
                "binom(J-r-s,f) u1^(J-r-s-f) H_q(C)",
            "higher_layer_contribution":
                "binom(k,f) u1^(k-f) H_q(P_k)",
            "diagonal": "binom(f,f)=1; no division by u1",
            "orientation": "strictly descending f",
            **formal,
        },
        "literal_source_legality": {
            "correction": "P_f(X) Y^f R^r S^s Z^(L-f-r-s)",
            "same_total_grade_L": True,
            "strictly_below_deleted_active_grade_J": True,
            "top_passive_identity":
                "L-f-r-s = (L-J)+(J-r-s-f)",
        },
        "decision": "GREEN_ALL_NONCAPACITY_TOP_BLOCKS_PROJECT_TO_CAPACITY",
        "remaining_exact_gate": (
            "Instantiate a simultaneous strong-capacity section for the "
            "residual top terms and propagate every u0/lower-passive tail "
            "through the literal low-Z packet connecting map.  This receipt "
            "does not assert those tails vanish or that F0..F3 are in range."
        ),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    payload = {
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
