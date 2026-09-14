#!/usr/bin/env python3
"""Mixed sharp-pivot / strong-capacity closure at the Full187 endpoint.

The earlier sharp-pivot support closure stopped at 70,543 live monomial rows
which have no next sharp pivot.  This executable asks the missing mixed-case
question: does each such row have a strong Hermite/error-value capacity
origin in the *literal full* 187-shape source?

For witnesses outside the terminal-safe 103 shapes, it additionally replaces
the terminal source exponent ``y=J-r-s`` by the lower-active choice ``y=f``
and shifts the passive exponent so total grade stays ``L``.  This checks that
the capacity source survives the deletion on the final terminal corner and
lands in exactly the same full passive row.

This is an exponent/window/source-legality certificate.  It does not orient
the other contact tails of a chosen CRT correction and is not a packet lift.
"""

from __future__ import annotations

from collections import Counter, deque
import hashlib
import json
from pathlib import Path
import resource

import full187_order2_pivot_remainder_closure_6900 as C
import full187_terminal_lowT_hasse_closure_audit_6900 as H


L = 2_703
TERMINAL_PASSIVE = L - H.J


def all_shapes():
    return tuple(
        (r, s)
        for s in range(H.CURVATURE + 1)
        for r in range(H.SLOPE - s + 1)
    )


def terminal_safe_shapes():
    return tuple(
        shape for shape in all_shapes()
        if H.compact_affine_free_shape(*shape)
    )


def pivot_closure_and_escapes():
    roots, origin_count = C.initial_rows()
    queue = deque(sorted(roots))
    seen = set(roots)
    escapes = set()
    live_edges = 0
    truncated_terms = 0
    while queue:
        row = queue.popleft()
        for successor in C.basis_support(row):
            if successor == row:
                continue
            if successor[0] + 3 * successor[1] >= H.M:
                truncated_terms += 1
                continue
            live_edges += 1
            if C.pivot_parameters(successor) is None:
                escapes.add(successor)
            elif successor not in seen:
                seen.add(successor)
                queue.append(successor)
    assert origin_count == 70_056
    assert len(roots) == 8_164
    assert len(seen) == 49_048
    assert len(escapes) == 70_543
    assert live_edges == 3_444_163
    assert truncated_terms == 7_242_188
    return roots, seen, escapes


def capacity_witnesses(escapes):
    """Return best safe and full-source capacity witnesses for escape rows."""
    safe = set(terminal_safe_shapes())
    safe_witness = {}
    full_witness = {}

    # A witness is ordered first by lower active degree and then
    # lexicographically.  This makes the output deterministic and maximizes
    # distance from the deleted active=J terminal corner.
    def record(table, row, witness):
        previous = table.get(row)
        key = (witness[0] + witness[1] + witness[2], witness)
        if previous is None or key < (
            previous[0] + previous[1] + previous[2], previous
        ):
            table[row] = witness

    for r, s in all_shapes():
        y_terminal = H.J - r - s
        for f in range(H.M):
            assert f <= y_terminal
            for a_e in range(f + 1):
                for c_s in range(f - a_e + 1):
                    base_weight = f + 2 * a_e + c_s
                    if base_weight >= H.M:
                        continue
                    for q in range(H.M - base_weight):
                        status, row, margin = H.origin_status(
                            r, s, f, a_e, c_s, q, H.ERRORS
                        )
                        if status != "capacity" or row not in escapes:
                            continue
                        depth = H.M - (base_weight + q)
                        witness = (r, s, f, a_e, c_s, q, depth, margin)
                        record(full_witness, row, witness)
                        if (r, s) in safe:
                            record(safe_witness, row, witness)

    assert set(full_witness) == escapes
    assert len(safe_witness) == 63_094
    assert len(escapes - set(safe_witness)) == 7_449
    return safe_witness, full_witness


def lower_active_receipt(row, witness):
    r, s, f, a_e, c_s, q, depth, margin = witness
    T, E, R, S, terminal_h = row
    active = f + r + s
    passive = L - active
    width = H.width(f, r, s)
    contact_weight = q + f + 2 * a_e + c_s

    assert (T, E, R, S) == (
        q + f - a_e + c_s,
        a_e,
        f - a_e - c_s + r,
        s + c_s,
    )
    assert terminal_h == H.J - r - s - f
    assert TERMINAL_PASSIVE + terminal_h == passive
    assert contact_weight < H.M
    assert depth == H.M - contact_weight > 0
    assert width - H.G * depth == margin
    assert H.G * depth + H.ERRORS <= width

    # Literal lower-active source:
    #   P(X) Y^f R^r S^s Z^(L-f-r-s).
    # Taking all f Y factors as contact factors and no received-direction
    # factor gives the requested row with coefficient-Hasse order q.
    assert active < H.J
    assert f + r + s <= H.J
    assert r + s <= H.SLOPE
    assert s <= H.CURVATURE
    assert passive >= 0
    assert active + passive == L
    assert width > 0
    return {
        "shape_r_s": (r, s),
        "f_aE_cS_q": (f, a_e, c_s, q),
        "depth_margin_width": (depth, margin, width),
        "lower_source_y_r_s_z": (f, r, s, passive),
        "lower_active_degree": active,
        "full_output_passive": passive,
    }


def histogram(values):
    return tuple(sorted(Counter(values).items()))


def main():
    roots, pivot_rows, escapes = pivot_closure_and_escapes()
    safe_witness, full_witness = capacity_witnesses(escapes)
    unsafe_only = escapes - set(safe_witness)

    receipts = {
        row: lower_active_receipt(row, full_witness[row])
        for row in escapes
    }
    unsafe_receipts = tuple(receipts[row] for row in sorted(unsafe_only))
    all_receipts = tuple(receipts[row] for row in sorted(escapes))

    # The prior terminal deletion is irrelevant to every chosen mixed-branch
    # correction: all witnesses are strictly below active grade J.  The rows
    # that specifically require one of the other 84 shapes sit much lower.
    all_active = tuple(r["lower_active_degree"] for r in all_receipts)
    unsafe_active = tuple(r["lower_active_degree"] for r in unsafe_receipts)
    assert max(all_active) < H.J
    assert (min(unsafe_active), max(unsafe_active)) == (22, 44)

    stable = {
        "scope": (
            "exact exponent/window mixed closure of every live sharp-pivot "
            "remainder row by a strong-capacity Full187 origin; correction "
            "tails and packet confluence are not claimed"
        ),
        "target_N_w_g_m_D_J_L_slope_curvature": (
            H.N, H.W, H.G, H.M, H.D, H.J, L,
            H.SLOPE, H.CURVATURE,
        ),
        "terminal_safe_and_full_shape_counts": (
            len(terminal_safe_shapes()), len(all_shapes())
        ),
        "initial_pivot_origins_distinct_rows": (70_056, len(roots)),
        "transitive_pivot_row_count": len(pivot_rows),
        "escaping_nonpivot_row_count": len(escapes),
        "capacity_coverage": {
            "within_terminal_safe103": len(safe_witness),
            "requiring_other_full187_shape": len(unsafe_only),
            "within_full187": len(full_witness),
            "uncovered": len(escapes - set(full_witness)),
        },
        "chosen_lower_active_degree_histogram": histogram(all_active),
        "unsafe_shape_only_lower_active_degree_histogram": histogram(
            unsafe_active
        ),
        "chosen_capacity_Hasse_order_histogram": histogram(
            full_witness[row][5] for row in escapes
        ),
        "chosen_capacity_depth_histogram": histogram(
            full_witness[row][6] for row in escapes
        ),
        "chosen_shape_histogram": tuple(sorted(Counter(
            full_witness[row][:2] for row in escapes
        ).items())),
        "first_32_unsafe_shape_only_rows_and_lifts": tuple(
            (row, receipts[row]) for row in sorted(unsafe_only)[:32]
        ),
        "lower_active_identity": (
            "for witness (r,s,f,aE,cS,q), use source y=f and "
            "z=L-f-r-s; then z=(L-J)+(J-r-s-f), the output row is "
            "unchanged, u1 exponent is zero, width is the certified "
            "strong-capacity width, and active degree is strictly below J"
        ),
        "decision": "GREEN_MIXED_SUPPORT_CLOSURE",
        "remaining_gate": (
            "choose and orient the complete CRT correction maps, replay all "
            "their contact/boundary tails, and prove termination/confluence "
            "for the four exact packets"
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
