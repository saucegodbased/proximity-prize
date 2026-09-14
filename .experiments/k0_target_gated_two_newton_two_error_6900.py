#!/usr/bin/env python3
"""Exact finite gate for the first genuinely multi-parameter k=0 chamber.

This is not a target theorem or a random rank scan.  It uses the smallest
promoted second-jet profile with all of the numerical target gates, two
agreement Newton coordinates beyond the degree-w anchor, and two error nodes:

    (n,w,g,m,B,s,U,L,k,n0) = (7,2,5,4,2,1,7,7,0,1).

Over F_11, after killing the degree-two anchor values, write the agreement
interpolant in the Newton basis as

    Q = binom(X,3) + t*binom(X,4).

The first extra coordinate is fixed to one and the later coordinate t is
exhausted.  At the two errors, five prescribed mismatch patterns are tested.
Every matrix and every rank is exact.
"""

from __future__ import annotations

from collections import Counter
import hashlib
import json
import multiprocessing as mp
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat

sys.path.insert(0, ".experiments")
from higher_jet_literal_matrix import translated_column  # noqa: E402
from higher6810_secondjet_retarget_exact import relaxed_rank_bound  # noqa: E402
import secondjet_candidate_major_function_field_rank_gate_6900 as K0  # noqa: E402


PRIME = 11
PROFILE = K0.Profile(7, 2, 5, 4, 2, 1, 7, 7, 0, 1)
NODES = tuple(range(7))
AGREEMENT = tuple(range(5))
ERRORS = (5, 6)
BOUNDARY_X = 7
MONOMIALS = K0.support(PROFILE)


def contact_columns(t: int, epsilon5: int, epsilon6: int):
    """Columns for Q=C(X,3)+t*C(X,4) and the given error mismatches."""
    t %= PRIME
    # C(0..6,3) = 0,0,0,1,4,10,20 and
    # C(0..6,4) = 0,0,0,0,1,5,15.
    q5 = (10 + 5 * t) % PRIME
    q6 = (20 + 15 * t) % PRIME
    u0 = (0, 0, 0, 0, 0, 1, 1)
    u1 = (
        0, 0, 0, 1, (4 + t) % PRIME,
        (q5 + epsilon5) % PRIME,
        (q6 + epsilon6) % PRIME,
    )
    answer = []
    for xp, yp, rp, sp, zp in MONOMIALS:
        column = {}
        for node in NODES:
            expansion = translated_column(
                xp, (yp, rp, sp), zp, node, u0[node], u1[node],
                PROFILE.m, 2, PRIME,
            )
            for term, value in expansion.items():
                if value:
                    column[(node, term)] = value
        answer.append(column)
    return tuple(answer)


def dense(columns, rows):
    return nmod_mat(
        len(rows), len(columns),
        [columns[j].get(rows[i], 0)
         for i in range(len(rows)) for j in range(len(columns))],
        PRIME,
    )


def boundary_matrix():
    return nmod_mat(
        4, len(MONOMIALS),
        [
            pow(BOUNDARY_X, monomial[0], PRIME)
            if sum(monomial[1:]) == 1 and monomial[1:][coordinate] == 1
            else 0
            for coordinate in range(4)
            for monomial in MONOMIALS
        ],
        PRIME,
    )


BOUNDARY = boundary_matrix()


def stack(top, bottom):
    return nmod_mat(
        top.nrows() + bottom.nrows(), top.ncols(),
        [int(top[i, j])
         for i in range(top.nrows()) for j in range(top.ncols())]
        + [int(bottom[i, j])
           for i in range(bottom.nrows()) for j in range(bottom.ncols())],
        PRIME,
    )


def instance(spec):
    label, t, epsilon5, epsilon6 = spec
    columns = contact_columns(t, epsilon5, epsilon6)
    rows = tuple(sorted(set().union(*(set(c) for c in columns)), key=repr))
    contact = dense(columns, rows)
    contact_rank = contact.rank()
    augmented_rank = stack(contact, BOUNDARY).rank()
    return {
        "pattern": label,
        "later_newton_t": t,
        "error_mismatches": (epsilon5, epsilon6),
        "contact_rows_rank": (len(rows), contact_rank),
        "augmented_rank": augmented_rank,
        "conormal_gain": augmented_rank - contact_rank,
    }


def main():
    started = time.monotonic()
    local_rank = relaxed_rank_bound(
        PROFILE.m, PROFILE.L, PROFILE.B, PROFILE.s, PROFILE.U)
    global_cap = PROFILE.n * local_rank
    terminal_width = (
        PROFILE.m * PROFILE.agreements
        - PROFILE.w * (PROFILE.B + PROFILE.m + 1)
    )
    assert (len(MONOMIALS), local_rank, global_cap) == (1728, 183, 1281)
    assert len(MONOMIALS) > global_cap
    assert PROFILE.B == 2 * PROFILE.s
    assert PROFILE.U - PROFILE.B == PROFILE.m + 1
    assert terminal_width == 6 > len(ERRORS)

    patterns = (
        ("matched", 0, 0),
        ("first_only", 1, 0),
        ("second_only", 0, 1),
        ("both_equal", 1, 1),
        ("both_opposite", 1, -1),
    )
    specs = tuple(
        (label, t, epsilon5, epsilon6)
        for t in range(PRIME)
        for label, epsilon5, epsilon6 in patterns
    )
    with mp.get_context("fork").Pool(processes=4) as pool:
        rows = tuple(pool.map(instance, specs, chunksize=1))

    histogram = sorted(Counter(row["conormal_gain"] for row in rows).items())
    payload = {
        "scope": (
            "smallest target-gated exact-g k0 chamber with two extra "
            "agreement Newton coordinates and two errors; finite exact gate, "
            "not a target theorem"
        ),
        "field": "F_11",
        "profile_n_w_g_m_B_s_U_L_k_n0": (
            PROFILE.n, PROFILE.w, PROFILE.agreements, PROFILE.m,
            PROFILE.B, PROFILE.s, PROFILE.U, PROFILE.L,
            PROFILE.k, PROFILE.n0,
        ),
        "source_columns_local_rank_global_cap_margin": (
            len(MONOMIALS), local_rank, global_cap,
            len(MONOMIALS) - global_cap,
        ),
        "target_gates": {
            "B_equals_2s": True,
            "U_minus_B_equals_m_plus_1": True,
            "terminal_width": terminal_width,
            "errors": len(ERRORS),
        },
        "normalization": {
            "agreement_newton_form": "Q=C(X,3)+t*C(X,4)",
            "first_extra_newton_coordinate": 1,
            "later_extra_newton_coordinate": "all t in F_11",
            "error_residuals": (1, 1),
            "error_mismatch_patterns": patterns,
            "boundary_specialization_X": BOUNDARY_X,
        },
        "cases": rows,
        "conormal_gain_histogram": histogram,
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    payload["runtime_receipt"] = {
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "peak_parent_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "peak_child_rss_kib": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))
    if histogram != [(4, len(rows))]:
        raise SystemExit("rank-four counterexample found")


if __name__ == "__main__":
    main()
