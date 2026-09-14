#!/usr/bin/env python3
"""Exact adversarial controls for the k=0 full-cutoff conormal claim.

This file deliberately uses the literal promoted second-jet source, rather
than the older asymmetric toy support.  Its principal chamber is the
minimal one-error/one-Newton-slot chamber found with all of the target-style
numerical gates enabled:

    (n,w,A,m,B,s,U,L,k,n0) = (5,2,4,4,2,1,7,7,0,1).

After the standard graph/seed/direction normalizations over F_7 there is one
high Newton discrepancy, one error residual and one error direction value.
We normalize the nonzero discrepancy to one and exhaust all 6*7 remaining
possibilities.  Function-field rank four is certified by a specialization
away from the domain; a specialization can only lower rank over F_7(X).

This is a finite falsifier, not the target theorem.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import asdict
from itertools import product
import hashlib
import json
import multiprocessing as mp
import resource
import sys
import time

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import secondjet_candidate_major_function_field_rank_gate_6900 as S  # noqa: E402
import prime_o2_conormal_threshold_falsifier as T  # noqa: E402
from higher_jet_literal_matrix import translated_column  # noqa: E402
from higher6810_secondjet_retarget_exact import relaxed_rank_bound  # noqa: E402


PRIME = 7
PROFILE = S.Profile(5, 2, 4, 4, 2, 1, 7, 7, 0, 1)
NODES = tuple(range(PROFILE.n))
AGREEMENT = tuple(range(PROFILE.agreements))
ERROR = PROFILE.n - 1
MONOMIALS = S.support(PROFILE)


def coefficient_count(profile: S.Profile) -> int:
    """Literal generalized version of the target coefficient formula."""
    p = profile
    answer = 0
    for sp in range(p.s + 1):
        for rp in range(max(p.B - 2 * sp, 0) + 1):
            budget = (p.m * p.agreements - (p.w - 2) * sp
                      - (p.w - 1) * rp)
            seed_width = p.L + 1 - sp - rp
            ycount = min(max(budget - 1, 0) // p.w + 1,
                         max(p.U + 1 - sp - rp, 0))
            answer += (
                ycount * budget * seed_width
                + p.w * ycount * (ycount - 1) * (2 * ycount - 1) // 6
                - (budget + p.w * seed_width)
                * ycount * (ycount - 1) // 2
            )
    return answer


def evaluate(coefficients: tuple[int, ...], x: int) -> int:
    return sum(c * pow(x, i, PRIME)
               for i, c in enumerate(coefficients)) % PRIME


def contact_matrix(delta: int, error_residual: int, error_direction: int):
    """Normalized selected graph f=0, gamma=0, h=delta*X(X-1)(X-2)/6."""
    # This is the Lagrange basis which is zero at 0,1,2 and one at 3.
    hbase = (0, 5, 3, 6)  # X(X-1)(X-2)/6 over F_7
    assert tuple(evaluate(hbase, x) for x in AGREEMENT) == (0, 0, 0, 1)
    u0 = (0, 0, 0, 0, error_residual)
    u1 = (0, 0, 0, delta, error_direction)
    columns = []
    for xp, yp, rp, sp, zp in MONOMIALS:
        column = {}
        for node in NODES:
            expansion = translated_column(
                xp, (yp, rp, sp), zp, node, u0[node], u1[node],
                PROFILE.m, 2, PRIME)
            for term, value in expansion.items():
                if value:
                    column[(node, term)] = value
        columns.append(column)
    return T.dense_matrix(columns)


def boundary_matrix(x: int):
    """Boundary gradient at the normalized zero graph and seed."""
    flat = []
    for coordinate in range(4):
        for xp, yp, rp, sp, zp in MONOMIALS:
            exponents = (yp, rp, sp, zp)
            flat.append(pow(x, xp, PRIME)
                        if exponents[coordinate] == 1
                        and sum(exponents) == 1 else 0)
    return nmod_mat(4, len(MONOMIALS), flat, PRIME)


def stack(left: nmod_mat, right: nmod_mat):
    assert left.ncols() == right.ncols()
    data = [int(left[i, j])
            for i in range(left.nrows()) for j in range(left.ncols())]
    data.extend(int(right[i, j])
                for i in range(right.nrows()) for j in range(right.ncols()))
    return nmod_mat(left.nrows() + right.nrows(), left.ncols(), data, PRIME)


def instance(spec: tuple[int, int, int]):
    delta, error_residual, error_direction = spec
    contact = contact_matrix(delta, error_residual, error_direction)
    contact_rank = contact.rank()
    ranks = tuple(stack(contact, boundary_matrix(x)).rank() - contact_rank
                  for x in (5, 6))
    return {
        "delta_errorResidual_errorDirection": spec,
        "contact_rows_rank_nullity": (
            contact.nrows(), contact_rank, len(MONOMIALS) - contact_rank),
        "conormal_ranks_at_X_5_6": ranks,
        "function_field_rank_lower_bound": max(ranks),
    }


def main() -> None:
    started = time.monotonic()
    S.PRIME = PRIME
    T.PRIME = PRIME

    columns = coefficient_count(PROFILE)
    local_rank = relaxed_rank_bound(
        PROFILE.m, PROFILE.L, PROFILE.B, PROFILE.s, PROFILE.U)
    margin = columns - PROFILE.n * local_rank
    assert columns == len(MONOMIALS) == 1276
    assert (local_rank, PROFILE.n * local_rank, margin) == (183, 915, 361)
    # Exact target-style support/terminal gates.
    assert PROFILE.B == 2 * PROFILE.s
    assert PROFILE.U - PROFILE.B == PROFILE.m + 1
    assert (PROFILE.m * PROFILE.agreements
            - PROFILE.w * (PROFILE.B + PROFILE.m + 1)) == 2
    assert PROFILE.n - PROFILE.agreements == 1 < 2
    assert ((PROFILE.m * PROFILE.agreements + PROFILE.B - 1)
            // PROFILE.w - PROFILE.U) == 1

    # delta=1 is the projective normalization of every bad direction class:
    # after subtracting a degree-two word on nodes 0,1,2, delta is the first
    # Newton discrepancy at node 3.  The remaining data is exhaustive.
    specs = tuple((1, residual, direction)
                  for residual in range(1, PRIME)
                  for direction in range(PRIME))
    context = mp.get_context("fork")
    with context.Pool(processes=4) as pool:
        rows = tuple(pool.map(instance, specs, chunksize=1))
    assert len(rows) == 42
    assert all(row["function_field_rank_lower_bound"] == 4 for row in rows)
    assert all(row["contact_rows_rank_nullity"] == (1055, 915, 361)
               for row in rows)

    # Exact good-direction boundary: delta=0 supplies a legal degree-two
    # tangent.  It must have rank at most three, and these controls attain 3.
    good_specs = tuple((0, residual, direction)
                       for residual, direction in ((1, 0), (1, 1), (2, 3)))
    good_rows = tuple(instance(spec) for spec in good_specs)
    assert all(row["function_field_rank_lower_bound"] == 3
               for row in good_rows)

    payload = {
        "field": "F_7(X)",
        "profile_n_w_A_m_B_s_U_L_k_n0": tuple(asdict(PROFILE).values()),
        "source_columns_localRank_nRank_margin": (
            columns, local_rank, PROFILE.n * local_rank, margin),
        "target_style_gates": {
            "B_equals_2s": True,
            "U_minus_B_equals_m_plus_1": True,
            "terminal_raw_width": 2,
            "errors": 1,
            "closed_cap_slack": 1,
            "strict_source_dimension": True,
        },
        "normalization": {
            "candidate_and_seed": "P=0, gamma=0",
            "agreement_nodes": AGREEMENT,
            "error_node": ERROR,
            "first_three_direction_values": (0, 0, 0),
            "first_Newton_discrepancy_at_node_3": 1,
            "error_residuals": "all F7^*",
            "error_direction_values": "all F7",
        },
        "bad_instances_exhausted": len(rows),
        "bad_rank_histogram": sorted(Counter(
            row["function_field_rank_lower_bound"] for row in rows).items()),
        "bad_rows": rows,
        "good_boundary_controls": good_rows,
        "verdict": (
            "No rank-defect counterexample in the complete normalized "
            "smallest target-gated chamber: all 42 bad instances have "
            "rank four over F7(X), while delta=0 controls have rank three."
        ),
        "scope": (
            "Exhaustive only after the stated normalizations and only in "
            "this finite chamber; it is not a proof of the target theorem."
        ),
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "peak_parent_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "peak_child_rss_kib": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
    }
    canonical = json.dumps({k: v for k, v in payload.items()
                            if k not in ("elapsed_seconds",
                                         "peak_parent_rss_kib",
                                         "peak_child_rss_kib")},
                           sort_keys=True, separators=(",", ":"))
    print(json.dumps(payload, sort_keys=True, indent=2))
    print("canonical_sha256=" + hashlib.sha256(canonical.encode()).hexdigest())


if __name__ == "__main__":
    main()
