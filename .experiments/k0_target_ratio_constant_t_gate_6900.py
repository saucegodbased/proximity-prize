#!/usr/bin/env python3
"""Deterministic target-ratio constant-T controls for exact-G k=0.

The exact ratio chamber has ``m=3*B-1, s=B/2, U=4*B`` with ``B=2``;
the ceiling chamber uses ``m=6``.  Both use ``(n,w,g)=(11,5,8)`` and
``Q=C(X,6)``, so every size-six anchor has constant nonzero Newton quotient.
All three errors have the same nonzero value residual and direction mismatch.
This is a bounded falsifier/mechanism receipt, not a target theorem.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import resource
import sys
import time

sys.path.insert(0, ".experiments")
import secondjet_candidate_major_function_field_rank_gate_6900 as K0  # noqa: E402
from higher6810_secondjet_retarget_exact import relaxed_rank_bound  # noqa: E402


P = K0.PRIME
EXACT = K0.Profile(11, 5, 8, 5, 2, 1, 8, 8, 0, 1)
CEILING = K0.Profile(11, 5, 8, 6, 2, 1, 8, 8, 0, 1)


def mul(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    answer = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            answer[i + j] = (answer[i + j] + a * b) % P
    return tuple(answer)


def evaluate(poly: tuple[int, ...], x: int) -> int:
    return sum(a * pow(x, i, P) for i, a in enumerate(poly)) % P


def constant_t_polynomial() -> tuple[int, ...]:
    answer = (1,)
    for x in range(6):
        answer = mul(answer, ((-x) % P, 1))
    inverse_factorial = pow(720, -1, P)
    return tuple(inverse_factorial * a % P for a in answer)


def constant_t_receipt(profile: K0.Profile) -> K0.Receipt:
    assert (profile.n, profile.w, profile.agreements) == (11, 5, 8)
    q = constant_t_polynomial()
    u0 = tuple(0 if x < 8 else 1 for x in range(11))
    u1 = tuple(
        evaluate(q, x) if x < 8 else (evaluate(q, x) + 3) % P
        for x in range(11)
    )
    return K0.Receipt(
        tuple(range(11)), tuple(range(8)), 0, (0,), u0, u1, q)


def run_profile(profile: K0.Profile) -> dict[str, object]:
    receipt = constant_t_receipt(profile)
    monomials = K0.support(profile)
    rows, rank, kernel, nullity = K0.contact_kernel(
        profile, receipt, monomials)
    gradient_ranks = tuple(
        (x, K0.gradient_rank_at(
            profile, receipt, monomials, kernel, nullity, x)[0])
        for x in range(11, 14)
    )
    _, tangent_pairings = K0.tangent_relation(
        profile, receipt, monomials, kernel, nullity)
    local_bound = relaxed_rank_bound(
        profile.m, profile.L, profile.B, profile.s, profile.U)
    return {
        "profile_n_w_g_m_B_s_U_L_k_n0": tuple(profile.__dict__.values()),
        "columns_contact_rows_rank_nullity":
            (len(monomials), rows, rank, nullity),
        "published_local_rank_and_source_margin":
            (local_bound, len(monomials) - profile.n * local_bound),
        "gradient_ranks_at_boundary_X": gradient_ranks,
        "nonzero_true_tangent_pairings": tangent_pairings,
    }


def main() -> None:
    started = time.monotonic()
    cases = (run_profile(EXACT), run_profile(CEILING))
    assert tuple(case["published_local_rank_and_source_margin"]
                 for case in cases) == ((313, 161), (429, 45))
    assert tuple(case["columns_contact_rows_rank_nullity"]
                 for case in cases) == (
        (3604, 4191, 3418, 186),
        (4764, 5995, 4635, 129),
    )
    assert all(
        tuple(rank for _, rank in case["gradient_ranks_at_boundary_X"])
        == (4, 4, 4)
        for case in cases
    )
    payload: dict[str, object] = {
        "scope": (
            "two deterministic target-ratio constant-T/equal-mismatch "
            "controls; finite mechanism test, not target transport"
        ),
        "field": "F_101",
        "Q": constant_t_polynomial(),
        "Q_degree": 6,
        "anchor_size": 6,
        "errors_delta_epsilon": ((1, 3), (1, 3), (1, 3)),
        "cases": cases,
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    payload["runtime"] = {
        "seconds": round(time.monotonic() - started, 3),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
