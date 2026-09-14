#!/usr/bin/env python3
"""Second exact-chamber discriminator for the critical raw-S seed prefix.

The profile ``(n,w,g,m,B,s,U,L)=(7,3,5,8,3,1,12,12)`` has two errors and
the exact relation ``m=3B-1`` shared by the target.  Its prescribed agreement
tangent ``Q=X^(w+1)`` is bad/high but has constant anchor Newton quotient.
Only the focused raw {1,R}, subcritical-S, and critical ``Y^m S Z^z`` columns
are materialized.  This smaller exact chamber was selected after the larger
degree-0/1/2 discriminator exceeded the rapid-test budget during elimination.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

sys.path.insert(0, ".experiments")
import k0_target_ratio_constant_t_gate_6900 as Gate  # noqa: E402
import k0_target_ratio_raw_1rs_layer_gate_6900 as Shape  # noqa: E402
import k0_target_ratio_raw_s_active_filtration_6900 as Active  # noqa: E402


K0 = Gate.K0
P = Gate.P
PROFILE = K0.Profile(7, 3, 5, 8, 3, 1, 12, 12, 0, 1)


def monomial_tangent_receipt(profile, trial: int, quotient_degree: int):
    old = K0.make_receipt(profile, trial, "top_monomial")
    degree = profile.w + 1 + quotient_degree
    assert degree < profile.agreements
    prescribed = (0,) * degree + (1,)
    u1 = list(old.u1)
    u0 = list(old.u0)
    for x in old.agreement:
        u1[x] = K0.evaluate(prescribed, x)
        u0[x] = (K0.evaluate(old.polynomial, x) - old.seed * u1[x]) % P
    for x in old.nodes:
        if x not in old.agreement:
            forbidden = (K0.evaluate(old.polynomial, x) -
                         old.seed * u1[x]) % P
            if u0[x] == forbidden:
                u0[x] = (u0[x] + 1) % P
    tangent = K0.interpolate(tuple(u1[x] for x in old.agreement),
                             old.agreement)
    assert K0.poly_degree(tangent) == degree
    return K0.Receipt(old.nodes, old.agreement, old.seed, old.polynomial,
                      tuple(u0), tuple(u1), tangent)


def run(quotient_degree: int, precritical_only: bool = False):
    started = time.monotonic()
    profile = PROFILE
    receipt = monomial_tangent_receipt(
        profile, 800 + quotient_degree, quotient_degree)
    complete = K0.support(profile)
    base = tuple(q for q in complete if (q[2], q[3]) in {(0, 0), (1, 0)})
    subcritical = tuple(q for q in complete
                        if (q[2], q[3]) == (0, 1) and q[1] < profile.m)
    critical_bands = tuple(tuple(q for q in complete
                                 if (q[2], q[3], q[1], q[4]) ==
                                 (0, 1, profile.m, z))
                           for z in range(2))
    assert all(critical_bands)
    monomials = (base + subcritical if precritical_only else
                 base + subcritical + sum(critical_bands, ()))
    contact = Shape.full_contact(profile, receipt, monomials)
    boundary = Shape.full_boundary(receipt, monomials, profile.n)
    base_indices = tuple(range(len(base)))
    admitted = base_indices + tuple(range(
        len(base), len(base) + len(subcritical)))
    rows = []
    if precritical_only:
        rows.append({
            "maximum_critical_seed": -1,
            "columns_contact_rank_kernel_gain": Active.analyze(
                contact, boundary, monomials, admitted)[
                    "columns_contact_rank_kernel_boundary_gain"],
        })
    offset = len(base) + len(subcritical)
    for z, band in (() if precritical_only else enumerate(critical_bands)):
        admitted += tuple(range(offset, offset + len(band)))
        offset += len(band)
        result = Active.analyze(contact, boundary, monomials, admitted)[
            "columns_contact_rank_kernel_boundary_gain"]
        rows.append({
            "maximum_critical_seed": z,
            "new_band_width": len(band),
            "columns_contact_rank_kernel_gain": result,
        })
        if result[-1] == 4:
            break
    return {
        "profile_n_w_A_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "prescribed_anchor_quotient_degree": quotient_degree,
        "precritical_only": precritical_only,
        "trial": 800 + quotient_degree,
        "agreement_set": receipt.agreement,
        "seed": receipt.seed,
        "candidate_and_tangent_degrees": (
            K0.poly_degree(receipt.polynomial),
            K0.poly_degree(receipt.tangent)),
        "focused_columns_base_subcritical_critical_bands": (
            len(base), len(subcritical), tuple(map(len, critical_bands))),
        "filtration": tuple(rows),
        "runtime": {
            "seconds": round(time.monotonic() - started, 3),
            "peak_rss_kib": resource.getrusage(
                resource.RUSAGE_SELF).ru_maxrss,
        },
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--quotient-degree", type=int, choices=(0,),
                        required=True)
    parser.add_argument("--precritical-only", action="store_true")
    args = parser.parse_args()
    payload = {
        "scope": "second exact m=3B-1 chamber critical-seed gate",
        "field": "F_101",
        "case": run(args.quotient_degree, args.precritical_only),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(
        canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
