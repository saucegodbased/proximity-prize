#!/usr/bin/env python3
"""One-shot corrected critical-cell gate in a second exact chamber.

This avoids a broad filtration scan.  In the nontrivial three-error profile
``(n,w,g,m,B,s,U,L)=(8,3,5,8,3,1,12,12)``, test exactly the family requested
by the literal quotient recurrence:

* raw {1,R};
* all raw S layers with Y degree below m;
* the first legal connector ``S Y^(m-1) R`` (all X/Z shifts);
* the complete critical two-cell packet ``Y^m S`` and ``Y^m S Z``.

The profile satisfies m=3B-1, has three errors, and B=3 is the first chamber
where the connector is legal.
"""

from __future__ import annotations

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
import k0_second_exact_chamber_critical_seed_gate_6900 as M8  # noqa: E402


K0 = Gate.K0
PROFILE = K0.Profile(8, 3, 5, 8, 3, 1, 12, 12, 0, 1)


def main():
    started = time.monotonic()
    profile = PROFILE
    receipt = M8.monomial_tangent_receipt(profile, 811, 0)
    complete = K0.support(profile)
    base = tuple(q for q in complete
                 if (q[2], q[3]) in {(0, 0), (1, 0)})
    subcritical = tuple(q for q in complete
                        if (q[2], q[3]) == (0, 1) and q[1] < profile.m)
    connector = tuple(q for q in complete
                      if (q[2], q[3], q[1]) == (1, 1, profile.m - 1))
    critical = tuple(q for q in complete
                     if (q[2], q[3], q[1]) == (0, 1, profile.m)
                     and q[4] <= 1)
    assert connector and critical
    monomials = base + subcritical + connector + critical
    contact = Shape.full_contact(profile, receipt, monomials)
    boundary = Shape.full_boundary(receipt, monomials, profile.n)
    result = Active.analyze(
        contact, boundary, monomials, tuple(range(len(monomials))))[
            "columns_contact_rank_kernel_boundary_gain"]
    payload = {
        "scope": "second exact-chamber corrected connector/two-cell gate",
        "field": "F_101",
        "profile_n_w_A_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "trial": 811,
        "agreement_set": receipt.agreement,
        "seed": receipt.seed,
        "candidate_and_tangent_degrees": (
            K0.poly_degree(receipt.polynomial),
            K0.poly_degree(receipt.tangent)),
        "family_column_counts": {
            "raw_1_R": len(base),
            "subcritical_S": len(subcritical),
            "connector_S_Y_m_minus_1_R": len(connector),
            "critical_Y_m_S_seed_0_1": len(critical),
        },
        "columns_contact_rank_kernel_boundary_gain": result,
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(
        canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    payload["runtime"] = {
        "seconds": round(time.monotonic() - started, 3),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
