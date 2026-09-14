#!/usr/bin/env python3
"""Capacity-positive second exact-chamber corrected-family gate.

This is the target-relevant correction to the negative-capacity L=12 receipt.
The profile ``(n,w,g,m,B,s,U,L)=(8,3,5,8,3,1,12,16)`` has full-source
margin +247 under the published local bound.  It tests one family only:
raw {1,R}, all subcritical S, the complete ``S Y^(m-1) R`` connector layer,
and the critical two-seed cell.

The contact matrix is filled sparsely into one Flint allocation, rather than
through a dense Python integer list, and the analysis avoids copying the
matrix before nullspace extraction.  This is necessary to remain below the
7.5 GB process cap at 9964 columns.
"""

from __future__ import annotations

from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import k0_target_ratio_constant_t_gate_6900 as Gate  # noqa: E402
import k0_target_ratio_raw_1rs_layer_gate_6900 as Shape  # noqa: E402
import k0_second_exact_chamber_critical_seed_gate_6900 as M8  # noqa: E402
from higher6810_secondjet_retarget_exact import relaxed_rank_bound  # noqa: E402


K0 = Gate.K0
P = Gate.P
PROFILE = K0.Profile(8, 3, 5, 8, 3, 1, 12, 16, 0, 1)


def low_memory_contact(profile, receipt, monomials):
    sparse = []
    row_set = set()
    for column_number, (xp, yp, rp, sp, zp) in enumerate(monomials):
        column = {}
        for node in receipt.nodes:
            expansion = Shape.translated_column(
                xp, (yp, rp, sp), zp, node, receipt.u0[node],
                receipt.u1[node], profile.m, 2, P)
            for term, value in expansion.items():
                if value:
                    row = (node, term)
                    column[row] = value
                    row_set.add(row)
        sparse.append(column)
        if (column_number + 1) % 1000 == 0:
            print(f"expanded {column_number + 1}/{len(monomials)} columns",
                  file=sys.stderr, flush=True)
    rows = tuple(sorted(row_set, key=repr))
    row_index = {row: i for i, row in enumerate(rows)}
    matrix = nmod_mat(len(rows), len(monomials), P)
    for j, column in enumerate(sparse):
        for row, value in column.items():
            matrix[row_index[row], j] = value
        if (j + 1) % 1000 == 0:
            print(f"filled {j + 1}/{len(monomials)} columns",
                  file=sys.stderr, flush=True)
    sparse.clear()
    return matrix


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
    monomials = base + subcritical + connector + critical
    assert tuple(map(len, (base, subcritical, connector, critical))) == (
        6830, 2976, 128, 30)
    local_bound = relaxed_rank_bound(
        profile.m, profile.L, profile.B, profile.s, profile.U)
    full_margin = len(complete) - profile.n * local_bound
    assert (len(complete), local_bound, full_margin) == (17679, 2179, 247)

    contact = low_memory_contact(profile, receipt, monomials)
    print(f"matrix {contact.nrows()}x{contact.ncols()}; rank-first gate",
          file=sys.stderr, flush=True)
    contact_rank = contact.rank()
    nullity = len(monomials) - contact_rank
    if nullity:
        print(f"nullity {nullity}; extracting boundary image",
              file=sys.stderr, flush=True)
        kernel, checked_nullity = contact.nullspace()
        assert checked_nullity == nullity
        boundary = Shape.full_boundary(receipt, monomials, profile.n)
        gain = (boundary * kernel).rank()
    else:
        gain = 0
    payload = {
        "scope": "capacity-positive second exact-chamber corrected family",
        "field": "F_101",
        "profile_n_w_A_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "trial": 811,
        "agreement_set": receipt.agreement,
        "seed": receipt.seed,
        "candidate_and_tangent_degrees": (
            K0.poly_degree(receipt.polynomial),
            K0.poly_degree(receipt.tangent)),
        "full_source_columns_local_bound_margin": (
            len(complete), local_bound, full_margin),
        "family_column_counts": tuple(map(
            len, (base, subcritical, connector, critical))),
        "contact_rows": contact.nrows(),
        "columns_contact_rank_kernel_boundary_gain": (
            len(monomials), contact_rank, nullity, gain),
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
