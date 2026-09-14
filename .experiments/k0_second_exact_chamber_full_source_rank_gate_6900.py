#!/usr/bin/env python3
"""Memory-bounded full-source rank/normal gate on the L=16 m8 receipt.

Run twice, once with ``--mode contact`` and once with ``--mode augmented``.
The difference between the augmented and contact ranks is exactly the boundary
image dimension of the contact kernel.  This avoids materializing a 17679^2
nullspace.  A two-pass fill discovers contact rows first and then regenerates
columns directly into one Flint matrix, keeping the process below 7.5 GB.
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

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import k0_target_ratio_constant_t_gate_6900 as Gate  # noqa: E402
import k0_target_ratio_raw_1rs_layer_gate_6900 as Shape  # noqa: E402
import k0_second_exact_chamber_critical_seed_gate_6900 as M8  # noqa: E402
from higher6810_secondjet_retarget_exact import relaxed_rank_bound  # noqa: E402


K0 = Gate.K0
P = Gate.P
PROFILE = K0.Profile(8, 3, 5, 8, 3, 1, 12, 16, 0, 1)


def expansions(profile, receipt, monomial):
    xp, yp, rp, sp, zp = monomial
    for node in receipt.nodes:
        for term, value in Shape.translated_column(
                xp, (yp, rp, sp), zp, node, receipt.u0[node],
                receipt.u1[node], profile.m, 2, P).items():
            if value:
                yield (node, term), value


def two_pass_matrix(profile, receipt, monomials, augmented: bool):
    rows_set = set()
    for j, monomial in enumerate(monomials):
        rows_set.update(row for row, _ in expansions(
            profile, receipt, monomial))
        if (j + 1) % 1000 == 0:
            print(f"row pass {j + 1}/{len(monomials)}", file=sys.stderr,
                  flush=True)
    rows = tuple(sorted(rows_set, key=repr))
    row_index = {row: i for i, row in enumerate(rows)}
    extra = 4 if augmented else 0
    matrix = nmod_mat(len(rows) + extra, len(monomials), P)
    for j, monomial in enumerate(monomials):
        for row, value in expansions(profile, receipt, monomial):
            matrix[row_index[row], j] = value
        if augmented:
            gradients = K0.monomial_gradient_polys(monomial, receipt)
            for coordinate in range(4):
                matrix[len(rows) + coordinate, j] = int(
                    gradients[coordinate](profile.n))
        if (j + 1) % 1000 == 0:
            print(f"fill pass {j + 1}/{len(monomials)}", file=sys.stderr,
                  flush=True)
    return matrix, len(rows)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("contact", "augmented"),
                        required=True)
    args = parser.parse_args()
    started = time.monotonic()
    profile = PROFILE
    receipt = M8.monomial_tangent_receipt(profile, 811, 0)
    monomials = K0.support(profile)
    local_bound = relaxed_rank_bound(
        profile.m, profile.L, profile.B, profile.s, profile.U)
    assert (len(monomials), local_bound,
            len(monomials) - profile.n * local_bound) == (17679, 2179, 247)
    matrix, contact_rows = two_pass_matrix(
        profile, receipt, monomials, args.mode == "augmented")
    print(f"{args.mode} matrix {matrix.nrows()}x{matrix.ncols()}; in-place rref",
          file=sys.stderr, flush=True)
    # `rank()` asks FLINT for a second elimination-sized allocation and the
    # 23720x17679 contact run exceeds 7.5 GB.  Destructive rref keeps the one
    # already-filled matrix and returns the same exact rank.
    _, rank = matrix.rref(inplace=True)
    payload = {
        "scope": "full-source contact/augmented rank on capacity-positive m8",
        "mode": args.mode,
        "field": "F_101",
        "profile_n_w_A_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "trial": 811,
        "agreement_set": receipt.agreement,
        "seed": receipt.seed,
        "candidate_and_tangent_degrees": (
            K0.poly_degree(receipt.polynomial),
            K0.poly_degree(receipt.tangent)),
        "full_source_columns_local_bound_margin": (
            len(monomials), local_bound,
            len(monomials) - profile.n * local_bound),
        "contact_rows_and_extra_boundary_rows": (
            contact_rows, 4 if args.mode == "augmented" else 0),
        "matrix_rank": rank,
        "contact_nullity_if_contact_mode": (
            len(monomials) - rank if args.mode == "contact" else None),
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
