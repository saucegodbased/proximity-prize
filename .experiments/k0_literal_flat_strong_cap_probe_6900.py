#!/usr/bin/env python3
"""Literal flattened-contact replay of the strongest old cap defect.

Unlike the superseded `translated_column(k=2)` receipts, this probe uses the
formal k0 substitution with rows `(eps,S,T,R,Z)` and

    Y = u0 + u1*Z + eps*R - eps^2*S + eps^3*T  (mod eps^m).

For the frozen F_101 m6 receipt it compares complete and eps>=3 head contact
ranks, with and without the four boundary rows, at passive caps 7,8,9.  Rank
differences are exact.  This remains a finite discriminator, not a target
theorem.
"""

from __future__ import annotations

from dataclasses import asdict, replace
import argparse
import gc
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import k0_first_positive_passive_universal_falsifier_6900 as Old  # noqa: E402
from k0_centered_head_y_correction_gate_6900 import (  # noqa: E402
    P, flattened_raw_column,
)


FOUR_GIB = 4 * 1024**3
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
if soft < 0 or soft > FOUR_GIB:
    resource.setrlimit(resource.RLIMIT_AS, (FOUR_GIB, hard))


def column(profile, receipt, monomial, head_only):
    answer = {}
    for node in receipt.nodes:
        for local, coefficient in flattened_raw_column(
                monomial, node, receipt.u0[node], receipt.u1[node],
                profile.m).items():
            if not head_only or local[0] >= 3:
                answer[(node, local)] = coefficient
    return answer


def run(profile, receipt, head_only):
    monomials = Old.K0.support(profile)
    columns = []
    rows_set = set()
    for index, monomial in enumerate(monomials, start=1):
        contact = column(profile, receipt, monomial, head_only)
        columns.append(contact)
        rows_set.update(contact)
        if index % 1000 == 0:
            print(
                f"L{profile.L} {'head' if head_only else 'full'} columns "
                f"{index}/{len(monomials)}",
                file=sys.stderr, flush=True)
    rows = tuple(sorted(rows_set, key=repr))
    row_index = {row: i for i, row in enumerate(rows)}

    def exact_rank(augmented):
        matrix = nmod_mat(len(rows) + (4 if augmented else 0),
                          len(monomials), P)
        for j, contact in enumerate(columns):
            for row, coefficient in contact.items():
                matrix[row_index[row], j] = coefficient
            if augmented:
                gradient = Old.gradient_vector(
                    monomials[j], receipt, profile.n, P)
                for coordinate, coefficient in enumerate(gradient):
                    matrix[len(rows) + coordinate, j] = coefficient
        print(
            f"L{profile.L} {'head' if head_only else 'full'} "
            f"{'augmented' if augmented else 'contact'} "
            f"matrix {matrix.nrows()}x{matrix.ncols()}",
            file=sys.stderr, flush=True)
        _, rank = matrix.rref(inplace=True)
        del matrix
        gc.collect()
        return rank

    contact_rank = exact_rank(False)
    augmented_rank = exact_rank(True)
    return {
        "projection": "eps>=3" if head_only else "complete eps< m",
        "literal_rows": len(rows),
        "columns_contact_rank_augmented_rank_boundary_gain": (
            len(monomials), contact_rank, augmented_rank,
            augmented_rank - contact_rank),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--caps", type=int, nargs="+", default=(8, 9))
    parser.add_argument("--projection", choices=("full", "head", "both"),
                        default="both")
    args = parser.parse_args()
    started = time.monotonic()
    base = Old.K0.Profile(11, 5, 8, 6, 2, 1, 8, 8, 0, 1)
    receipt = Old.make_custom_receipt(
        base, P, 0, "random", "mid", "minimal", "arbitrary",
        "alternating", 2)
    results = []
    for passive_cap in args.caps:
        profile = replace(base, L=passive_cap)
        print(f"literal cap L={passive_cap}", file=sys.stderr, flush=True)
        row = {
            "profile_n_w_g_m_B_s_U_L_k_n0":
                tuple(asdict(profile).values()),
        }
        if args.projection in ("full", "both"):
            row["complete"] = run(profile, receipt, False)
        if args.projection in ("head", "both"):
            row["head"] = run(profile, receipt, True)
        results.append(row)
    stable = {
        "scope": "literal flattened-contact strong-cap replay",
        "field": P,
        "agreement_set": receipt.agreement,
        "candidate_and_tangent_degrees": (
            Old.degree(receipt.polynomial, P),
            Old.degree(receipt.tangent, P)),
        "contact_semantics": (
            "rows (eps,S,T,R,Z), no E; "
            "Y=u0+u1Z+epsR-eps^2S+eps^3T mod eps^m"),
        "results": results,
        "scope_guard": "finite exact discriminator; not a target-uniform theorem",
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    payload = {
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "runtime": {
            "seconds": round(time.monotonic() - started, 3),
            "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            "external_memory_cap_bytes": FOUR_GIB,
        },
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
