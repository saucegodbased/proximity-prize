#!/usr/bin/env python3
"""Attribute the first literal complete k0 kernel/boundary gain by R/S shape.

On the corrected F_101 m6, L8 receipt, order the exact formal raw source as

    raw (R=S=0), R^1, S^1, R^2.

One contact RREF and one contact-plus-boundary RREF give every nested prefix
rank by counting pivot columns.  This identifies the first derivative family
needed for any complete-map kernel and measures its boundary image without
extracting a basis-dependent dense relation.  It is a finite discriminator,
not a target theorem.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import k0_capacity_positive_layer_attribution_6900 as Layer  # noqa: E402
import k0_first_positive_passive_universal_falsifier_6900 as Old  # noqa: E402
from k0_literal_flat_strong_cap_probe_6900 import (  # noqa: E402
    formal_gradient_vector,
)
from k0_centered_head_y_correction_gate_6900 import (  # noqa: E402
    P, flattened_raw_column,
)


FOUR_GIB = 4 * 1024**3
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
if soft < 0 or soft > FOUR_GIB:
    resource.setrlimit(resource.RLIMIT_AS, (FOUR_GIB, hard))


def literal_column(profile, receipt, monomial):
    answer = {}
    for node in receipt.nodes:
        for local, coefficient in flattened_raw_column(
                monomial, node, receipt.u0[node], receipt.u1[node],
                profile.m).items():
            answer[(node, local)] = coefficient
    return answer


def rank_and_pivots(columns, rows, monomials, receipt, boundary):
    row_index = {row: i for i, row in enumerate(rows)}
    matrix = nmod_mat(len(rows) + (4 if boundary else 0),
                      len(monomials), P)
    for j, contact in enumerate(columns):
        for row, coefficient in contact.items():
            matrix[row_index[row], j] = coefficient
        if boundary:
            gradient = formal_gradient_vector(monomials[j], receipt, 11)
            for coordinate, coefficient in enumerate(gradient):
                matrix[len(rows) + coordinate, j] = coefficient
    print(
        f"{'augmented' if boundary else 'contact'} matrix "
        f"{matrix.nrows()}x{matrix.ncols()}",
        file=sys.stderr, flush=True)
    _, rank = matrix.rref(inplace=True)
    pivots = Layer.pivot_columns(matrix, rank)
    return rank, pivots


def main():
    started = time.monotonic()
    profile = Old.K0.Profile(11, 5, 8, 6, 2, 1, 8, 8, 0, 1)
    receipt = Old.make_custom_receipt(
        profile, P, 0, "random", "mid", "minimal", "arbitrary",
        "alternating", 2)
    source = Old.K0.support(profile)
    group_specs = (
        ("raw", (0, 0)),
        ("R1", (1, 0)),
        ("S1", (0, 1)),
        ("R2", (2, 0)),
    )
    grouped = tuple(
        tuple(q for q in source if (q[2], q[3]) == shape)
        for _name, shape in group_specs)
    assert sum(map(len, grouped)) == len(source)
    monomials = sum(grouped, ())
    assert Counter((q[2], q[3]) for q in source) == Counter({
        (0, 0): 1560, (1, 0): 1164, (0, 1): 1200, (2, 0): 840,
    })
    columns = []
    rows_set = set()
    for index, monomial in enumerate(monomials, start=1):
        contact = literal_column(profile, receipt, monomial)
        columns.append(contact)
        rows_set.update(contact)
        if index % 1000 == 0:
            print(f"columns {index}/{len(monomials)}",
                  file=sys.stderr, flush=True)
    rows = tuple(sorted(rows_set, key=repr))
    contact_rank, contact_pivots = rank_and_pivots(
        columns, rows, monomials, receipt, False)
    augmented_rank, augmented_pivots = rank_and_pivots(
        columns, rows, monomials, receipt, True)
    contact_pivot_set = set(contact_pivots)
    augmented_pivot_set = set(augmented_pivots)
    stages = []
    end = 0
    admitted = []
    for (name, shape), group in zip(group_specs, grouped):
        admitted.append(name)
        end += len(group)
        c_rank = sum(column < end for column in contact_pivot_set)
        a_rank = sum(column < end for column in augmented_pivot_set)
        stages.append({
            "new_group_and_shape": (name, shape),
            "admitted_groups": tuple(admitted),
            "columns_contact_rank_nullity_augmented_rank_boundary_gain": (
                end, c_rank, end - c_rank, a_rank, a_rank - c_rank),
        })
    assert (contact_rank, augmented_rank) == (4719, 4722)
    stable = {
        "scope": "literal flattened complete-contact derivative-family attribution",
        "field": P,
        "profile_n_w_g_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "agreement_set": receipt.agreement,
        "candidate_and_tangent_degrees": (
            Old.degree(receipt.polynomial, P),
            Old.degree(receipt.tangent, P)),
        "contact_semantics": (
            "formal rows (eps,S,T,R,Z); "
            "Y=u0+u1Z+epsR-eps^2S+eps^3T mod eps^m"),
        "boundary_semantics": (
            "formal graph point (Y,R,S,Z)=(P,P',Hasse2(P),gamma)"),
        "group_order": tuple(group_specs),
        "full_rows_columns_contact_augmented_ranks": (
            len(rows), len(monomials), contact_rank, augmented_rank),
        "nested_stages": tuple(stages),
        "scope_guard": (
            "prefix ranks depend on the declared family order; exact finite "
            "attribution only, not target-uniform minimality"),
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
