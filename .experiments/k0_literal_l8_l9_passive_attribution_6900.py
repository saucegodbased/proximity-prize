#!/usr/bin/env python3
"""Attribute the literal formal L8 -> L9 passive repair by derivative shape.

The corrected m6 control has complete boundary gain three at L8 and four at
L9.  Every newly legal L9 column has positive Z power.  Order those columns
after the complete L8 source as raw, R, S, and R^2 shapes, and obtain every
nested prefix rank from one exact contact RREF and one exact augmented RREF.

This is a finite mechanism discriminator, not a target-uniform theorem.
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
    column, formal_gradient_vector,
)
from k0_centered_head_y_correction_gate_6900 import P  # noqa: E402


FOUR_GIB = 4 * 1024**3
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
if soft < 0 or soft > FOUR_GIB:
    resource.setrlimit(resource.RLIMIT_AS, (FOUR_GIB, hard))


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
    return rank, Layer.pivot_columns(matrix, rank)


def main():
    started = time.monotonic()
    base_profile = Old.K0.Profile(11, 5, 8, 6, 2, 1, 8, 8, 0, 1)
    next_profile = Old.K0.Profile(11, 5, 8, 6, 2, 1, 8, 9, 0, 1)
    receipt = Old.make_custom_receipt(
        base_profile, P, 0, "random", "mid", "minimal", "arbitrary",
        "alternating", 2)
    base = tuple(Old.K0.support(base_profile))
    base_set = set(base)
    added = tuple(q for q in Old.K0.support(next_profile)
                  if q not in base_set)
    group_specs = (
        ("new_raw", (0, 0)),
        ("new_R1", (1, 0)),
        ("new_S1", (0, 1)),
        ("new_R2", (2, 0)),
    )
    groups = tuple(
        tuple(q for q in added if (q[2], q[3]) == shape)
        for _name, shape in group_specs)
    assert Counter((q[2], q[3]) for q in added) == Counter({
        (0, 0): 252, (1, 0): 212, (0, 1): 220, (2, 0): 175,
    })
    assert all(q[4] > 0 for q in added)
    monomials = base + sum(groups, ())
    assert len(monomials) == 5623

    columns = []
    rows_set = set()
    for index, monomial in enumerate(monomials, start=1):
        contact = column(next_profile, receipt, monomial, False)
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
    end = len(base)
    admitted = ["L8_base"]
    boundaries = (("L8_base", len(base)),) + tuple(
        (name, len(group)) for (name, _shape), group in zip(group_specs, groups))
    end = 0
    for name, count in boundaries:
        admitted.append(name) if name != "L8_base" else None
        end += count
        c_rank = sum(pivot < end for pivot in contact_pivot_set)
        a_rank = sum(pivot < end for pivot in augmented_pivot_set)
        stages.append({
            "new_group": name,
            "admitted_groups": tuple(admitted),
            "columns_contact_rank_nullity_augmented_rank_boundary_gain": (
                end, c_rank, end - c_rank, a_rank, a_rank - c_rank),
        })

    assert (contact_rank, augmented_rank) == (5445, 5449)
    assert tuple(stages[0][
        "columns_contact_rank_nullity_augmented_rank_boundary_gain"]
                 [1:]) == (4719, 45, 4722, 3)
    stable = {
        "scope": "literal formal L8-to-L9 positive-Z layer attribution",
        "field": P,
        "base_profile_n_w_g_m_B_s_U_L_k_n0":
            tuple(asdict(base_profile).values()),
        "next_profile_n_w_g_m_B_s_U_L_k_n0":
            tuple(asdict(next_profile).values()),
        "agreement_set": receipt.agreement,
        "candidate_and_tangent_degrees": (
            Old.degree(receipt.polynomial, P),
            Old.degree(receipt.tangent, P)),
        "contact_semantics": (
            "formal rows (eps,S,T,R,Z); "
            "Y=u0+u1Z+epsR-eps^2S+eps^3T mod eps^m"),
        "boundary_semantics": (
            "formal graph point (Y,R,S,Z)=(P,P',Hasse2(P),gamma)"),
        "all_added_columns_have_positive_Z_power": True,
        "ordered_new_groups_and_counts": tuple(
            (name, shape, len(group))
            for (name, shape), group in zip(group_specs, groups)),
        "rows_columns_contact_augmented_ranks": (
            len(rows), len(monomials), contact_rank, augmented_rank),
        "nested_stages": tuple(stages),
        "scope_guard": (
            "prefix attribution depends on the declared group order; exact "
            "finite discriminator only, not target-uniform minimality"),
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
