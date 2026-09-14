#!/usr/bin/env python3
"""Low-memory exact shape-group attribution for the L=16 m8 K0 receipt.

The already-certified complete source has contact rank 17411 and boundary
gain four, while the selected low family is contact-injective.  This script
orders the remaining shapes as

    all low/base/S, then R^2, then R^3, then the omitted S*R shapes.

It tests the prefix ending at R^3 without rebuilding the 5.5-GiB complete
matrix.  Rows are restricted to one deterministic set of local coordinates:
the pivot coordinates of the node-zero full local transpose.  Full column
rank after a row restriction proves full column rank for the literal contact
matrix, so this is an exact certificate, not a probabilistic sketch.  If the
restriction loses rank, the result is explicitly inconclusive.
"""

from __future__ import annotations

from dataclasses import asdict
import gc
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import k0_second_exact_chamber_full_source_rank_gate_6900 as Full  # noqa: E402


K0 = Full.K0
P = Full.P
PROFILE = Full.PROFILE


def node_expansion(profile, receipt, monomial, node):
    xp, yp, rp, sp, zp = monomial
    return Full.Shape.translated_column(
        xp, (yp, rp, sp), zp, node, receipt.u0[node], receipt.u1[node],
        profile.m, 2, P)


def pivot_columns(matrix, rank):
    """Return the leading columns of a matrix already in RREF."""
    answer = []
    column = 0
    for row in range(rank):
        while column < matrix.ncols() and int(matrix[row, column]) % P == 0:
            column += 1
        assert column < matrix.ncols()
        answer.append(column)
        column += 1
    return tuple(answer)


def common_selected_terms(profile, receipt, complete):
    """Exact pivot-coordinate restriction from node zero's full local map."""
    node = receipt.nodes[0]
    terms_set = set()
    for j, monomial in enumerate(complete):
        terms_set.update(node_expansion(
            profile, receipt, monomial, node).keys())
        if (j + 1) % 2000 == 0:
            print(f"local row pass {j + 1}/{len(complete)}",
                  file=sys.stderr, flush=True)
    terms = tuple(sorted(terms_set, key=repr))
    # Transpose is built directly: its pivot columns are independent rows of
    # the untransposed local contact map.
    transpose = nmod_mat(len(complete), len(terms), P)
    term_index = {term: i for i, term in enumerate(terms)}
    for j, monomial in enumerate(complete):
        for term, value in node_expansion(
                profile, receipt, monomial, node).items():
            if value:
                transpose[j, term_index[term]] = value
        if (j + 1) % 2000 == 0:
            print(f"local fill {j + 1}/{len(complete)}",
                  file=sys.stderr, flush=True)
    print(f"local transpose {transpose.nrows()}x{transpose.ncols()}; rref",
          file=sys.stderr, flush=True)
    _, rank = transpose.rref(inplace=True)
    selected_indices = pivot_columns(transpose, rank)
    selected = tuple(terms[i] for i in selected_indices)
    del transpose
    gc.collect()
    return terms, selected, rank


def restricted_prefix_rank(profile, receipt, prefix, selected_terms):
    selected_set = set(selected_terms)
    row_index = {
        (node, term): i
        for i, (node, term) in enumerate(
            (pair for node in receipt.nodes for pair in
             ((node, term) for term in selected_terms)))
    }
    matrix = nmod_mat(len(row_index), len(prefix), P)
    for j, monomial in enumerate(prefix):
        for node in receipt.nodes:
            for term, value in node_expansion(
                    profile, receipt, monomial, node).items():
                if value and term in selected_set:
                    matrix[row_index[(node, term)], j] = value
        if (j + 1) % 1000 == 0:
            print(f"projected fill {j + 1}/{len(prefix)}",
                  file=sys.stderr, flush=True)
    print(f"projected prefix {matrix.nrows()}x{matrix.ncols()}; rref",
          file=sys.stderr, flush=True)
    _, rank = matrix.rref(inplace=True)
    return rank


def main():
    started = time.monotonic()
    profile = PROFILE
    receipt = Full.M8.monomial_tangent_receipt(profile, 811, 0)
    complete = K0.support(profile)

    selected_low = tuple(
        q for q in complete
        if (q[2], q[3]) in {(0, 0), (1, 0)}
        or ((q[2], q[3]) == (0, 1) and q[1] < profile.m)
        or (q[2], q[3], q[1]) == (1, 1, profile.m - 1)
        or ((q[2], q[3], q[1]) == (0, 1, profile.m) and q[4] <= 1))
    selected_set = set(selected_low)
    remaining_s = tuple(
        q for q in complete
        if (q[2], q[3]) == (0, 1) and q not in selected_set)
    r2 = tuple(q for q in complete if (q[2], q[3]) == (2, 0))
    r3 = tuple(q for q in complete if (q[2], q[3]) == (3, 0))
    remaining_sr = tuple(
        q for q in complete
        if (q[2], q[3]) == (1, 1) and q not in selected_set)
    groups = (selected_low, remaining_s, r2, r3, remaining_sr)
    assert tuple(map(len, groups)) == (9964, 258, 2640, 2195, 2622)
    assert len(set().union(*(set(group) for group in groups))) == len(complete)

    prefix_groups = groups[:-1]
    prefix = sum(prefix_groups, ())
    stage_sizes = []
    running = 0
    for group in prefix_groups:
        running += len(group)
        stage_sizes.append(running)
    assert tuple(stage_sizes) == (9964, 10222, 12862, 15057)

    all_terms, selected_terms, local_rank = common_selected_terms(
        profile, receipt, complete)
    projected_rank = restricted_prefix_rank(
        profile, receipt, prefix, selected_terms)
    prefix_is_injective = projected_rank == len(prefix)
    if prefix_is_injective:
        stage_contact_rank_nullity_gain = tuple(
            (size, size, 0, 0) for size in stage_sizes)
    else:
        stage_contact_rank_nullity_gain = None

    selected_terms_sha = hashlib.sha256(
        repr(selected_terms).encode()).hexdigest()
    payload = {
        "scope": "exact low-memory ordered shape attribution on m8 L16 receipt",
        "field": "F_101",
        "profile_n_w_A_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "trial": 811,
        "agreement_set": receipt.agreement,
        "group_order_and_counts": tuple(zip(
            ("selected_low", "remaining_S", "R2", "R3", "remaining_SR"),
            map(len, groups))),
        "all_local_terms_node0_rank_selected_terms": (
            len(all_terms), local_rank, len(selected_terms)),
        "selected_terms_sha256": selected_terms_sha,
        "projected_rows_columns_rank": (
            len(receipt.nodes) * len(selected_terms), len(prefix),
            projected_rank),
        "prefix_is_literally_contact_injective": prefix_is_injective,
        "stage_columns_contact_rank_nullity_boundary_gain_if_injective":
            stage_contact_rank_nullity_gain,
        "prior_complete_exact_columns_contact_rank_nullity_boundary_gain":
            (17679, 17411, 268, 4),
        "prior_complete_contact_and_augmented_canonical_sha256": (
            "3ebfbdb8b5583f4384e4bb1d862b96a440de9322b0329f71b736378d2c4cf8af",
            "4cc1465cab2e6c01795573d9969acba36ef585ecc1998835f2cd8188cb8e200f"),
        "logic": (
            "full column rank after literal row restriction implies full "
            "column rank before restriction; otherwise result is inconclusive"
        ),
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
