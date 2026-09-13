#!/usr/bin/env python3
"""Multiplicity stability test for the full 11-generator order-four module.

At one error node, form every weighted-order-four monomial in
Lambda,V,J1,J2, multiply it by V^(m-4), and give each coefficient three
local X-jets.  For finite passive-shift prefixes this script computes the
rank of the complete literal contact image.  It tests whether the rank-22
steady state observed at m=4 survives at larger multiplicity.

This is local raw-module algebra.  It deliberately makes no source-width,
lower-grade quotient, or distinguished-RHS claim.
"""

from __future__ import annotations

import hashlib
import json
import sys

sys.path.insert(0, ".experiments")
import f101_order4_eight_carrier_local_jet_block_6900 as E  # noqa: E402
import f101_order4_osculating_covariant_basis_gate_6900 as O  # noqa: E402
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402


P = 101
BASE_SEED = 3
FULL_ORDER4 = tuple(
    (a, v, c, d)
    for a in range(5)
    for v in range(5)
    for c in range(3)
    for d in range(2)
    if a + v + 2 * c + 3 * d == 4
)
assert len(FULL_ORDER4) == 11


def full_generators(literal):
    generators = O.make_generators(literal)
    return (generators["Lambda"], generators["V"],
            generators["J1"], generators["J2"])


def carrier(literal, m, exponents):
    a, v, c, d = exponents
    lam, centered_v, j1, j2 = full_generators(literal)
    return E.sparse_product((
        (lam, a),
        (centered_v, m - 4 + v),
        (j1, c),
        (j2, d),
        (F.Z, BASE_SEED + a + c + 2 * d),
    ))


def shift_contact(column, shift):
    return {
        (t, error, r, s, z + shift): coefficient
        for (t, error, r, s, z), coefficient in column.items()
    }


def one_multiplicity(literal, node, offset, delta, m, max_shifts=3):
    q_at_node = F.poly_eval(literal.q, node)
    direction = (q_at_node + offset) % P
    base_columns = []
    labels = []
    for jet in range(3):
        for exponents in FULL_ORDER4:
            source = carrier(literal, m, exponents)
            source = E.scale_by_poly(source, E.local_x_power(node, jet))
            base_columns.append(E.local_contact(
                source, node, delta, direction, m))
            labels.append((jet, exponents))
    assert len(base_columns) == 33

    ranks = []
    columns = []
    for shift in range(max_shifts):
        columns.extend(shift_contact(column, shift)
                       for column in base_columns)
        ranks.append(M.modular_rank_sparse(columns))
    increments = tuple(
        rank - (ranks[index - 1] if index else 0)
        for index, rank in enumerate(ranks))
    return {
        "m": m,
        "base_columns": len(base_columns),
        "shift_prefix_ranks": tuple(ranks),
        "rank_increments": increments,
        "base_contact_support_union": len({
            row for column in base_columns for row in column}),
        "base_column_support_range": (
            min(len(column) for column in base_columns),
            max(len(column) for column in base_columns)),
    }


def main():
    M.PRIME = M.T.PRIME = M.F.PRIME = F.PRIME = P
    literal = M.build_case(
        "full_order4_multiplicity_critic", E.CASE, 7, 7, 4,
        error_direction_offsets=E.OFFSETS)
    node, offset, delta = 7, E.OFFSETS[0], E.DELTAS[0]
    results_list = []
    for m in (4, 5, 6, 8):
        print(f"multiplicity {m}", file=sys.stderr, flush=True)
        result = one_multiplicity(literal, node, offset, delta, m)
        print(f"multiplicity {m} ranks {result['shift_prefix_ranks']}",
              file=sys.stderr, flush=True)
        results_list.append(result)
    results = tuple(results_list)
    assert results[0]["rank_increments"][:3] == (33, 32, 22)
    payload = {
        "scope": (
            "one-error raw complete-contact shift Hilbert ranks; no source "
            "width, lower-grade quotient, or RHS membership claim"
        ),
        "field": P,
        "node_offset_delta": (node, offset, delta),
        "coefficient_jets": 3,
        "weighted_order4_exponents_Lambda_V_J1_J2": FULL_ORDER4,
        "results": results,
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(
        canonical.encode()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
