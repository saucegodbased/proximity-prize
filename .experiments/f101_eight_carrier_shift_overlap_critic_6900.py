#!/usr/bin/env python3
"""Adversarial overlap test for shifted eight-carrier local states.

The one-layer 24x24 unit block uses rows whose passive seeds depend on the
carrier order h=a+c.  After a Z shift those physical rows overlap rows of
other carriers in adjacent layers.  This script compares the rank seen by
the proposed selected rows with the rank of the complete one-node contact
image for one through four simultaneous layers.

This is a local architecture discriminator only.  It does not make any
Full187 source or quotient claim.
"""

from __future__ import annotations

import hashlib
import json
import sys

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import f101_order4_eight_carrier_local_jet_block_6900 as E  # noqa: E402
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402


P = E.P


def shift_z(source, shift):
    return {
        (x, y, r, s, z + shift): coefficient
        for (x, y, r, s, z), coefficient in source.items()
    }


def dense(columns, rows):
    return nmod_mat(len(rows), len(columns), [
        column.get(row, 0)
        for row in rows for column in columns
    ], P)


def combine(columns, coefficients):
    out = {}
    for column, coefficient in zip(columns, coefficients):
        coefficient = int(coefficient) % P
        if not coefficient:
            continue
        for row, value in column.items():
            updated = (out.get(row, 0) + coefficient * value) % P
            if updated:
                out[row] = updated
            else:
                out.pop(row, None)
    return out


def one_prefix(literal, node, offset, delta, layer_count, jet_layers=3):
    m = E.CASE[3]
    b = E.CASE[7] + 1 - m
    q_at_node = F.poly_eval(literal.q, node)
    received_direction = (q_at_node + offset) % P

    columns = []
    labels = []
    selected_rows = set()
    for layer in range(layer_count):
        for jet in range(jet_layers):
            for a, c in E.PAIRS:
                source = E.carrier(literal, a, c)
                source = shift_z(source, layer)
                source = E.scale_by_poly(
                    source, E.local_x_power(node, jet))
                columns.append(E.local_contact(
                    source, node, delta, received_direction, m))
                labels.append((layer, jet, a, c))
                selected_rows.add((jet, 0, c, 0, b + a + c + layer))

    selected_rows = tuple(sorted(selected_rows))
    complete_rows = tuple(sorted({row for column in columns for row in column}))
    selected_matrix = dense(columns, selected_rows)
    complete_matrix = dense(columns, complete_rows)
    selected_rank = selected_matrix.rank()
    complete_rank = complete_matrix.rank()

    # Exhibit one selected-invisible vector with nonzero complete image when
    # the complete rank is larger.  Search the selected nullspace basis.
    witness = None
    kernel, nullity = selected_matrix.nullspace()
    for basis_column in range(nullity):
        coefficients = tuple(kernel[row, basis_column]
                             for row in range(len(columns)))
        leakage = combine(columns, coefficients)
        if leakage:
            assert not combine(
                [{row: column.get(row, 0) for row in selected_rows
                  if column.get(row, 0)} for column in columns],
                coefficients)
            witness = {
                "nonzero_input_terms": tuple(
                    (labels[index], int(value) % P)
                    for index, value in enumerate(coefficients)
                    if int(value) % P),
                "complete_leakage_support": len(leakage),
                "minimum_maximum_leakage_seed": (
                    min(row[-1] for row in leakage),
                    max(row[-1] for row in leakage)),
                "first_leakage_rows": tuple(sorted(leakage.items())[:12]),
            }
            break
    assert (complete_rank > selected_rank) == (witness is not None)
    return {
        "layers": layer_count,
        "columns": len(columns),
        "distinct_selected_rows": len(selected_rows),
        "selected_rank": selected_rank,
        "complete_contact_rows": len(complete_rows),
        "complete_contact_rank": complete_rank,
        "selected_kernel_dimension": len(columns) - selected_rank,
        "complete_kernel_dimension": len(columns) - complete_rank,
        "selected_invisible_complete_visible_witness": witness,
    }


def main():
    M.T.PRIME = M.F.PRIME = F.PRIME = P
    literal = M.build_case(
        "eight_carrier_shift_overlap", E.CASE, 7, 7, 4,
        error_direction_offsets=E.OFFSETS)
    nodes = []
    for node, offset, delta in zip(
            range(7, 10), E.OFFSETS, E.DELTAS):
        results = tuple(one_prefix(
            literal, node, offset, delta, layers)
            for layers in range(1, 5))
        assert results[0]["columns"] == results[0]["selected_rank"] == 24
        assert all(result["complete_contact_rank"] >= result["selected_rank"]
                   for result in results)
        assert all(result["complete_contact_rank"] > result["selected_rank"]
                   for result in results[1:])
        nodes.append({
            "node_offset_delta": (node, offset, delta),
            "prefixes": results,
        })
    payload = {
        "scope": "local shifted-state overlap critic; not a target proof",
        "field": P,
        "case": E.CASE,
        "carrier_pairs": E.PAIRS,
        "jet_layers": 3,
        "nodes": tuple(nodes),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(
        canonical.encode()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
