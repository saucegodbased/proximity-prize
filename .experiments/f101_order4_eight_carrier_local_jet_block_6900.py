#!/usr/bin/env python3
"""Local three-jet block for the eight order-four terminal covariants.

For (a,c) in

  (0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),

put

  K[a,c] = p[a,c] Lambda^a V^(m-a-2c) J1^c Z^(b+a+c).

At an error root, order the pairs by h=a+c and then by decreasing c.
The selected local row for K[a,c] is R^c Z^(b+h).  This script checks on
the literal F101 order-four chart, with nonzero arbitrary direction offsets,
that the resulting eight-by-eight value block is lower triangular with
diagonal Lambda^(a+c) delta^(m-a-2c).  Replacing p by (X-alpha)^j for
j=0,1,2 gives a 24-by-24 lower-triangular three-Hasse-layer block with the
same diagonal repeated three times.

This is a local unit receipt.  It also records an important scale
distinction.  The sharp tiny-F101 representations have bounds
deg p[a,c] <= 3e-1-a-c and therefore 24e-16 parameters.  This is not a
target obstruction: the independently checked Full187 widths allow the
uniform bound deg p[a,c] < 3e for all eight families, giving exactly 24e
parameters and hence ordinary three-jet Hermite interpolation at all errors.
"""

from __future__ import annotations

from math import comb
import hashlib
import json
import sys

from flint import nmod_mat, nmod_poly

sys.path.insert(0, ".experiments")
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402
from higher_jet_literal_matrix import translated_column  # noqa: E402


P = 101
CASE = (10, 4, 7, 4, 28, 1, 1, 6, 10)
PAIRS = ((0, 0), (0, 1), (1, 0), (1, 1),
         (2, 0), (2, 1), (3, 0), (4, 0))
OFFSETS = (3, 5, 7)
DELTAS = (1, 9, 17)


def sparse_product(factors):
    out = F.sparse_constant(1)
    for factor, exponent in factors:
        out = F.sparse_mul(out, F.sparse_pow(factor, exponent))
    return out


def generators(literal):
    q1 = F.poly_derivative(literal.q)
    l1 = F.poly_derivative(literal.locator)
    v = F.sparse_add(
        F.Y, F.sparse_mul(F.Z, F.sparse_embed_x(literal.q)), -1)
    v1 = F.sparse_add(
        F.R, F.sparse_mul(F.Z, F.sparse_embed_x(q1)), -1)
    j1 = F.sparse_add(
        F.sparse_mul(F.sparse_embed_x(literal.locator), v1),
        F.sparse_mul(F.sparse_embed_x(l1), v), -1)
    return v, j1


def carrier(literal, a, c):
    m = CASE[3]
    b = CASE[7] + 1 - m
    v, j1 = generators(literal)
    return sparse_product((
        (F.sparse_embed_x(literal.locator), a),
        (v, m - a - 2 * c),
        (j1, c),
        (F.Z, b + a + c),
    ))


def local_x_power(alpha, exponent):
    """Ascending coefficients of (X-alpha)^exponent over F101."""
    return tuple(
        comb(exponent, degree)
        * pow(-alpha % P, exponent - degree, P) % P
        for degree in range(exponent + 1))


def local_contact(source, node, delta, received_direction, m):
    image = {}
    for (xp, yp, rp, sp, zp), coefficient in source.items():
        translated = translated_column(
            xp, (yp, rp, sp), zp, node, delta, received_direction,
            m, 2, P)
        for row, value in translated.items():
            updated = (image.get(row, 0) + coefficient * value) % P
            if updated:
                image[row] = updated
            else:
                image.pop(row, None)
    return image


def scale_by_poly(source, polynomial):
    return F.sparse_mul(F.sparse_embed_x(polynomial), source)


def one_node(literal, node, offset, delta, jet_layers=3):
    m = CASE[3]
    b = CASE[7] + 1 - m
    lam = F.poly_eval(literal.locator, node)
    q_at_node = F.poly_eval(literal.q, node)
    assert q_at_node == 0
    assert lam and delta
    received_direction = (q_at_node + offset) % P

    rows = []
    columns = []
    labels = []
    for jet in range(jet_layers):
        for a, c in PAIRS:
            rows.append((jet, 0, c, 0, b + a + c))
            source = carrier(literal, a, c)
            source = scale_by_poly(source, local_x_power(node, jet))
            columns.append(local_contact(
                source, node, delta, received_direction, m))
            labels.append((jet, a, c))

    matrix = nmod_mat(len(rows), len(columns), [
        column.get(row, 0)
        for row in rows for column in columns
    ], P)
    diagonal = []
    for index, (jet, a, c) in enumerate(labels):
        expected = (pow(lam, a + c, P)
                    * pow(delta, m - a - 2 * c, P)) % P
        actual = int(matrix[index, index]) % P
        assert actual == expected, (node, jet, a, c, actual, expected)
        diagonal.append(actual)
        assert all(int(matrix[row, column]) % P == 0
                   for row in range(index)
                   for column in (index,))

    base_determinant = (pow(lam, 16, P)
                        * pow(delta, 8 * m - 19, P)) % P
    determinant = int(matrix.det()) % P
    assert determinant == pow(base_determinant, jet_layers, P)
    assert matrix.rank() == 8 * jet_layers
    return {
        "node": node,
        "direction_offset": offset,
        "delta": delta,
        "Lambda_at_node": lam,
        "jet_layers": jet_layers,
        "matrix_shape_rank": (matrix.nrows(), matrix.ncols(), matrix.rank()),
        "lower_triangular": True,
        "diagonal": tuple(diagonal),
        "one_layer_determinant": base_determinant,
        "full_determinant": determinant,
        "expected_determinant_formula":
            "(Lambda^16 * delta^(8m-19))^jet_layers",
    }


def main():
    M.T.PRIME = M.F.PRIME = F.PRIME = P
    literal = M.build_case(
        "eight_carrier_local_block", CASE, 7, 7, 4,
        error_direction_offsets=OFFSETS)
    errors = tuple(range(7, 10))
    nodes = tuple(
        one_node(literal, node, offset, delta)
        for node, offset, delta in zip(errors, OFFSETS, DELTAS))

    e = len(errors)
    degree_caps = tuple(3 * e - 1 - a - c for a, c in PAIRS)
    coefficient_dimensions = tuple(cap + 1 for cap in degree_caps)
    assert sum(a + c for a, c in PAIRS) == 16
    assert sum(m - a - 2 * c for a, c in PAIRS
               for m in (CASE[3],)) == 8 * CASE[3] - 19
    assert sum(coefficient_dimensions) == 24 * e - 16 == 56
    assert 8 * 3 * e == 72

    payload = {
        "scope": (
            "exact local value/three-Hasse-layer unit block; complete-state "
            "and passive-seed assembly remain separate"
        ),
        "field": P,
        "case": CASE,
        "carrier_pairs_a_c_in_block_order": PAIRS,
        "carrier_formula":
            "p[a,c] Lambda^a V^(m-a-2c) J1^c Z^(b+a+c)",
        "nodes": nodes,
        "tiny_F101_degree_caps_3e_minus_1_minus_a_minus_c": degree_caps,
        "tiny_F101_coefficient_dimensions": coefficient_dimensions,
        "tiny_F101_total_coefficient_dimension": sum(coefficient_dimensions),
        "tiny_F101_arbitrary_three_jet_output_dimension": 24 * e,
        "tiny_F101_three_jet_dimension_deficit": 16,
        "tiny_F101_deficit_is_not_a_target_obstruction": True,
        "Full187_uniform_degree_cap": 3 * 81731 - 1,
        "Full187_uniform_coefficient_dimension_per_carrier": 3 * 81731,
        "Full187_total_coefficient_dimension": 8 * 3 * 81731,
        "Full187_arbitrary_three_jet_output_dimension": 24 * 81731,
        "Full187_uniform_endpoint_margin_from_independent_width_audit":
            704064,
        "honest_remaining_gate": (
            "identify the complete terminal residual with the selected "
            "three-jet state and assemble its strictly higher-seed leakage; "
            "local invertibility and target Hermite capacity are green"
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
