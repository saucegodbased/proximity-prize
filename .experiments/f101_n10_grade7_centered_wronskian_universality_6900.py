#!/usr/bin/env python3
"""Exact n=10 replay of the F101 grade-seven centered-shell probe.

The two chambers are fixed in the bordered-filtration mechanism before this
script runs.  For each one, this script restricts the literal coupled source
to total boundary grade at most J+1=7, solves the all-node contact kernel and
the first three literal J right hand sides, then reconstructs the *entire*
grade-seven piece in centered coordinates.  It is intentionally a bounded
universality check, not a parameter scan or a submission artifact.
"""

from __future__ import annotations

import hashlib
import json
from collections import defaultdict
from math import comb
from pathlib import Path

from flint import nmod_mat, nmod_poly

import f101_o2_bordered_filtration_mechanism_6900 as M


PRIME = 101
EXPECTED_SHAPES = {
    (0, 0, 0, 7), (0, 1, 0, 6),
    (1, 0, 0, 6), (1, 1, 0, 5),
    (2, 0, 0, 5), (2, 1, 0, 4),
    (3, 0, 0, 4), (4, 0, 0, 3),
}


def polynomial_from_terms(terms):
    if not terms:
        return nmod_poly([], PRIME)
    coefficients = [0] * (max(terms) + 1)
    for exponent, coefficient in terms.items():
        coefficients[exponent] = coefficient % PRIME
    return nmod_poly(coefficients, PRIME)


def factor_receipt(poly):
    if poly == 0:
        return {"degree": -1, "polynomial": "0", "factors": ()}
    unit, factors = poly.factor()
    return {
        "degree": poly.degree(),
        "polynomial": str(poly),
        "factor_unit": int(unit),
        "factors": tuple((str(factor), int(multiplicity))
                         for factor, multiplicity in factors),
    }


def exact_quotient(numerator, denominator):
    quotient, remainder = divmod(numerator, denominator)
    assert remainder == 0, (numerator, denominator, remainder)
    return quotient


def restricted_indices(literal):
    jet = literal.parameters[7]
    return tuple(sorted(
        (index for index, monomial in enumerate(literal.monomials)
         if sum(monomial[1:]) <= jet + 1),
        key=lambda index: (
            sum(literal.monomials[index][1:]),
            sum(literal.monomials[index][1:4]),
            literal.monomials[index][0],
            literal.monomials[index][3],
            literal.monomials[index][2],
            literal.monomials[index][1],
            literal.monomials[index][4],
        )))


def matrix_from_columns(row_ids, columns, indices):
    row_index = {row: index for index, row in enumerate(row_ids)}
    flat = [0] * (len(row_ids) * len(indices))
    for column, source_index in enumerate(indices):
        for row, coefficient in columns[source_index].items():
            destination = row_index.get(row)
            if destination is not None:
                flat[destination * len(indices) + column] = coefficient
    return nmod_mat(len(row_ids), len(indices), flat, PRIME)


def solve_restricted(literal):
    """Return canonical kernel lifts of the first three exact normal RHS."""
    indices = restricted_indices(literal)
    contact_rows = tuple(index for index, row in enumerate(literal.row_keys)
                         if row[0] == "C")
    j_rows = tuple(sorted(
        {index for source_index in indices
         for index in literal.columns[source_index]
         if literal.row_keys[index][0] == "J"}
        | {index for target in literal.targets[:3] for index in target}))
    contact = matrix_from_columns(contact_rows, literal.columns, indices)
    kernel, nullity = contact.nullspace()
    j_matrix = matrix_from_columns(j_rows, literal.columns, indices)
    image = j_matrix * kernel
    kernel_basis = nmod_mat(kernel.nrows(), nullity, [
        int(kernel[row, column])
        for row in range(kernel.nrows())
        for column in range(nullity)
    ], PRIME)
    j_index = {row: index for index, row in enumerate(j_rows)}

    lifts = []
    for normal, target in zip(("F0", "F1", "F2"), literal.targets[:3]):
        # This sign matches the exact bordered solve used by the primary
        # factor probe: the resulting source has J-image equal to target.
        target_column = [0] * len(j_rows)
        for row, coefficient in target.items():
            target_column[j_index[row]] = (-coefficient) % PRIME
        augmented_flat = []
        for row in range(len(j_rows)):
            augmented_flat.extend(
                int(image[row, column]) for column in range(nullity))
            augmented_flat.append(target_column[row])
        augmented = nmod_mat(
            len(j_rows), nullity + 1, augmented_flat, PRIME)
        relations, relation_count = augmented.nullspace()
        relation = next(column for column in range(relation_count)
                        if int(relations[nullity, column]) % PRIME)
        scale = pow(int(relations[nullity, relation]) % PRIME, -1, PRIME)
        coefficients = nmod_mat(nullity, 1, [
            int(relations[row, relation]) * scale % PRIME
            for row in range(nullity)
        ], PRIME)
        source = kernel_basis * coefficients
        # A direct sparse check prevents a sign or row-order convention from
        # being mistaken for the centered identity below.
        assert all(int((j_matrix * source)[row, 0]) % PRIME ==
                   target.get(j_rows[row], 0) % PRIME
                   for row in range(len(j_rows)))
        lifts.append((normal, source))
    return indices, contact, nullity, image, lifts


def grouped_grade_seven(literal, indices, source):
    grouped = defaultdict(dict)
    support = []
    for row, source_index in enumerate(indices):
        coefficient = int(source[row, 0]) % PRIME
        if not coefficient:
            continue
        monomial = literal.monomials[source_index]
        support.append((monomial, coefficient))
        xp, y, r, s, z = monomial
        if y + r + s + z == 7:
            grouped[(y, r, s, z)][xp] = coefficient
    return support, {shape: polynomial_from_terms(terms)
                     for shape, terms in grouped.items()}


def centered_receipt(literal, grouped):
    """Prove/reject the same 3-carrier identity by exact coefficient tests."""
    # A carrier is allowed to vanish (and then its raw shape is absent from
    # the sparse source).  The assertion is therefore a no-new-shape test,
    # rather than an artificial nonvanishing requirement inherited from n=11.
    assert set(grouped).issubset(EXPECTED_SHAPES), tuple(sorted(grouped))
    grouped = {shape: grouped.get(shape, nmod_poly([], PRIME))
               for shape in EXPECTED_SHAPES}
    xi = nmod_poly(list(literal.xi), PRIME)
    q = nmod_poly(list(literal.q), PRIME)
    locator = nmod_poly(list(literal.locator), PRIME)
    xi_derivative = xi.derivative()
    locator_derivative = locator.derivative()

    # The centered R tail has one possible carrier coefficient A.
    actuator = exact_quotient(grouped[(2, 1, 0, 4)], locator * xi)
    assert grouped[(0, 1, 0, 6)] == actuator * locator * xi**5
    assert grouped[(1, 1, 0, 5)] == -2 * actuator * locator * xi**3
    assert grouped[(2, 1, 0, 4)] == actuator * locator * xi

    # Triangularly transform the five pure Y/Z coefficients to V=Y-QZ.
    centered = {}
    for power in range(4, -1, -1):
        coefficient = grouped[(power, 0, 0, 7 - power)]
        for higher in range(power + 1, 5):
            coefficient -= (centered[higher] * comb(higher, power)
                            * (-q)**(higher - power))
        centered[power] = coefficient

    assert centered[0] == 0
    assert centered[1] == 0
    assert centered[2] == -2 * actuator * locator * xi**2 * xi_derivative
    c = centered[4]
    b = centered[3]
    cofactor = exact_quotient(b + actuator * xi * locator_derivative,
                              locator)
    assert centered[3] == cofactor * locator - actuator * xi * locator_derivative
    assert centered[2] == -actuator * xi * locator * (2 * xi * xi_derivative)

    # Direct raw-X boundary identity, in the terminology of the shell audit.
    b0 = b - c * q + 2 * actuator * locator * xi_derivative
    m = literal.parameters[3]
    assert grouped[(0, 0, 0, 7)] == b0 * (-q)**(m - 1)

    return {
        "identity": (
            "V^2*Z^3*(c*V^2 + C*Lambda*V*Z + A*Xi*J1*Z), "
            "V=Y-Xi^2*Z, V1=R-2*Xi*Xi'*Z, "
            "J1=Lambda*V1-Lambda'*V"
        ),
        "A": factor_receipt(actuator),
        "C": factor_receipt(cofactor),
        "c": factor_receipt(c),
        "B": factor_receipt(b),
        "B0_equals_B_minus_cQ_plus_2ALambdaXi_prime": factor_receipt(b0),
        "centered_pure_V0_through_V4": tuple(
            factor_receipt(centered[power]) for power in range(5)),
        "degree_summary": {
            "e_equals_deg_Xi": xi.degree(),
            "deg_A": actuator.degree(),
            "deg_C": cofactor.degree(),
            "deg_c": c.degree(),
            "deg_B0": b0.degree(),
        },
    }


def one_case(case_definition):
    label, parameters, actual, anchor, coordinates = case_definition
    literal = M.build_case(label, parameters, actual, anchor, coordinates)
    indices, contact, nullity, image, lifts = solve_restricted(literal)
    rows = []
    for normal, source in lifts:
        support, grouped = grouped_grade_seven(literal, indices, source)
        rows.append({
            "normal": normal,
            "whole_restricted_source_support": len(support),
            "whole_restricted_source_sha256": hashlib.sha256(
                repr(tuple(support)).encode()).hexdigest(),
            "grade_seven_shapes": tuple(sorted(grouped)),
            "grade_seven_terms": sum(
                1 for monomial, _coefficient in support
                if sum(monomial[1:]) == 7),
            "centered_reconstruction": centered_receipt(literal, grouped),
        })
    return {
        "label": label,
        "parameters_n_w_A_m_D_s_t_J_L": parameters,
        "normal_coordinates": coordinates,
        "Xi": literal.xi,
        "Q_equals_Xi_squared": literal.q,
        "Lambda": literal.locator,
        "source_columns_grade_at_most_7": len(indices),
        "contact_rank_nullity": (contact.rank(), nullity),
        "J_rank_on_contact_kernel": image.rank(),
        "first_three_rhs": tuple(rows),
    }


def main():
    M.T.PRIME = M.F.PRIME = PRIME
    rows = tuple(one_case(case_definition) for case_definition in M.CASES[1:])
    payload = {
        "scope": (
            "Two predeclared matched n=10 chambers; literal all-node "
            "contact and first-three J RHS, restricted only to source "
            "boundary grade <= 7."
        ),
        "field": PRIME,
        "expected_exact_grade7_shapes": tuple(sorted(EXPECTED_SHAPES)),
        "cases": rows,
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
