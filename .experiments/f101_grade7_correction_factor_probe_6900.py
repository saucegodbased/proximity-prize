#!/usr/bin/env python3
"""Factor the canonical grade-seven parts of the exact F101 locator lifts.

This replays the already-green primary `L=J+1=7` solve, but exposes the
coefficient polynomials of the new shell instead of only hashing the dense
source vectors.  The output is a mechanism probe: factors or shared support
that are stable across F0/F1/F2 are candidates for a scalable seed-trellis
recurrence.  A basis-dependent factor is not a target theorem.
"""

from __future__ import annotations

import hashlib
import json
from collections import defaultdict
from math import comb
from pathlib import Path

from flint import nmod_mat, nmod_poly

import f101_o2_seedcap_pc_filtration_discriminator_6900 as P
import f101_o2_xi2_full_kernel_certificate_6900 as C
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F
import prime_o2_conormal_threshold_falsifier as T


PRIME = 101


def polynomial_from_terms(terms):
    if not terms:
        return nmod_poly([], PRIME)
    coefficients = [0] * (max(terms) + 1)
    for exponent, coefficient in terms.items():
        coefficients[exponent] = coefficient % PRIME
    return nmod_poly(coefficients, PRIME)


def factor_receipt(poly):
    if poly == 0:
        return {
            "degree": -1,
            "polynomial": "0",
            "factor_unit": 0,
            "factors": (),
        }
    unit, factors = poly.factor()
    return {
        "degree": poly.degree(),
        "polynomial": str(poly),
        "factor_unit": int(unit),
        "factors": tuple((str(factor), multiplicity)
                         for factor, multiplicity in factors),
    }


def exact_quotient(numerator, denominator):
    quotient, remainder = divmod(numerator, denominator)
    assert remainder == 0, (numerator, denominator, remainder)
    return quotient


def main():
    T.PRIME = F.PRIME = PRIME
    F.GAMMA = 0
    F.MULTIPLICITY = C.M
    xi, q, monomials, contact_columns = P.build_full_columns()
    locator = F.locator(C.AGREEMENT)
    locator_poly = nmod_poly(list(locator), PRIME)
    xi_poly = nmod_poly(list(xi), PRIME)
    q_poly = nmod_poly(list(q), PRIME)
    normals = F.centered_locator_normals(locator, (0,), q)
    targets = tuple(P.normal_target(normal, 3) for normal in normals)

    indices = tuple(sorted(
        (index for index, monomial in enumerate(monomials)
         if sum(monomial[1:]) <= C.JET + 1),
        key=lambda index: (
            sum(monomials[index][1:]),
            sum(monomials[index][1:4]),
            monomials[index][0],
            monomials[index][3],
            monomials[index][2],
            monomials[index][1],
            monomials[index][4],
        )))
    ordered = tuple(monomials[index] for index in indices)
    contact_matrix = T.dense_matrix(
        [contact_columns[index] for index in indices])
    kernel, nullity = contact_matrix.nullspace()
    assert (contact_matrix.rank(), nullity) == (1735, 39)

    j_rows = sorted(
        {row for monomial in ordered
         for row in P.exact_polynomial_normal_rows(monomial, 3)}
        | {row for target in targets for row in target}, key=repr)
    j_index = {row: index for index, row in enumerate(j_rows)}
    flat = [0] * (len(j_rows) * len(indices))
    for column, monomial in enumerate(ordered):
        for row, coefficient in P.exact_polynomial_normal_rows(
                monomial, 3).items():
            flat[j_index[row] * len(indices) + column] = coefficient
    j_matrix = nmod_mat(len(j_rows), len(indices), flat, PRIME)
    image = j_matrix * kernel
    assert image.rank() == 12
    kernel_basis = nmod_mat(kernel.nrows(), nullity, [
        int(kernel[row, column])
        for row in range(kernel.nrows())
        for column in range(nullity)
    ], PRIME)

    receipts = []
    shape_sets = []
    for name, target in zip(("F0", "F1", "F2"), targets):
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
        source_vector = kernel_basis * coefficients

        grouped = defaultdict(dict)
        support = []
        for row, monomial in enumerate(ordered):
            coefficient = int(source_vector[row, 0]) % PRIME
            if not coefficient:
                continue
            support.append((monomial, coefficient))
            xp, y, r, s, z = monomial
            if y + r + s + z == C.JET + 1:
                grouped[(y, r, s, z)][xp] = coefficient

        shape_sets.append(set(grouped))
        grouped_polynomials = {
            shape: polynomial_from_terms(terms)
            for shape, terms in grouped.items()
        }
        expected_shapes = {
            (0, 0, 0, 7),
            (0, 1, 0, 6),
            (1, 0, 0, 6),
            (1, 1, 0, 5),
            (2, 0, 0, 5),
            (2, 1, 0, 4),
            (3, 0, 0, 4),
            (4, 0, 0, 3),
        }
        assert set(grouped_polynomials) == expected_shapes

        # The three R-bearing shapes are not merely similarly factored: they
        # are exactly one centered quadratic carrier
        #
        #   A(X) Lambda(X) Xi(X) R Z^4 (Y - Xi(X)^2 Z)^2.
        #
        # This is basis-dependent evidence, but the asserted identity is an
        # exact polynomial equality over F_101, not a visual factor match.
        actuator = exact_quotient(
            grouped_polynomials[(2, 1, 0, 4)],
            locator_poly * xi_poly,
        )
        assert grouped_polynomials[(0, 1, 0, 6)] == (
            actuator * locator_poly * xi_poly**5)
        assert grouped_polynomials[(1, 1, 0, 5)] == (
            -2 * actuator * locator_poly * xi_poly**3)
        assert grouped_polynomials[(2, 1, 0, 4)] == (
            actuator * locator_poly * xi_poly)

        # Split the five pure Y/Z shapes against the centered quartic whose
        # leading coefficient is forced by the Y^4 Z^3 shape.  The residual
        # factors tell us whether the same actuator A controls the rest of the
        # canonical correction.
        quartic_lead = grouped_polynomials[(4, 0, 0, 3)]
        residual_by_y = {}
        for y in range(5):
            shape = (y, 0, 0, 7 - y)
            centered_coefficient = (
                quartic_lead * comb(4, y) * (-q_poly) ** (4 - y))
            residual_by_y[y] = (
                grouped_polynomials[shape] - centered_coefficient)

        # Convert the pure part completely from the Y basis to the centered
        # V = Y - Xi^2 Z basis.  This triangular change of variables is exact
        # and exposes which V-adic layers really occur; a single-cubic guess
        # is deliberately not assumed.
        centered_pure = {}
        for k in range(4, -1, -1):
            coefficient = grouped_polynomials[(k, 0, 0, 7 - k)]
            for higher in range(k + 1, 5):
                coefficient -= (
                    centered_pure[higher]
                    * comb(higher, k)
                    * (-q_poly) ** (higher - k)
                )
            centered_pure[k] = coefficient
        xi_derivative = xi_poly.derivative()
        assert centered_pure[0] == 0
        assert centered_pure[1] == 0
        assert centered_pure[2] == (
            -2 * actuator * locator_poly * xi_poly**2 * xi_derivative)
        locator_derivative = locator_poly.derivative()
        wronskian_remainder = exact_quotient(
            centered_pure[3]
            + actuator * xi_poly * locator_derivative,
            locator_poly,
        )
        boundary_zero_cofactor = (
            centered_pure[3]
            - centered_pure[4] * q_poly
            + 2 * actuator * locator_poly * xi_derivative
        )
        assert boundary_zero_cofactor.degree() == 13
        assert grouped_polynomials[(0, 0, 0, 7)] == (
            boundary_zero_cofactor * (-q_poly) ** (C.M - 1))

        pure_residuals = []
        for y in range(5):
            shape = (y, 0, 0, 7 - y)
            centered_coefficient = (
                quartic_lead * comb(4, y) * (-q_poly) ** (4 - y))
            residual = residual_by_y[y]
            pure_residuals.append({
                "shape_Y_R_S_Z": shape,
                "centered_quartic_coefficient": str(centered_coefficient),
                "residual": factor_receipt(residual),
                "residual_gcd_with_actuator": factor_receipt(
                    residual.gcd(actuator)),
                "residual_gcd_with_Lambda_Xi": factor_receipt(
                    residual.gcd(locator_poly * xi_poly)),
            })
        shell = []
        for shape in sorted(grouped):
            poly = polynomial_from_terms(grouped[shape])
            shell.append({
                "shape_Y_R_S_Z": shape,
                "X_support": tuple(sorted(grouped[shape])),
                **factor_receipt(poly),
            })
        receipts.append({
            "normal": name,
            "whole_source_support": len(support),
            "whole_source_sha256": hashlib.sha256(
                repr(tuple(support)).encode()).hexdigest(),
            "grade_seven_shapes": len(grouped),
            "grade_seven_terms": sum(len(terms)
                                     for terms in grouped.values()),
            "exact_R_carrier": {
                "identity": (
                    "A(X)*Lambda(X)*Xi(X)*R*Z^4*"
                    "(Y-Xi(X)^2*Z)^2"
                ),
                "A": factor_receipt(actuator),
            },
            "exact_centered_shell": {
                "V": "Y-Xi(X)^2*Z",
                "V1": "R-2*Xi(X)*Xi'(X)*Z",
                "J1": "Lambda(X)*V1-Lambda'(X)*V",
                "identity": (
                    "V^2*Z^3*(c(X)*V^2 + B(X)*V*Z + "
                    "A(X)*Lambda(X)*Xi(X)*V1*Z)"
                ),
                "covariant_identity": (
                    "V^2*Z^3*(c(X)*V^2 + C(X)*Lambda(X)*V*Z + "
                    "A(X)*Xi(X)*J1*Z)"
                ),
                "A": factor_receipt(actuator),
                "B": factor_receipt(centered_pure[3]),
                "C": factor_receipt(wronskian_remainder),
                "c": factor_receipt(centered_pure[4]),
                "B0_boundary_zero_cofactor": {
                    "definition": "B-c*Q+2*A*Lambda*Xi'",
                    "raw_boundary_zero_identity": "B0*(-Q)^(m-1)",
                    **factor_receipt(boundary_zero_cofactor),
                },
            },
            "pure_centered_quartic_split": {
                "identity": "sum_k C_k(X)*(Y-Q(X)*Z)^k*Z^(7-k)",
                "c": factor_receipt(quartic_lead),
                "centered_coefficients_C0_through_C4": tuple(
                    factor_receipt(centered_pure[k]) for k in range(5)),
                "residuals": tuple(pure_residuals),
            },
            "grade_seven_coefficients": tuple(shell),
        })

    common_shapes = set.intersection(*shape_sets)
    union_shapes = set.union(*shape_sets)
    payload = {
        "scope": (
            "canonical-basis factor probe for one exact F101 grade-seven "
            "locator lift; not invariant under kernel-basis changes"
        ),
        "field": PRIME,
        "parameters_n_w_A_m_D_s_t_J_L": C.CASE,
        "Xi": xi,
        "Q_equals_Xi_squared": q,
        "Lambda": locator,
        "contact_rank_nullity": (contact_matrix.rank(), nullity),
        "J_rank_on_contact_kernel": image.rank(),
        "common_grade_seven_shapes": tuple(sorted(common_shapes)),
        "union_grade_seven_shapes": tuple(sorted(union_shapes)),
        "corrections": tuple(receipts),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(
        canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
