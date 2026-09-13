#!/usr/bin/env python3
"""Exact grade-seven centered-shell falsifier for the fixed offsets (3,5,7).

This is one predeclared non-Q error-direction chamber, not a parameter scan.
It reuses the literal all-node contact/J solve of the matched n=10 chamber
and then records the first centered coefficients that obstruct the prior
three-carrier Wronskian shell.
"""

from __future__ import annotations

import hashlib
import json
from math import comb
from pathlib import Path

from flint import nmod_poly

import f101_o2_bordered_filtration_mechanism_6900 as M
import f101_n10_grade7_centered_wronskian_universality_6900 as U


PRIME = 101
CASE = (10, 4, 7, 4, 28, 1, 1, 6, 10)
OFFSETS = (3, 5, 7)


def quotient_receipt(numerator, denominator):
    quotient, remainder = divmod(numerator, denominator)
    return U.factor_receipt(quotient), U.factor_receipt(remainder)


def centered_pure(grouped, q):
    """Write the pure part as sum H_k (Y-QZ)^k Z^(7-k)."""
    centered = {}
    for power in range(4, -1, -1):
        coefficient = grouped[(power, 0, 0, 7 - power)]
        for higher in range(power + 1, 5):
            coefficient -= (centered[higher] * comb(higher, power)
                            * (-q)**(higher - power))
        centered[power] = coefficient
    return centered


def centered_r(grouped, q):
    """Write the R part as sum T_k R (Y-QZ)^k Z^(6-k)."""
    r2 = grouped[(2, 1, 0, 4)]
    r1 = grouped[(1, 1, 0, 5)] + 2 * q * r2
    r0 = grouped[(0, 1, 0, 6)] + q * r1 - q**2 * r2
    return {0: r0, 1: r1, 2: r2}


def one_rhs(literal, indices, normal, source):
    support, observed = U.grouped_grade_seven(literal, indices, source)
    assert set(observed) == U.EXPECTED_SHAPES, tuple(sorted(observed))
    # All expected raw coefficients are nonzero here, but make the raw shape
    # scope explicit before performing the centered change of variables.
    grouped = {shape: observed[shape] for shape in U.EXPECTED_SHAPES}
    xi = nmod_poly(list(literal.xi), PRIME)
    q = nmod_poly(list(literal.q), PRIME)
    locator = nmod_poly(list(literal.locator), PRIME)
    xi_prime = xi.derivative()
    locator_prime = locator.derivative()

    r = centered_r(grouped, q)
    pure = centered_pure(grouped, q)
    actuator, r2_remainder = divmod(r[2], locator * xi)
    cofactor, wronskian_remainder = divmod(
        pure[3] + actuator * xi * locator_prime, locator)
    assert r2_remainder == 0
    assert wronskian_remainder == 0

    # What the former three-carrier form would require to vanish.
    r_extra = {0: r[0], 1: r[1]}
    pure_extra = {
        0: pure[0],
        1: pure[1],
        2: pure[2] + 2 * actuator * locator * xi**2 * xi_prime,
    }
    c = pure[4]
    b0 = pure[3] - c * q + 2 * actuator * locator * xi_prime
    boundary_remainder = grouped[(0, 0, 0, 7)] - b0 * (-q)**3

    # This is a countergate, not a failed attempt: every displayed extra
    # coefficient is nonzero, so the prior three-carrier shell is false.
    assert all(poly != 0 for poly in r_extra.values())
    assert all(poly != 0 for poly in pure_extra.values())
    assert boundary_remainder != 0

    return {
        "normal": normal,
        "whole_restricted_source_support": len(support),
        "whole_restricted_source_sha256": hashlib.sha256(
            repr(tuple(support)).encode()).hexdigest(),
        "raw_grade7_shapes": tuple(sorted(observed)),
        "raw_grade7_terms": sum(
            1 for monomial, _coefficient in support
            if sum(monomial[1:]) == 7),
        "surviving_congruences": {
            "T2_equals_A_Lambda_Xi": {
                "A": U.factor_receipt(actuator),
                "division_remainder": U.factor_receipt(r2_remainder),
            },
            "B_plus_A_Xi_Lambda_prime_equals_Lambda_C": {
                "B": U.factor_receipt(pure[3]),
                "C": U.factor_receipt(cofactor),
                "division_remainder": U.factor_receipt(wronskian_remainder),
            },
        },
        "centered_R_coefficients_T0_T1_T2": tuple(
            U.factor_receipt(r[power]) for power in range(3)),
        "centered_pure_coefficients_H0_through_H4": tuple(
            U.factor_receipt(pure[power]) for power in range(5)),
        "three_carrier_countergate": {
            "formerly_required_zero_R_V0Z6": U.factor_receipt(r_extra[0]),
            "formerly_required_zero_R_V1Z5": U.factor_receipt(r_extra[1]),
            "formerly_required_zero_V0Z7": U.factor_receipt(pure_extra[0]),
            "formerly_required_zero_V1Z6": U.factor_receipt(pure_extra[1]),
            "V2Z5_residual_after_covariant_term": U.factor_receipt(
                pure_extra[2]),
            "B0": U.factor_receipt(b0),
            "raw_Z7_minus_B0_times_minus_Q_cubed": U.factor_receipt(
                boundary_remainder),
        },
    }


def main():
    M.T.PRIME = M.F.PRIME = PRIME
    literal = M.build_case(
        "matched_n10_L10_error_direction_offsets_3_5_7", CASE,
        actual_agreement_count=7, anchor_count=7, normal_coordinates=4,
        error_direction_offsets=OFFSETS)
    indices, contact, nullity, image, lifts = U.solve_restricted(literal)
    rows = tuple(one_rhs(literal, indices, normal, source)
                 for normal, source in lifts)
    payload = {
        "scope": (
            "The one predeclared n=10 exact-border chamber with error "
            "direction offsets (3,5,7); first three RHS only, source "
            "boundary grade <=7."
        ),
        "field": PRIME,
        "parameters_n_w_A_m_D_s_t_J_L": CASE,
        "error_direction_offsets_from_Q": OFFSETS,
        "Xi": literal.xi,
        "Q_equals_Xi_squared": literal.q,
        "Lambda": literal.locator,
        "source_columns_grade_at_most_7": len(indices),
        "contact_rank_nullity": (contact.rank(), nullity),
        "J_rank_on_contact_kernel": image.rank(),
        "countergate_result": (
            "FAILS: nonzero centered R*V^0, R*V^1, V^0, V^1, and "
            "covariant-V^2 residuals remain, even though the two stated "
            "divisibilities survive."
        ),
        "first_three_rhs": rows,
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
