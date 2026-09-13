#!/usr/bin/env python3
"""Exact pure-Y/Z residual factor probe for canonical F101 grade-seven lifts.

For each canonical correction from the existing grade-seven probe, take the
coefficient c(X) of Y^4 Z^3 and subtract

    c(X) * (Y - Q(X) Z)^4 * Z^3.

The five pure Y/Z shape polynomials are then factored exactly over F_101.
This is a canonical-basis mechanism probe only; it makes no target-scale or
basis-invariant claim.
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
PURE_SHAPES = tuple((y, 0, 0, 7 - y) for y in range(5))
R_SHAPES = tuple((y, 1, 0, 6 - y) for y in range(3))
ALL_SHAPES = PURE_SHAPES + R_SHAPES
TOP_SHAPE = (4, 0, 0, 3)


def polynomial_from_terms(terms: dict[int, int]) -> nmod_poly:
    if not terms:
        return nmod_poly([], PRIME)
    coefficients = [0] * (max(terms) + 1)
    for exponent, coefficient in terms.items():
        coefficients[exponent] = coefficient % PRIME
    return nmod_poly(coefficients, PRIME)


def factor_receipt(poly: nmod_poly) -> dict[str, object]:
    if poly.degree() < 0:
        return {"degree": -1, "polynomial": "0", "factor_unit": 0,
                "factors": ()}
    unit, factors = poly.factor()
    return {
        "degree": poly.degree(),
        "polynomial": str(poly),
        "factor_unit": int(unit),
        "factors": tuple((str(factor), multiplicity)
                         for factor, multiplicity in factors),
    }


def scalar_multiple_against(poly: nmod_poly, reference: nmod_poly):
    """Return a in F_101 when poly=a*reference, otherwise None."""
    if reference.degree() < 0:
        return 0 if poly.degree() < 0 else None
    if poly.degree() != reference.degree():
        return None
    scale = int(poly[poly.degree()]) * pow(int(reference[reference.degree()]), -1, PRIME) % PRIME
    return scale if poly == scale * reference else None


def canonical_grade7_coefficients():
    """Replay the exact canonical relation selection of the existing probe."""
    T.PRIME = F.PRIME = PRIME
    F.GAMMA = 0
    F.MULTIPLICITY = C.M
    xi, q, monomials, contact_columns = P.build_full_columns()
    locator = F.locator(C.AGREEMENT)
    normals = F.centered_locator_normals(locator, (0,), q)
    targets = tuple(P.normal_target(normal, 3) for normal in normals)

    indices = tuple(sorted(
        (index for index, monomial in enumerate(monomials)
         if sum(monomial[1:]) <= C.JET + 1),
        key=lambda index: (
            sum(monomials[index][1:]), sum(monomials[index][1:4]),
            monomials[index][0], monomials[index][3], monomials[index][2],
            monomials[index][1], monomials[index][4])))
    ordered = tuple(monomials[index] for index in indices)
    contact_matrix = T.dense_matrix([contact_columns[index] for index in indices])
    kernel, nullity = contact_matrix.nullspace()
    assert (contact_matrix.rank(), nullity) == (1735, 39)

    j_rows = sorted(
        {row for monomial in ordered
         for row in P.exact_polynomial_normal_rows(monomial, 3)}
        | {row for target in targets for row in target}, key=repr)
    j_index = {row: index for index, row in enumerate(j_rows)}
    flat = [0] * (len(j_rows) * len(indices))
    for column, monomial in enumerate(ordered):
        for row, coefficient in P.exact_polynomial_normal_rows(monomial, 3).items():
            flat[j_index[row] * len(indices) + column] = coefficient
    image = nmod_mat(len(j_rows), len(indices), flat, PRIME) * kernel
    assert image.rank() == 12
    kernel_basis = nmod_mat(kernel.nrows(), nullity, [
        int(kernel[row, column])
        for row in range(kernel.nrows()) for column in range(nullity)], PRIME)

    corrections = []
    for name, target in zip(("F0", "F1", "F2"), targets):
        target_column = [0] * len(j_rows)
        for row, coefficient in target.items():
            target_column[j_index[row]] = (-coefficient) % PRIME
        augmented_flat = []
        for row in range(len(j_rows)):
            augmented_flat.extend(int(image[row, column]) for column in range(nullity))
            augmented_flat.append(target_column[row])
        relations, relation_count = nmod_mat(
            len(j_rows), nullity + 1, augmented_flat, PRIME).nullspace()
        relation = next(column for column in range(relation_count)
                        if int(relations[nullity, column]) % PRIME)
        scale = pow(int(relations[nullity, relation]) % PRIME, -1, PRIME)
        source_vector = kernel_basis * nmod_mat(nullity, 1, [
            int(relations[row, relation]) * scale % PRIME
            for row in range(nullity)], PRIME)
        grouped: dict[tuple[int, int, int, int], dict[int, int]] = defaultdict(dict)
        for row, monomial in enumerate(ordered):
            coefficient = int(source_vector[row, 0]) % PRIME
            if coefficient and sum(monomial[1:]) == C.JET + 1:
                xp, y, r, s, z = monomial
                grouped[(y, r, s, z)][xp] = coefficient
        corrections.append((name, grouped))
    return xi, q, locator, corrections


def main() -> None:
    xi, q, locator, corrections = canonical_grade7_coefficients()
    xi_poly = nmod_poly(list(xi), PRIME)
    q_poly = nmod_poly(list(q), PRIME)
    assert q_poly == xi_poly ** 2
    receipts = []
    ladder_decompositions = []
    taus = []
    raw_shells = []
    residual_shells = []
    top_coefficients = []
    for normal, grouped in corrections:
        assert set(grouped) == set(ALL_SHAPES)
        actual = {shape: polynomial_from_terms(grouped[shape])
                  for shape in PURE_SHAPES}
        c = actual[TOP_SHAPE]
        residuals = {}
        exact_match = {}
        for y, _r, _s, _z in PURE_SHAPES:
            expected = c * ((-1) ** (4 - y)) * comb(4, y) * q_poly ** (4 - y)
            residual = actual[(y, 0, 0, 7 - y)] - expected
            residuals[(y, 0, 0, 7 - y)] = residual
            exact_match[str(y)] = residual.degree() < 0
        nonzero = [poly for poly in residuals.values() if poly.degree() >= 0]
        gcd = nonzero[0]
        for poly in nonzero[1:]:
            gcd = gcd.gcd(poly)
        rho = {}
        for y in range(4):
            quotient, remainder = divmod(residuals[(y, 0, 0, 7 - y)],
                                         xi_poly ** (6 - 2 * y))
            assert remainder.degree() < 0
            rho[y] = quotient
        sigma = {}
        for y in range(3):
            r_shape = (y, 1, 0, 6 - y)
            r_poly = polynomial_from_terms(grouped[r_shape])
            quotient, remainder = divmod(r_poly, xi_poly ** (5 - 2 * y))
            assert remainder.degree() < 0
            sigma[y] = quotient
        for y in range(5):
            expected = c * ((-1) ** (4 - y)) * comb(4, y) * q_poly ** (4 - y)
            if y < 4:
                expected += xi_poly ** (6 - 2 * y) * rho[y]
            assert actual[(y, 0, 0, 7 - y)] == expected
        for y in range(3):
            assert polynomial_from_terms(grouped[(y, 1, 0, 6 - y)]) == \
                xi_poly ** (5 - 2 * y) * sigma[y]
        sigma_scales = tuple(scalar_multiple_against(sigma[y], sigma[0])
                             for y in range(3))
        assert all(scale is not None for scale in sigma_scales)
        assert sigma_scales == (1, PRIME - 2, 1)
        pure_W_moments = {}
        for order in range(4):
            moment = nmod_poly([], PRIME)
            for y in range(order, 4):
                moment += comb(y, order) * rho[y]
            pure_W_moments[order] = moment
        pure_W_multiplicity = next(
            order for order in range(4) if pure_W_moments[order].degree() >= 0)
        assert pure_W_multiplicity == 2
        alpha = pure_W_moments[2]
        beta = pure_W_moments[3]
        assert rho[3] == beta
        assert rho[2] == alpha - 3 * beta
        assert rho[1] == 3 * beta - 2 * alpha
        assert rho[0] == alpha - beta
        tau, remainder = divmod(alpha, sigma[0])
        assert remainder.degree() < 0
        raw_shells.append({shape: polynomial_from_terms(terms)
                           for shape, terms in grouped.items()})
        residual_shells.append(residuals)
        top_coefficients.append(c)
        ladder_decompositions.append({
            "normal": normal,
            "c": factor_receipt(c),
            "rho_pure_core_after_c_Y_minus_QZ_4_Z3": {
                str(y): factor_receipt(rho[y]) for y in range(4)},
            "sigma_R_core": {
                str(y): factor_receipt(sigma[y]) for y in range(3)},
            "sigma_R_core_scales_against_sigma0": sigma_scales,
            "pure_residual_W_moments": {
                str(order): factor_receipt(pure_W_moments[order])
                for order in range(4)},
            "pure_residual_W_multiplicity": pure_W_multiplicity,
            "closed_D_factor_coefficients": {
                "alpha_coefficient_of_QZ": factor_receipt(alpha),
                "beta_coefficient_of_D": factor_receipt(beta),
                "sigma_R": factor_receipt(sigma[0]),
                "universal_tau_alpha_over_sigma": factor_receipt(tau),
            },
            "exact_recomposition": True,
        })
        taus.append(tau)
        receipts.append({
            "normal": normal,
            "c_shape_Y4Z3": factor_receipt(c),
            "pure_shapes_before": {
                repr(shape): factor_receipt(actual[shape]) for shape in PURE_SHAPES},
            "pure_shapes_after_subtract_c_Y_minus_QZ_4_Z3": {
                repr(shape): factor_receipt(residuals[shape]) for shape in PURE_SHAPES},
            "exact_match_by_Y_degree": exact_match,
            "gcd_of_nonzero_residual_pure_shapes": factor_receipt(gcd),
        })

    all_shapes = tuple(sorted(set().union(*(set(shell) for shell in raw_shells))))
    assert all_shapes == tuple(sorted(ALL_SHAPES))
    c0 = int(top_coefficients[0][0])
    full_shell_scale_checks = []
    pure_residual_scale_checks = []
    for index, normal in enumerate(("F0", "F1", "F2")):
        scale = int(top_coefficients[index][0]) * pow(c0, -1, PRIME) % PRIME
        full_mismatches = tuple(
            shape for shape in all_shapes
            if raw_shells[index][shape] != scale * raw_shells[0][shape])
        pure_mismatches = tuple(
            shape for shape in PURE_SHAPES
            if residual_shells[index][shape] != scale * residual_shells[0][shape])
        full_shell_scale_checks.append({
            "normal": normal, "scale_against_F0_from_Y4Z3": scale,
            "mismatch_shapes": full_mismatches,
        })
        pure_residual_scale_checks.append({
            "normal": normal, "scale_against_F0_from_Y4Z3": scale,
            "mismatch_shapes": pure_mismatches,
        })

    normalized_F0_pure_residuals = {
        repr(shape): factor_receipt(residual_shells[0][shape] * pow(c0, -1, PRIME))
        for shape in PURE_SHAPES
    }
    normalized_F0_full_shell = {
        repr(shape): factor_receipt(raw_shells[0][shape] * pow(c0, -1, PRIME))
        for shape in all_shapes
    }
    assert all(tau == taus[0] for tau in taus)
    rho_cross_normal_scales = {
        str(y): tuple(scalar_multiple_against(
            divmod(residual_shells[index][(y, 0, 0, 7 - y)],
                   xi_poly ** (6 - 2 * y))[0],
            divmod(residual_shells[0][(y, 0, 0, 7 - y)],
                   xi_poly ** (6 - 2 * y))[0])
        for index in range(3)) for y in range(4)
    }
    sigma_cross_normal_scales = {
        str(y): tuple(scalar_multiple_against(
            divmod(raw_shells[index][(y, 1, 0, 6 - y)],
                   xi_poly ** (5 - 2 * y))[0],
            divmod(raw_shells[0][(y, 1, 0, 6 - y)],
                   xi_poly ** (5 - 2 * y))[0])
        for index in range(3)) for y in range(3)
    }

    payload = {
        "scope": (
            "canonical F101 grade-seven pure-Y/Z residual factor probe; not a "
            "basis-invariant or target-scale recurrence theorem"),
        "field": PRIME,
        "parameters_n_w_A_m_D_s_t_J_L": C.CASE,
        "Xi": xi,
        "Q_equals_Xi_squared": q,
        "Lambda": locator,
        "subtracted_shape": "c(X)*(Y-Q(X)*Z)^4*Z^3, c=[Y^4 Z^3]",
        "closed_shape_decomposition": (
            "with D=Y-QZ and Q=Xi^2, the complete eight-shape grade-seven shell is "
            "G_i=D^2*Z^3*(c_i*D^2 + beta_i*D*Z + sigma_i*(tau*Q*Z^2 + Xi*R*Z))"
        ),
        "universal_tau": factor_receipt(taus[0]),
        "pure_shapes": PURE_SHAPES,
        "all_grade7_shapes": all_shapes,
        "full_shell_scale_checks": tuple(full_shell_scale_checks),
        "pure_residual_scale_checks": tuple(pure_residual_scale_checks),
        "F0_normalized_by_c_Y4Z3_full_shell": normalized_F0_full_shell,
        "F0_normalized_by_c_pure_residuals": normalized_F0_pure_residuals,
        "rho_core_scales_against_F0_by_Y_degree": rho_cross_normal_scales,
        "sigma_core_scales_against_F0_by_Y_degree": sigma_cross_normal_scales,
        "Xi_Q_factor_ladder_decompositions": tuple(ladder_decompositions),
        "corrections": tuple(receipts),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
