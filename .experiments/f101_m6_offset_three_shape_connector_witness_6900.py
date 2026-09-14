#!/usr/bin/env python3
"""Extract a canonical three-shape connector in the m=6 offset chamber.

The companion discriminator proves that the union of the total-grade-nine
``(r,s) = (0,0),(0,1),(1,0)`` groups contains all four packet residues
modulo the complete total-grade-at-most-eight prefix.  This script solves
those four equations coefficientwise with all free variables set to zero and
records the actual X-polynomial profiles.  The solution is not unique.  The
purpose is to distinguish a locator/CRT formula from a dense finite-field
coincidence; this remains a finite F_101 control.
"""

from __future__ import annotations

from collections import defaultdict
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat, nmod_poly

sys.path.insert(0, ".experiments")
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import f101_m456_pure_centered_connector_discriminator_6900 as D  # noqa: E402


P = 101
CASE = D.CASES["m6"]
OFFSETS = D.ERROR_OFFSETS
SHELL_SHAPES = ((0, 0), (0, 1), (1, 0))


def polynomial(values):
    """Trim one little-endian coefficient vector as an nmod_poly."""
    while values and values[-1] % P == 0:
        values.pop()
    return nmod_poly(values or [0], P)


def factor_string(poly):
    if poly == 0:
        return "0"
    unit, factors = poly.factor()
    pieces = [str(unit)] if int(unit) != 1 else []
    pieces.extend(
        f"({factor})^{multiplicity}" if multiplicity != 1 else f"({factor})"
        for factor, multiplicity in factors)
    return "*".join(pieces) or "1"


def factor_degree_profile(poly):
    """Record only irreducible degrees/multiplicities, avoiding huge output."""
    if poly == 0:
        return ()
    _unit, factors = poly.factor()
    return tuple((factor.degree(), multiplicity)
                 for factor, multiplicity in factors)


def locator_divisibility(poly, locators):
    """Test divisibility by the natural agreement/error/domain locators."""
    return {
        name: {
            "locator_degree": locator.degree(),
            "divides": poly != 0 and poly % locator == 0,
            "quotient_degree_if_divides": (
                (poly // locator).degree()
                if poly != 0 and poly % locator == 0 else None),
        }
        for name, locator in locators.items()
    }


def solve_columns(columns, targets):
    rows = tuple(sorted(
        set().union(*(set(column) for column in columns),
                    *(set(target) for target in targets))))
    matrix = nmod_mat(len(rows), len(columns), [
        column.get(row, 0)
        for row in rows for column in columns
    ], P)
    target_matrix = nmod_mat(len(rows), len(targets), [
        target.get(row, 0)
        for row in rows for target in targets
    ], P)
    augmented = nmod_mat(len(rows), len(columns) + len(targets), [
        (columns[column].get(row, 0)
         if column < len(columns)
         else targets[column - len(columns)].get(row, 0))
        for row in rows for column in range(len(columns) + len(targets))
    ], P)
    reduced, augmented_rank = augmented.rref()
    source_rank = matrix.rank()
    assert augmented_rank == source_rank
    solution = nmod_mat(len(columns), len(targets), P)
    pivots = []
    for row in range(augmented_rank):
        pivot = next((column for column in range(len(columns))
                      if int(reduced[row, column]) % P), None)
        assert pivot is not None
        assert int(reduced[row, pivot]) % P == 1
        pivots.append(pivot)
        for target in range(len(targets)):
            solution[pivot, target] = int(
                reduced[row, len(columns) + target]) % P
    assert matrix * solution == target_matrix
    free_columns = tuple(column for column in range(len(columns))
                         if column not in set(pivots))
    kernel_basis = []
    for free in free_columns:
        vector = nmod_mat(len(columns), 1, P)
        vector[free, 0] = 1
        for row, pivot in enumerate(pivots):
            vector[pivot, 0] = -int(reduced[row, free]) % P
        assert matrix * vector == nmod_mat(len(rows), 1, P)
        kernel_basis.append(vector)
    return solution, tuple(kernel_basis), {
        "row_count": len(rows),
        "source_column_count": len(columns),
        "source_rank": source_rank,
        "source_nullity": len(columns) - source_rank,
        "canonical_free_variables_set_to_zero": True,
        "pivot_count": len(pivots),
        "explicit_kernel_basis_size": len(kernel_basis),
    }


def group_layers_divisible(shell_indices, vector, literal, shape, locator):
    """Whether every X-polynomial layer in one shape is locator-divisible."""
    layers = defaultdict(list)
    for row, source_index in enumerate(shell_indices):
        if literal.monomials[source_index][2:4] != shape:
            continue
        xp, y, r, s, z = literal.monomials[source_index]
        layers[(y, r, s, z)].append((xp, int(vector[row, 0]) % P))
    for entries in layers.values():
        width = max(xp for xp, _coefficient in entries) + 1
        coefficients = [0] * width
        for xp, coefficient in entries:
            coefficients[xp] = coefficient
        if polynomial(coefficients) % locator != 0:
            return False
    return True


def layer_summary(shell_indices, solution, literal, target, locators):
    layers = defaultdict(list)
    for row, source_index in enumerate(shell_indices):
        coefficient = int(solution[row, target]) % P
        if coefficient:
            xp, y, r, s, z = literal.monomials[source_index]
            layers[(y, r, s, z)].append((xp, coefficient))
    answer = []
    polynomials = []
    for shape, entries in sorted(layers.items()):
        degree_bound = max(x for x, *_ in (
            literal.monomials[index] for index in shell_indices
            if literal.monomials[index][1:] == shape)) + 1
        coefficients = [0] * degree_bound
        for xp, coefficient in entries:
            coefficients[xp] = coefficient
        poly = polynomial(coefficients)
        polynomials.append(poly)
        answer.append({
            "Y_R_S_Z": shape,
            "nonzero_coefficients": len(entries),
            "admitted_X_width": degree_bound,
            "actual_X_degree": poly.degree(),
            "support_min_max": (min(x for x, _ in entries),
                                max(x for x, _ in entries)),
            "factor_degree_profile": factor_degree_profile(poly),
            "locator_divisibility": locator_divisibility(poly, locators),
            "coefficient_sha256": hashlib.sha256(
                repr(tuple(entries)).encode()).hexdigest(),
        })
    common = polynomials[0] if polynomials else nmod_poly([0], P)
    for poly in polynomials[1:]:
        common = common.gcd(poly)
    return {
        "nonzero_source_coefficients": sum(len(entries)
                                           for entries in layers.values()),
        "nonzero_YRSZ_layers": len(layers),
        "common_polynomial_gcd": factor_string(common),
        "common_polynomial_gcd_degree": common.degree(),
        "common_polynomial_gcd_factor_degree_profile": (
            factor_degree_profile(common)),
        "common_gcd_locator_divisibility": (
            locator_divisibility(common, locators)),
        "layers": tuple(answer),
    }


def main():
    started = time.monotonic()
    M.PRIME = M.T.PRIME = M.F.PRIME = P
    literal = M.build_case(
        "m6_offset_three_shape_connector_witness",
        CASE,
        actual_agreement_count=CASE[2],
        anchor_count=CASE[2],
        normal_coordinates=4,
        error_direction_offsets=OFFSETS,
    )
    prefix = tuple(
        index for index, monomial in enumerate(literal.monomials)
        if sum(monomial[1:]) <= CASE[7])
    prefix_echelon = M.ColumnEchelon()
    for index in prefix:
        prefix_echelon.add(literal.columns[index], index)
    assert prefix_echelon.rank == len(prefix) == 3582

    shell_indices = tuple(
        index for index, monomial in enumerate(literal.monomials)
        if sum(monomial[1:]) == CASE[7] + 1
        and (monomial[2], monomial[3]) in SHELL_SHAPES)
    assert len(shell_indices) == 642
    shell_residues = tuple(
        prefix_echelon.reduce(literal.columns[index])
        for index in shell_indices)
    target_residues = tuple(
        prefix_echelon.reduce(target) for target in literal.targets)
    solution, kernel_basis, solve_receipt = solve_columns(
        shell_residues, target_residues)

    agreement_locator = nmod_poly(list(literal.locator), P)
    error_locator = nmod_poly(list(literal.xi), P)
    domain_locator = agreement_locator * error_locator
    locators = {
        "agreement": agreement_locator,
        "error": error_locator,
        "full_domain": domain_locator,
        "Q_equals_error_locator_squared": nmod_poly(list(literal.q), P),
    }

    packet_summaries = []
    for target in range(4):
        by_group = []
        for shape in SHELL_SHAPES:
            selected_rows = tuple(
                row for row, source_index in enumerate(shell_indices)
                if literal.monomials[source_index][2:4] == shape)
            selected_indices = tuple(shell_indices[row] for row in selected_rows)
            group_solution = nmod_mat(len(selected_rows), 1, [
                int(solution[row, target]) % P for row in selected_rows
            ], P)
            summary = layer_summary(
                selected_indices, group_solution, literal, 0, locators)
            summary["derivative_shape_r_s"] = shape
            by_group.append(summary)
        packet_summaries.append({
            "packet": f"F{target}",
            "nonzero_coefficients": sum(
                int(solution[row, target]) % P != 0
                for row in range(solution.nrows())),
            "shape_groups": tuple(by_group),
        })

    s_shape = (0, 1)
    canonical_columns = tuple(
        nmod_mat(solution.nrows(), 1, [
            int(solution[row, target]) % P
            for row in range(solution.nrows())
        ], P)
        for target in range(4))
    canonical_s_domain_divisible = tuple(
        group_layers_divisible(shell_indices, vector, literal, s_shape,
                               domain_locator)
        for vector in canonical_columns)
    kernel_s_domain_divisible = tuple(
        group_layers_divisible(shell_indices, vector, literal, s_shape,
                               domain_locator)
        for vector in kernel_basis)

    stable = {
        "scope": (
            "canonical coefficientwise three-shape first-shell witnesses "
            "with free variables zero modulo the full grade-eight prefix; "
            "finite F101 control only"),
        "parameters_n_w_g_m_D_s_t_J_L": CASE,
        "error_direction_offsets": OFFSETS,
        "prefix_columns_rank": (len(prefix), prefix_echelon.rank),
        "shell_shapes": SHELL_SHAPES,
        "solve_receipt": solve_receipt,
        "natural_locators": {
            name: {
                "degree": poly.degree(),
                "factorization": factor_string(poly),
            }
            for name, poly in locators.items()
        },
        "packet_witnesses": tuple(packet_summaries),
        "full_domain_locator_in_S_group": {
            "canonical_packets_all_layers_divisible": (
                canonical_s_domain_divisible),
            "kernel_basis_all_layers_divisible": kernel_s_domain_divisible,
            "forced_for_every_solution": (
                all(canonical_s_domain_divisible)
                and all(kernel_s_domain_divisible)),
        },
        "decision_rule": (
            "A low-degree locator/common gcd supports a symbolic recurrence; "
            "dense unrelated factors are finite evidence only."),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    print(json.dumps({
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "runtime_receipt": {
            "elapsed_seconds": round(time.monotonic() - started, 6),
            "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        },
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
