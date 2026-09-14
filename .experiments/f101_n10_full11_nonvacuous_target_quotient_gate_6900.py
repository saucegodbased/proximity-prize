#!/usr/bin/env python3
"""Decisive finite gate for the full order-four covariant repair module.

The old n=4 target experiment was vacuous: the grade-at-most-J source
already contained all three target normals.  Here we use the established
n=10 arbitrary-direction chamber, at m=5 and m=6, where each target has a
genuine one-dimensional defect modulo grade <= J.

Some of the eleven weighted-order-four covariants are not individually
legal in this deliberately tight chamber.  We therefore form the raw
covariant module first and compute its exact subspace whose illegal source
monomials cancel.  Only the resulting legal compound sources are mapped to
contact columns.  The final question is whether those legal compound
sources close the three actual target defects modulo the old source.

This is finite F_101 evidence.  It is not a Full187 theorem.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys
import time

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import f101_order4_osculating_covariant_basis_gate_6900 as O  # noqa: E402
import f101_terminal_seed_trellis_three_carrier_6900 as TT  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402


P = 101
MULTIPLICITIES = (5, 6)
OFFSETS = (3, 5, 7)
MULTIPLIER_DEGREE = 8


def add_scaled(target, source, scale=1):
    for monomial, coefficient in source.items():
        value = (target.get(monomial, 0) + scale * coefficient) % P
        if value:
            target[monomial] = value
        else:
            target.pop(monomial, None)


def shifted_x(source, amount):
    return {
        (x + amount, y, r, s, z): coefficient
        for (x, y, r, s, z), coefficient in source.items()
    }


def shifted_z(source, amount):
    return {
        (x, y, r, s, z + amount): coefficient
        for (x, y, r, s, z), coefficient in source.items()
    }


def centered_v(literal):
    return F.sparse_add(
        F.Y, F.sparse_mul(F.Z, F.sparse_embed_x(literal.q)), -1)


def raw_full11_columns(literal, m, shift_count):
    prefactor = F.sparse_pow(centered_v(literal), m - 4)
    columns = []
    tags = []
    for label, exponents, _active, _seed, source in \
            O.weighted_order_four_families(literal):
        source = F.sparse_mul(source, prefactor)
        for z_shift in range(shift_count):
            z_source = shifted_z(source, z_shift)
            for x_degree in range(MULTIPLIER_DEGREE + 1):
                columns.append(shifted_x(z_source, x_degree))
                tags.append((label, exponents, z_shift, x_degree))
    return tuple(columns), tuple(tags)


def legal_compound_basis(raw_columns, legal_monomials):
    illegal_rows = tuple(sorted({
        monomial
        for column in raw_columns
        for monomial, coefficient in column.items()
        if coefficient % P and monomial not in legal_monomials
    }))
    if illegal_rows:
        matrix = nmod_mat(len(illegal_rows), len(raw_columns), [
            column.get(row, 0) % P
            for row in illegal_rows
            for column in raw_columns
        ], P)
        kernel, nullity = matrix.nullspace()
    else:
        kernel = nmod_mat(len(raw_columns), len(raw_columns), P)
        for index in range(len(raw_columns)):
            kernel[index, index] = 1
        nullity = len(raw_columns)

    legal_sources = []
    nonzero_combinations = 0
    for basis_index in range(nullity):
        source = {}
        for column_index, column in enumerate(raw_columns):
            coefficient = int(kernel[column_index, basis_index]) % P
            if coefficient:
                add_scaled(source, column, coefficient)
        assert all(monomial in legal_monomials for monomial in source)
        if source:
            legal_sources.append(source)
            nonzero_combinations += 1
    return illegal_rows, nullity, tuple(legal_sources), nonzero_combinations


def one_multiplicity(m, slope=1, curvature=1):
    started = time.monotonic()
    print(f"[m={m}] build literal", file=sys.stderr, flush=True)
    case = (10, 4, 7, m, 7 * m, slope, curvature, m + 2, m + 6)
    literal = M.build_case(
        f"n10_full11_m{m}", case, actual_agreement_count=7,
        anchor_count=7, normal_coordinates=3,
        error_direction_offsets=OFFSETS)
    source_index = {
        monomial: index for index, monomial in enumerate(literal.monomials)
    }
    J, L = case[7], case[8]
    base = [
        literal.columns[index]
        for index, monomial in enumerate(literal.monomials)
        if sum(monomial[1:]) <= J
    ]
    print(f"[m={m}] echelon {len(base)} base columns", file=sys.stderr,
          flush=True)
    echelon = M.ColumnEchelon()
    for index, column in enumerate(base):
        echelon.add(column, ("base", index))
    base_rank = echelon.rank
    base_remainders = tuple(echelon.reduce(target)
                            for target in literal.targets)
    base_individual = tuple(int(bool(remainder))
                            for remainder in base_remainders)
    base_joint = M.modular_rank_sparse(base_remainders)

    raw_columns, tags = raw_full11_columns(literal, m, L - J)
    print(f"[m={m}] raw legality kernel on {len(raw_columns)} columns",
          file=sys.stderr, flush=True)
    illegal_rows, raw_kernel_nullity, legal_sources, nonzero = \
        legal_compound_basis(raw_columns, set(source_index))
    print(f"[m={m}] map/eliminate {len(legal_sources)} legal compounds",
          file=sys.stderr, flush=True)
    for index, source in enumerate(legal_sources):
        image = TT.indexed_image(literal, source, source_index)
        echelon.add(image, ("full11", index))
    cycle_rank = echelon.rank
    remainders = tuple(echelon.reduce(target) for target in literal.targets)
    individual = tuple(int(bool(remainder)) for remainder in remainders)
    joint = M.modular_rank_sparse(remainders)
    print(f"[m={m}] done in {time.monotonic() - started:.1f}s; defect={joint}",
          file=sys.stderr, flush=True)

    return {
        "parameters_n_w_g_m_D_s_t_J_L": case,
        "base_columns_rank": (len(base), base_rank),
        "base_individual_target_defects": base_individual,
        "base_joint_target_defect": base_joint,
        "full11_raw_columns": len(raw_columns),
        "full11_raw_column_tags": len(tags),
        "illegal_source_rows": len(illegal_rows),
        "raw_legality_kernel_nullity": raw_kernel_nullity,
        "nonzero_legal_compound_sources": nonzero,
        "legal_compound_contact_rank_gain": cycle_rank - base_rank,
        "after_full11_individual_target_defects": individual,
        "after_full11_joint_target_defect": joint,
    }


def main():
    M.PRIME = M.T.PRIME = M.F.PRIME = F.PRIME = P
    requested = []
    for value in sys.argv[1:]:
        parts = tuple(int(part) for part in value.split(","))
        if len(parts) == 1:
            requested.append((parts[0], 1, 1))
        elif len(parts) == 3:
            requested.append(parts)
        else:
            raise ValueError("arguments are m or m,slope,curvature")
    if not requested:
        requested = [(m, 1, 1) for m in MULTIPLICITIES]
    payload = {
        "scope": (
            "nonvacuous n10 finite target-quotient gate for the exact legal "
            "subspace of the raw full11 order-four covariant module"
        ),
        "field": P,
        "offsets": OFFSETS,
        "multiplier_degree_cap": MULTIPLIER_DEGREE,
        "results": tuple(one_multiplicity(m, slope, curvature)
                         for m, slope, curvature in requested),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(
        canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
