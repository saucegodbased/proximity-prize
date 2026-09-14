#!/usr/bin/env python3
"""Nonvacuous forced-RHS quotient audit for order-four terminal carriers.

For n=10 with error-direction offsets (3,5,7), this script uses the cap-rich
nonvacuous chamber

    (n,w,g,m,D,s,t,J,L)=(10,5,7,5,35,2,1,8,12).

It reduces the actual F0/F1/F2 locator-normal RHS and every legal compound
order-four carrier source modulo the *complete* source of grade at most J.

The eleven centered covariants need not be individually source-legal in the
tight finite chamber.  For each tested family subset we therefore compute
the exact kernel of all illegal raw monomial coordinates first.  Its image
is the whole legal compound subspace, not a hand-picked lift.  Total source
grade separates passive Z shifts, so legality is solved once at grade J+1
and the resulting basis is shifted through all four terminal layers.

Three nested modules are compared:

* the eight Lambda/V/J1 families with J1 exponent at most one;
* all nine no-J2 families (adding J1^2);
* all eleven weighted-order-four families (adding Lambda*J2 and V*J2).

This is exact F101 evidence in finite chambers, not a Full187 theorem.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import f101_order4_osculating_covariant_basis_gate_6900 as O  # noqa: E402
import f101_terminal_seed_trellis_three_carrier_6900 as TT  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402


P = 101
OFFSETS = (3, 5, 7)
CASE = (10, 5, 7, 5, 35, 2, 1, 8, 12)
MULTIPLIER_DEGREES = tuple(range(9))  # deg p < 3e, e=3
SUBSETS = ("eight", "no_J2", "full11")


def add_scaled(target, source, scale=1):
    for row, coefficient in source.items():
        value = (target.get(row, 0) + scale * coefficient) % P
        if value:
            target[row] = value
        else:
            target.pop(row, None)


def dot(functional, column):
    return sum(functional.get(row, 0) * coefficient
               for row, coefficient in column.items()) % P


def shift_x(source, amount):
    return {
        (x + amount, y, r, s, z): coefficient
        for (x, y, r, s, z), coefficient in source.items()
    }


def shift_z(source, amount):
    return {
        (x, y, r, s, z + amount): coefficient
        for (x, y, r, s, z), coefficient in source.items()
    }


def centered_v(literal):
    return F.sparse_add(
        F.Y, F.sparse_mul(F.Z, F.sparse_embed_x(literal.q)), -1)


def subset_accepts(name, exponents):
    _a_lambda, _a_v, a_j1, a_j2 = exponents
    if name == "eight":
        return a_j2 == 0 and a_j1 <= 1
    if name == "no_J2":
        return a_j2 == 0
    if name == "full11":
        return True
    raise ValueError(name)


def raw_columns_at_first_layer(literal, case, subset, legal_monomials):
    m = case[3]
    prefactor = F.sparse_pow(centered_v(literal), m - 4)
    # weighted_order_four_families is homogenized to grade seven.  After the
    # V^(m-4) prefactor, add the unique seed power reaching grade J+1.
    extra_seed = case[7] - m - 2
    assert extra_seed >= 0
    columns = []
    tags = []
    family_names = []
    individual_legality = []
    for label, exponents, _active, _seed, order_four in \
            O.weighted_order_four_families(literal):
        if not subset_accepts(subset, exponents):
            continue
        family_names.append(label)
        carrier = F.sparse_mul(order_four, prefactor)
        carrier = shift_z(carrier, extra_seed)
        legal_degrees = []
        for degree in MULTIPLIER_DEGREES:
            column = shift_x(carrier, degree)
            columns.append(column)
            tags.append((label, exponents, degree))
            if all(monomial in legal_monomials for monomial in column):
                legal_degrees.append(degree)
        individual_legality.append((label, tuple(legal_degrees)))
    expected_families = {"eight": 8, "no_J2": 9, "full11": 11}[subset]
    assert len(family_names) == expected_families
    assert len(columns) == 9 * expected_families
    return (tuple(columns), tuple(tags), tuple(family_names),
            extra_seed, tuple(individual_legality))


def legal_compound_basis(raw_columns, legal_monomials):
    illegal_rows = tuple(sorted({
        monomial
        for column in raw_columns
        for monomial, coefficient in column.items()
        if coefficient % P and monomial not in legal_monomials
    }))
    illegal = nmod_mat(len(illegal_rows), len(raw_columns), [
        column.get(row, 0) % P
        for row in illegal_rows for column in raw_columns
    ], P)
    if illegal_rows:
        kernel, nullity = illegal.nullspace()
        illegal_rank = illegal.rank()
    else:
        kernel = nmod_mat(len(raw_columns), len(raw_columns), P)
        for index in range(len(raw_columns)):
            kernel[index, index] = 1
        nullity = len(raw_columns)
        illegal_rank = 0
    assert illegal_rank + nullity == len(raw_columns)

    basis_sources = []
    coefficient_supports = []
    zero_raw_relations = 0
    for basis_index in range(nullity):
        source = {}
        coefficient_support = []
        for column_index, column in enumerate(raw_columns):
            coefficient = int(kernel[column_index, basis_index]) % P
            if coefficient:
                coefficient_support.append((column_index, coefficient))
                add_scaled(source, column, coefficient)
        assert all(monomial in legal_monomials for monomial in source)
        if source:
            basis_sources.append(source)
            coefficient_supports.append(tuple(coefficient_support))
        else:
            zero_raw_relations += 1

    # Kernel images can still be linearly dependent after raw syzygies.  Use
    # exact source-coordinate rank, then let the contact quotient expose any
    # further loss.
    legal_source_rank = M.modular_rank_sparse(basis_sources)
    return {
        "illegal_rows": illegal_rows,
        "illegal_coordinate_rank": illegal_rank,
        "legality_kernel_dimension": nullity,
        "zero_raw_relations_in_kernel_basis": zero_raw_relations,
        "nonzero_basis_sources": tuple(basis_sources),
        "coefficient_supports": tuple(coefficient_supports),
        "legal_raw_source_rank": legal_source_rank,
    }


def target_defects(carrier_columns, target_remainders):
    carrier_rank = M.modular_rank_sparse(carrier_columns)
    individual = tuple(
        M.modular_rank_sparse(carrier_columns + [target]) - carrier_rank
        for target in target_remainders)
    joint = M.modular_rank_sparse(
        carrier_columns + list(target_remainders)) - carrier_rank
    return carrier_rank, individual, joint


def full11_dual_certificate(base_echelon, carrier_quotient_columns,
                            carrier_images, targets, target_remainders,
                            row_keys):
    """Three explicit independent duals annihilating base plus carriers."""
    carrier_echelon = M.ColumnEchelon()
    for index, column in enumerate(carrier_quotient_columns):
        carrier_echelon.add(column, index)
    reduced_targets = tuple(carrier_echelon.reduce(target)
                            for target in target_remainders)
    assert M.modular_rank_sparse(reduced_targets) == 3

    # Pick the first three coordinate rows whose evaluations on the reduced
    # targets are independent.  A free-row evaluation extends uniquely over
    # carrier pivots, then over base pivots, to annihilate both spaces.
    candidate_rows = tuple(sorted({row for target in reduced_targets
                                   for row in target}))
    row_echelon = M.ColumnEchelon()
    free_rows = []
    for row in candidate_rows:
        values = {index: target.get(row, 0)
                  for index, target in enumerate(reduced_targets)
                  if target.get(row, 0)}
        if row_echelon.add(values, row):
            free_rows.append(row)
        if len(free_rows) == 3:
            break
    assert len(free_rows) == 3

    functionals = []
    for free_row in free_rows:
        functional = {free_row: 1}
        for pivot in reversed(sorted(carrier_echelon.pivots)):
            value = -sum(
                coefficient * functional.get(row, 0)
                for row, coefficient in carrier_echelon.pivots[pivot].items()
                if row != pivot) % P
            if value:
                functional[pivot] = value
        for pivot in reversed(sorted(base_echelon.pivots)):
            value = -sum(
                coefficient * functional.get(row, 0)
                for row, coefficient in base_echelon.pivots[pivot].items()
                if row != pivot) % P
            if value:
                functional[pivot] = value
        assert all(dot(functional, column) == 0
                   for column in base_echelon.pivots.values())
        assert all(dot(functional, column) == 0
                   for column in carrier_images)
        functionals.append(functional)

    pairings = tuple(tuple(dot(functional, target) for target in targets)
                     for functional in functionals)
    pairing_matrix = nmod_mat(3, 3, [value for row in pairings for value in row], P)
    determinant = int(pairing_matrix.det()) % P
    assert determinant
    receipts = []
    for free_row, functional, pairing in zip(free_rows, functionals, pairings):
        support = tuple(sorted(
            ((row_keys[row], coefficient)
             for row, coefficient in functional.items()), key=repr))
        receipts.append({
            "free_quotient_row": row_keys[free_row],
            "functional_support": len(functional),
            "functional_sha256": hashlib.sha256(
                repr(support).encode()).hexdigest(),
            "values_on_F0_F1_F2": pairing,
        })
    return {
        "construction": (
            "three independent free rows after exact carrier reduction; "
            "back-substituted through carrier pivots then base pivots"
        ),
        "base_rank_annihilated": base_echelon.rank,
        "carrier_quotient_rank_annihilated": carrier_echelon.rank,
        "carrier_images_individually_checked": len(carrier_images),
        "functionals": tuple(receipts),
        "pairing_matrix": pairings,
        "pairing_determinant_mod_101": determinant,
    }


def audit_subset(literal, case, source_index, base_echelon,
                 targets, target_remainders, subset):
    m = case[3]
    raw_columns, tags, family_names, extra_seed, individual_legality = \
        raw_columns_at_first_layer(literal, case, subset, set(source_index))
    legality = legal_compound_basis(raw_columns, set(source_index))
    sources = legality.pop("nonzero_basis_sources")
    coefficient_supports = legality.pop("coefficient_supports")

    # Every raw term has grade J+1.  Distinct Z shifts therefore occupy
    # disjoint raw grades, so cross-shift cancellation of illegal monomials
    # is impossible and the one-layer legality kernel is exhaustive layerwise.
    assert all(sum(monomial[1:]) == case[7] + 1
               for source in raw_columns for monomial in source)

    accumulated_quotient = []
    accumulated_images = []
    layer_receipts = []
    previous_rank = 0
    for shift in range(case[8] - case[7]):
        shifted_sources = tuple(shift_z(source, shift) for source in sources)
        assert all(all(monomial in source_index for monomial in source)
                   for source in shifted_sources)
        images = tuple(
            TT.indexed_image(literal, source, source_index)
            for source in shifted_sources)
        # Legal compound order-four covariants are genuine agreement cycles.
        assert all(not any(
            literal.row_keys[row][0] == "C"
            and literal.row_keys[row][1] in literal.actual_agreement
            for row in image) for image in images)
        quotient = tuple(base_echelon.reduce(image) for image in images)
        accumulated_quotient.extend(quotient)
        accumulated_images.extend(images)
        rank, individual, joint = target_defects(
            accumulated_quotient, target_remainders)
        layer_receipts.append({
            "shift": shift,
            "source_grade": case[7] + 1 + shift,
            "legal_basis_sources": len(sources),
            "rank_increment_modulo_base": rank - previous_rank,
            "cumulative_carrier_quotient_rank": rank,
            "individual_F0_F1_F2_defects": individual,
            "joint_F0_F1_F2_defect": joint,
        })
        previous_rank = rank

    support_hash = hashlib.sha256(repr(tuple(
        tuple(sorted(source.items())) for source in sources)).encode()).hexdigest()
    coefficient_hash = hashlib.sha256(
        repr(coefficient_supports).encode()).hexdigest()
    result = {
        "subset": subset,
        "families": family_names,
        "extra_seed_to_grade_J_plus_1": extra_seed,
        "individually_legal_X_degrees_by_family": individual_legality,
        "raw_columns_at_one_layer": len(raw_columns),
        "raw_column_tags": len(tags),
        "illegal_source_rows_at_one_layer": len(legality["illegal_rows"]),
        "illegal_coordinate_rank": legality["illegal_coordinate_rank"],
        "legality_kernel_dimension": legality["legality_kernel_dimension"],
        "zero_raw_relations_in_kernel_basis":
            legality["zero_raw_relations_in_kernel_basis"],
        "nonzero_legal_basis_sources": len(sources),
        "legal_raw_source_rank": legality["legal_raw_source_rank"],
        "legal_basis_source_sha256": support_hash,
        "legality_kernel_coefficient_sha256": coefficient_hash,
        "layers": tuple(layer_receipts),
    }
    if subset == "full11":
        result["exact_three_dual_invariants"] = full11_dual_certificate(
            base_echelon, accumulated_quotient, accumulated_images,
            targets, target_remainders, literal.row_keys)
    return result


def one_case(case):
    m = case[3]
    literal = M.build_case(
        f"n10_full11_forced_rhs_m{m}", case,
        actual_agreement_count=7, anchor_count=7, normal_coordinates=3,
        error_direction_offsets=OFFSETS)
    source_index = {
        monomial: index for index, monomial in enumerate(literal.monomials)
    }
    base = [
        literal.columns[index]
        for index, monomial in enumerate(literal.monomials)
        if sum(monomial[1:]) <= case[7]
    ]
    base_echelon = M.ColumnEchelon()
    for index, column in enumerate(base):
        base_echelon.add(column, index)
    target_remainders = tuple(
        base_echelon.reduce(target) for target in literal.targets)
    target_quotient_rank = M.modular_rank_sparse(target_remainders)
    base_individual = tuple(1 if target else 0 for target in target_remainders)
    assert target_quotient_rank == M.modular_rank_sparse(
        base + list(literal.targets)) - base_echelon.rank

    subset_rows = []
    for subset in SUBSETS:
        subset_rows.append(audit_subset(
            literal, case, source_index, base_echelon,
            literal.targets, target_remainders, subset))
        print("finished subset", subset, "case", case, file=sys.stderr,
              flush=True)
    subsets = tuple(subset_rows)
    return {
        "parameters_n_w_g_m_D_s_t_J_L": case,
        "literal_source_columns": len(literal.monomials),
        "base_columns_rank": (len(base), base_echelon.rank),
        "base_individual_F0_F1_F2_defects": base_individual,
        "base_joint_F0_F1_F2_defect": target_quotient_rank,
        "target_remainder_supports": tuple(len(target)
                                           for target in target_remainders),
        "target_remainders_sha256": hashlib.sha256(
            repr(tuple(tuple(sorted(target.items()))
                       for target in target_remainders)).encode()).hexdigest(),
        "modules": subsets,
    }


def main():
    started = time.monotonic()
    M.PRIME = M.T.PRIME = M.F.PRIME = O.T.PRIME = O.F.PRIME = F.PRIME = P
    payload = {
        "scope": (
            "exact nonvacuous F0/F1/F2 quotient containment in the complete "
            "legal order-four compound modules; finite F101 chambers only"
        ),
        "field": P,
        "error_direction_offsets": OFFSETS,
        "coefficient_degree_bound": "deg p < 3e = 9",
        "case": one_case(CASE),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["runtime_receipt"] = {
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "external_address_and_rss_cap_bytes": 4294967296,
    }
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
