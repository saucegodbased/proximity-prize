#!/usr/bin/env python3
"""Extract a compact low-head/final-three certificate in the F101 m8 gate.

This chains from the faithful old-boundary basis certified by
``k0_corrected_terminal_connecting_transpose_gate_6900.py``.  It rebuilds
only the low head (ordinary epsilon orders 0,...,4), groups source columns by
raw derivative shape, and extracts a canonical head-kernel relation whose
boundary escapes the old complete-kernel image.

The compact invariant is the nonzero 4x4 determinant formed by the three old
boundary-image basis vectors and this one head witness.  The complete contact
of the witness is checked to be supported only in the final three epsilon
orders 5,6,7.  This is an exact finite certificate, not a target theorem or a
claim that the dense source relation is support-minimal among all bases.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import asdict, replace
import gc
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat, nmod_poly

sys.path.insert(0, ".experiments")
import k0_capacity_positive_layer_attribution_6900 as Layer  # noqa: E402
import k0_corrected_terminal_connecting_transpose_gate_6900 as Gate  # noqa: E402
import k0_degree4_degree5_full_sr_attribution_6900 as Degree  # noqa: E402


P = Gate.P
ADDRESS_SPACE_CAP_BYTES = Gate.ADDRESS_SPACE_CAP_BYTES
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
if soft < 0 or soft > ADDRESS_SPACE_CAP_BYTES:
    resource.setrlimit(resource.RLIMIT_AS,
                       (ADDRESS_SPACE_CAP_BYTES, hard))


# Certified by primary case hash
# 91ada844e33bdda7fc8b51046dbbf230ed38022920ba36bf04283d5cf15fe6b6.
OLD_COMPLETE_BOUNDARY_BASIS = (
    (1, 36, 0, 68),
    (0, 1, 0, 13),
    (0, 0, 1, 19),
)


def annihilator(vectors):
    matrix = nmod_mat([list(vector) for vector in vectors], P)
    kernel, nullity = matrix.nullspace()
    assert nullity == 1
    value = tuple(int(kernel[i, 0]) % P for i in range(4))
    pivot = next(entry for entry in value if entry)
    inverse = pow(pivot, -1, P)
    return tuple(entry * inverse % P for entry in value)


def pairing(left, right):
    return sum(a * b for a, b in zip(left, right)) % P


def relation_boundary(matrix, pivots, column, boundaries):
    value = list(boundaries[column])
    support_count = 1
    relation = {column: 1}
    for row, pivot_column in enumerate(pivots):
        coefficient = int(matrix[row, column]) % P
        if coefficient:
            support_count += 1
            relation[pivot_column] = (-coefficient) % P
            old = boundaries[pivot_column]
            value = [(entry - coefficient * old[i]) % P
                     for i, entry in enumerate(value)]
    return tuple(value), support_count, relation


def apply_contact(relation, profile, receipt):
    answer = {}
    for column, coefficient in relation.items():
        monomial = MONOMIALS[column]
        for row, value in Gate.formal_column(
                profile, receipt, monomial).items():
            updated = (answer.get(row, 0) + coefficient * value) % P
            if updated:
                answer[row] = updated
            else:
                answer.pop(row, None)
    return answer


def determinant(rows):
    matrix = nmod_mat([list(row) for row in rows], P)
    return int(matrix.det()) % P


def all_node_locator(nodes):
    x = nmod_poly([0, 1], P)
    answer = nmod_poly([1], P)
    for node in nodes:
        answer *= x - node
    return answer


MONOMIALS = ()


def main():
    global MONOMIALS
    started = time.monotonic()
    profile = replace(Degree.PROFILE, L=10)
    receipt = Degree.Full.M8.monomial_tangent_receipt(
        profile, Degree.TRIAL, 0)
    source = tuple(Degree.K0.support(profile))
    group_specs = (
        ("raw", (0, 0)),
        ("R1", (1, 0)),
        ("S1", (0, 1)),
        ("R2", (2, 0)),
        ("R3", (3, 0)),
        ("RS", (1, 1)),
    )
    grouped = tuple(tuple(q for q in source if (q[2], q[3]) == shape)
                    for _name, shape in group_specs)
    MONOMIALS = sum(grouped, ())
    assert len(MONOMIALS) == len(source) == 11178
    assert tuple(len(group) for group in grouped) == (
        2508, 2035, 2090, 1620, 1260, 1665)
    group_of = {}
    group_ends = {}
    offset = 0
    for (name, _shape), group in zip(group_specs, grouped):
        for index in range(offset, offset + len(group)):
            group_of[index] = name
        offset += len(group)
        group_ends[offset] = name

    # Re-run all primitive/map normalizations before extracting a relation.
    sanity = Gate.semantic_sanity(profile, receipt, MONOMIALS)
    terminal_base = profile.m - 3
    head_rows_set = set()
    for position, monomial in enumerate(MONOMIALS, start=1):
        head_rows_set.update(
            row for row in Gate.formal_column(profile, receipt, monomial)
            if row[1] < terminal_base)
        if position % 1000 == 0:
            print(f"row pass {position}/{len(MONOMIALS)}",
                  file=sys.stderr, flush=True)
    head_rows = tuple(sorted(head_rows_set, key=repr))
    row_index = {row: i for i, row in enumerate(head_rows)}
    boundaries = tuple(Gate.formal_boundary(profile, receipt, monomial)
                       for monomial in MONOMIALS)
    matrix = nmod_mat(len(head_rows), len(MONOMIALS), P)
    for column, monomial in enumerate(MONOMIALS):
        for row, value in Gate.formal_column(
                profile, receipt, monomial).items():
            i = row_index.get(row)
            if i is not None:
                matrix[i, column] = value
        if (column + 1) % 1000 == 0:
            print(f"fill {column + 1}/{len(MONOMIALS)}",
                  file=sys.stderr, flush=True)
    print(f"rref low head: {matrix.nrows()}x{matrix.ncols()}",
          file=sys.stderr, flush=True)
    _, rank = matrix.rref(inplace=True)
    pivots = Layer.pivot_columns(matrix, rank)
    pivot_set = set(pivots)

    ell = annihilator(OLD_COMPLETE_BOUNDARY_BASIS)
    assert ell == (1, 79, 30, 25)
    assert all(pairing(ell, vector) == 0
               for vector in OLD_COMPLETE_BOUNDARY_BASIS)

    normal_basis = {}
    contact_rank = 0
    first_gains = []
    family_stages = []
    first_escape = None
    sparsest_canonical_escape = None
    for column in range(len(MONOMIALS)):
        if column in pivot_set:
            contact_rank += 1
        else:
            boundary, support_count, relation = relation_boundary(
                matrix, pivots, column, boundaries)
            escaped = pairing(ell, boundary)
            if Gate.add_boundary_basis(normal_basis, boundary):
                first_gains.append({
                    "gain": len(normal_basis),
                    "column_zero_based": column,
                    "family": group_of[column],
                    "monomial_X_Y_R_S_Z": MONOMIALS[column],
                    "canonical_relation_support_size": support_count,
                    "boundary_Y_R_S_Z": boundary,
                    "old_conormal_pairing": escaped,
                })
            if escaped:
                candidate = (support_count, column, boundary, escaped,
                             relation)
                if first_escape is None:
                    first_escape = candidate
                if (sparsest_canonical_escape is None or
                        candidate[:2] < sparsest_canonical_escape[:2]):
                    sparsest_canonical_escape = candidate
        position = column + 1
        if position in group_ends:
            family_stages.append({
                "completed_family": group_ends[position],
                "columns_contact_rank_nullity_boundary_gain": (
                    position, contact_rank, position - contact_rank,
                    len(normal_basis)),
            })
    assert contact_rank == rank == 4734
    assert len(normal_basis) == 4
    assert first_escape is not None and sparsest_canonical_escape is not None

    def witness_receipt(candidate):
        support_count, column, boundary, escaped, relation = candidate
        support = tuple(sorted((index, coefficient)
                               for index, coefficient in relation.items()
                               if coefficient % P))
        assert len(support) == support_count
        contact = apply_contact(relation, profile, receipt)
        head = {row: value for row, value in contact.items()
                if row[1] < terminal_base}
        terminal = {row: value for row, value in contact.items()
                    if row[1] >= terminal_base}
        assert not head
        assert terminal
        terminal_orders = Counter(row[1] for row in terminal)
        boundary_check = [0, 0, 0, 0]
        for index, coefficient in support:
            for coordinate, value in enumerate(boundaries[index]):
                boundary_check[coordinate] = (
                    boundary_check[coordinate] + coefficient * value) % P
        assert tuple(boundary_check) == boundary
        det = determinant(OLD_COMPLETE_BOUNDARY_BASIS + (boundary,))
        assert det != 0
        assert escaped != 0
        assert all(MONOMIALS[index][1:] == (0, 0, 0, 1)
                   for index, _coefficient in support)
        max_x = max(MONOMIALS[index][0] for index, _ in support)
        polynomial_coefficients = [0] * (max_x + 1)
        for index, coefficient in support:
            polynomial_coefficients[MONOMIALS[index][0]] = coefficient
        polynomial = nmod_poly(polynomial_coefficients, P)
        locator_power = all_node_locator(receipt.nodes) ** terminal_base
        quotient, remainder = divmod(polynomial, locator_power)
        assert remainder.is_zero()
        return {
            "column_zero_based": column,
            "family": group_of[column],
            "monomial_X_Y_R_S_Z": MONOMIALS[column],
            "canonical_relation_support_size": support_count,
            "canonical_relation_support_by_family": tuple(sorted(
                Counter(group_of[index] for index, _ in support).items())),
            "canonical_relation_sha256": hashlib.sha256(
                repr(support).encode()).hexdigest(),
            "first_16_index_coefficient_monomial": tuple(
                (index, coefficient, MONOMIALS[index])
                for index, coefficient in support[:16]),
            "boundary_Y_R_S_Z": boundary,
            "old_conormal_Y_R_S_Z": ell,
            "old_conormal_pairing": escaped,
            "old_basis_plus_witness_determinant": det,
            "pure_XZ_polynomial_degree": polynomial.degree(),
            "all_node_locator_power_and_degree": (
                terminal_base, locator_power.degree()),
            "exact_locator_quotient_coefficients": tuple(int(c)
                for c in quotient.coeffs()),
            "exactly_divisible_by_Omega_nodes_pow_mminus3": True,
            "head_contact_residual_empty": True,
            "terminal_nonzero_rows": len(terminal),
            "terminal_support_by_epsilon_order": tuple(sorted(
                terminal_orders.items())),
            "terminal_vector_sha256": hashlib.sha256(
                repr(tuple(sorted(terminal.items(), key=repr))).encode()
            ).hexdigest(),
        }

    first_receipt = witness_receipt(first_escape)
    sparse_receipt = witness_receipt(sparsest_canonical_escape)
    assert first_receipt["old_basis_plus_witness_determinant"] != 0
    assert sparse_receipt["old_basis_plus_witness_determinant"] != 0

    stable = {
        "scope": (
            "exact canonical low-head witness and 4x4 terminal-detector "
            "minor in the faithful F101 m8 chamber"),
        "field": P,
        "profile_n_w_g_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "agreement_set": receipt.agreement,
        "semantic_sanity": sanity,
        "head_and_terminal_epsilon_orders": (
            tuple(range(terminal_base)),
            tuple(range(terminal_base, profile.m))),
        "group_order_shapes_counts": tuple(
            (name, shape, len(group))
            for (name, shape), group in zip(group_specs, grouped)),
        "head_rows_columns_rank_nullity_boundary_gain": (
            len(head_rows), len(MONOMIALS), rank,
            len(MONOMIALS) - rank, len(normal_basis)),
        "family_stages": tuple(family_stages),
        "first_independent_boundary_gains": tuple(first_gains),
        "chained_old_complete_boundary_basis_Y_R_S_Z":
            OLD_COMPLETE_BOUNDARY_BASIS,
        "chained_old_boundary_conormal_Y_R_S_Z": ell,
        "first_canonical_escape_witness": first_receipt,
        "sparsest_escape_among_canonical_nonpivot_relations": sparse_receipt,
        "minimality_guard": (
            "sparsest means only among the canonical one-free-column RREF "
            "relations in the declared family order; it is not global "
            "support minimality"),
        "verdict": (
            "GREEN finite minor: an explicit low-head kernel relation has "
            "terminal-only complete contact and completes the certified old "
            "boundary image to Boundary4"),
        "scope_guard": (
            "The source relation is finite and receipt-specific. The 4x4 "
            "minor is not a symbolic target recurrence or target-uniform "
            "nonvanishing theorem."),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    payload = {
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(
            Path(__file__).read_bytes()).hexdigest(),
        "runtime": {
            "seconds": round(time.monotonic() - started, 3),
            "peak_rss_kib": resource.getrusage(
                resource.RUSAGE_SELF).ru_maxrss,
            "hard_address_space_cap_bytes": ADDRESS_SPACE_CAP_BYTES,
        },
    }
    print(json.dumps(payload, indent=2, sort_keys=True))
    del matrix
    gc.collect()


if __name__ == "__main__":
    main()
