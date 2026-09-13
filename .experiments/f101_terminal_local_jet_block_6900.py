#!/usr/bin/env python3
"""Exact local/finite gate for the terminal three-carrier jet block.

This is deliberately a diagnostic companion to
``f101_terminal_seed_trellis_three_carrier_6900.py``.  It checks which clean
carrier multipliers fit the literal F101 source, how their images sit modulo
the grade-at-most-six image, and whether value jets or one further Hasse layer
are needed to close the three fixed locator right-hand sides.
"""

from __future__ import annotations

import json
import sys
from itertools import combinations
import hashlib

sys.path.insert(0, ".experiments")
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import f101_terminal_seed_trellis_three_carrier_6900 as S  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402
import prime_o2_conormal_threshold_falsifier as T  # noqa: E402


P = 101
PRIMARY = (11, 5, 8, 4, 32, 1, 1, 6, 10)


def x_power(exponent):
    return (0,) * exponent + (1,)


def clean_carrier(kind, multiplier, literal):
    """Return one of c*V^m, C*Lambda*V^(m-1), A*Xi*V^(m-2)*J1."""
    m = PRIMARY[3]
    b = PRIMARY[7] + 1 - m
    v = F.sparse_add(
        F.Y, F.sparse_mul(F.Z, F.sparse_embed_x(literal.q)), -1)
    q1 = F.poly_derivative(literal.q)
    v1 = F.sparse_add(
        F.R, F.sparse_mul(F.Z, F.sparse_embed_x(q1)), -1)
    coefficient = F.sparse_embed_x(multiplier)
    if kind == "c":
        core = F.sparse_pow(v, m)
        zpower = b
    elif kind == "C":
        coefficient = F.sparse_mul(
            coefficient, F.sparse_embed_x(literal.locator))
        core = F.sparse_pow(v, m - 1)
        zpower = b + 1
    elif kind == "A":
        coefficient = F.sparse_mul(
            coefficient, F.sparse_embed_x(literal.xi))
        locator1 = F.poly_derivative(literal.locator)
        j1 = F.sparse_add(
            F.sparse_mul(F.sparse_embed_x(literal.locator), v1),
            F.sparse_mul(F.sparse_embed_x(locator1), v), -1)
        core = F.sparse_mul(F.sparse_pow(v, m - 2), j1)
        zpower = b + 1
    else:
        raise ValueError(kind)
    return F.sparse_mul(
        F.sparse_mul(coefficient, core), F.sparse_pow(F.Z, zpower))


def image(literal, source, source_index):
    out = {}
    for monomial, coefficient in source.items():
        assert monomial in source_index, (monomial, source)
        S.add_scaled(out, literal.columns[source_index[monomial]], coefficient)
    return out


def defects(echelon, targets):
    return tuple(0 if not echelon.reduce(target) else 1 for target in targets)


def row_label(literal, indexed_row):
    return literal.row_keys[indexed_row]


def span_receipt(literal, base_indices, columns, name):
    echelon = M.ColumnEchelon()
    for index in base_indices:
        echelon.add(literal.columns[index], ("base", index))
    gains = 0
    for label, column in columns:
        gains += int(echelon.add(column, label))
    return {
        "name": name,
        "columns": len(columns),
        "rank_gain_mod_base": gains,
        "defects": defects(echelon, literal.targets),
    }


def minimal_clean_subsets(literal, base_indices, clean_columns):
    """Find the first exact clean-column subsets containing all three RHS."""
    base = M.ColumnEchelon()
    for index in base_indices:
        base.add(literal.columns[index], ("base", index))
    labels = sorted(clean_columns, key=lambda item: (item[1], item[0]))
    reduced = {label: base.reduce(clean_columns[label]) for label in labels}
    reduced_targets = [base.reduce(target) for target in literal.targets]
    target_rank = M.modular_rank_sparse(reduced_targets)
    assert target_rank == 3

    # Restrict to a set of row evaluations which is injective on the entire
    # clean span.  This compresses the quotient vectors from dozens of J rows
    # to their exact rank (twelve) before the combinatorial search.
    all_rows = sorted({row for column in reduced.values() for row in column})
    row_echelon = M.ColumnEchelon()
    selected_rows = []
    for row in all_rows:
        row_vector = {index: reduced[label].get(row, 0)
                      for index, label in enumerate(labels)
                      if reduced[label].get(row, 0)}
        if row_echelon.add(row_vector, row):
            selected_rows.append(row)
    clean_rank = row_echelon.rank
    assert clean_rank == M.modular_rank_sparse(list(reduced.values())) == 12

    def compress(column):
        return {index: column.get(row, 0)
                for index, row in enumerate(selected_rows)
                if column.get(row, 0)}

    reduced = {label: compress(column) for label, column in reduced.items()}
    reduced_targets = [compress(target) for target in reduced_targets]
    assert M.modular_rank_sparse(
        list(reduced.values()) + reduced_targets) == clean_rank
    for size in range(3, len(labels) + 1):
        witnesses = []
        for subset in combinations(labels, size):
            columns = [reduced[label] for label in subset]
            rank = M.modular_rank_sparse(columns)
            if M.modular_rank_sparse(columns + reduced_targets) == rank:
                witnesses.append(subset)
                if len(witnesses) == 8:
                    break
        if witnesses:
            return {
                "compressed_clean_quotient_rank": clean_rank,
                "number_of_separating_rows": len(selected_rows),
                "minimum_number_of_clean_columns": size,
                "first_witnesses": tuple(witnesses),
            }
    raise AssertionError("full clean span was already checked to close")


def main():
    M.PRIME = M.F.PRIME = M.T.PRIME = P
    F.PRIME = P
    F.GAMMA = 0
    F.MULTIPLICITY = PRIMARY[3]
    literal = M.build_case("primary_n11", PRIMARY, 8, 8, 3)
    source_index = {monomial: index
                    for index, monomial in enumerate(literal.monomials)}
    base_indices = [index for index, monomial in enumerate(literal.monomials)
                    if sum(monomial[1:]) <= PRIMARY[7]]
    echelon = M.ColumnEchelon()
    for index in base_indices:
        echelon.add(literal.columns[index], ("base", index))
    assert echelon.rank == 1461

    # First inspect the exact canonical closing columns modulo the lower image.
    canonical_remainders = []
    for normal, (a_coeffs, b_coeffs, c_coeffs) in zip(S.NAMES, S.ABC):
        source = S.terminal_source(
            a_coeffs, b_coeffs, c_coeffs,
            literal.xi, literal.q, literal.locator,
            PRIMARY[3], PRIMARY[7])
        column = image(literal, source, source_index)
        remainder = echelon.reduce(column)
        assert remainder
        pivot = min(remainder)
        assert all(row_label(literal, row)[0] == "J" for row in remainder)
        canonical_remainders.append({
            "normal": normal,
            "remainder_support": len(remainder),
            "pivot": row_label(literal, pivot),
            "pivot_coefficient": remainder[pivot],
            "remainder_only_J_rows": True,
            "contact_rows_by_node": tuple(sorted({
                row_label(literal, row)[1]
                for row in remainder
                if row_label(literal, row)[0] == "C"
            })),
        })
        assert echelon.add(column, ("canonical", normal))
    assert echelon.rank == 1464
    assert defects(echelon, literal.targets) == (0, 0, 0)

    # Restart and add every individually legal clean carrier in increasing
    # multiplier degree.  This measures how many global coefficient jets the
    # literal finite model actually needs.
    echelon = M.ColumnEchelon()
    for index in base_indices:
        echelon.add(literal.columns[index], ("base", index))
    legal = {kind: [] for kind in ("c", "C", "A")}
    clean_columns = {}
    illegal_first = {}
    additions = []
    for degree in range(16):
        for kind in ("c", "C", "A"):
            source = clean_carrier(kind, x_power(degree), literal)
            if F.source_legal(source):
                assert all(sum(monomial[1:]) == PRIMARY[7] + 1
                           for monomial in source)
                column = image(literal, source, source_index)
                # Each clean carrier is an exact agreement cycle and has no
                # exact vertical rows.
                assert not any(
                    literal.row_keys[row][0] == "C"
                    and literal.row_keys[row][1] in literal.actual_agreement
                    for row in column)
                assert not any(literal.row_keys[row][0] == "J"
                               for row in column)
                legal[kind].append(degree)
                clean_columns[kind, degree] = column
                rank_before = echelon.rank
                independent = echelon.add(column, (kind, degree))
                additions.append({
                    "kind": kind,
                    "degree": degree,
                    "independent_mod_prefix": independent,
                    "rank_increment": echelon.rank - rank_before,
                    "rank": echelon.rank,
                    "defects": defects(echelon, literal.targets),
                })
            elif kind not in illegal_first:
                illegal_first[kind] = degree

    def selected(kind, stop):
        return [((kind, degree), clean_columns[kind, degree])
                for degree in legal[kind] if degree < stop]

    e = len(literal.xi) - 1
    subset_receipts = []
    for kind in ("c", "C", "A"):
        subset_receipts.append(span_receipt(
            literal, base_indices, selected(kind, 99),
            f"all legal {kind}"))
    subset_receipts.extend((
        span_receipt(
            literal, base_indices,
            selected("c", e) + selected("C", e) + selected("A", e),
            "value interpolation: degree < e for all three"),
        span_receipt(
            literal, base_indices,
            selected("c", 2 * e) + selected("C", 2 * e)
            + selected("A", 2 * e),
            "two Hermite layers, truncated only by literal legality"),
        span_receipt(
            literal, base_indices,
            selected("C", 2 * e),
            "C value+first-derivative interpolation only"),
        span_receipt(
            literal, base_indices,
            selected("c", e) + selected("C", 2 * e)
            + selected("A", e),
            "c,A values plus C value+first derivative"),
    ))

    payload = {
        "field": P,
        "primary_parameters": PRIMARY,
        "base_columns_rank": (len(base_indices), 1461),
        "canonical_terminal_remainders": canonical_remainders,
        "clean_carrier_legal_multiplier_degrees": {
            kind: tuple(degrees) for kind, degrees in legal.items()
        },
        "first_illegal_multiplier_degree": illegal_first,
        "clean_addition_trace": additions,
        "clean_subset_receipts": subset_receipts,
        "minimal_clean_subset_search": minimal_clean_subsets(
            literal, base_indices, clean_columns),
        "final_clean_rank": echelon.rank,
        "final_clean_defects": defects(echelon, literal.targets),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"),
                           default=repr)
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True, default=repr))


if __name__ == "__main__":
    main()
