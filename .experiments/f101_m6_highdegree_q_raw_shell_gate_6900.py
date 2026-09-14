#!/usr/bin/env python3
"""High-degree-Q arbitrary-error test of the m6 raw Y/R/S connector.

This freezes the existing m6 J=8, L=12 chamber, but replaces Xi_E^2 by an
agreement polynomial of the maximal allowed degree g-1.  Its values are then
independently offset at all error nodes.  The exact four packets are reduced
modulo the legal grade-at-most-J prefix, followed by the first raw shell
groups (r,s)=(0,0),(1,0),(0,1), separately and in all subsets.

All ranks are coefficientwise over F_101.  No X-localization is used.
"""

from __future__ import annotations

import hashlib
from itertools import combinations
import json
from pathlib import Path
import resource
import sys
import time

sys.path.insert(0, ".experiments")
import asymmetric_second_jet_6900 as H  # noqa: E402
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402
import prime_o2_conormal_threshold_falsifier as T  # noqa: E402
import safe_terminal_subsource_surjectivity_audit_6900 as A  # noqa: E402
from higher_jet_literal_matrix import translated_column  # noqa: E402


P = 101
CASE = (10, 4, 7, 6, 42, 1, 1, 8, 12)
Q_H = (1, 1)
Q_COFACTOR = (1, 1)
ERROR_OFFSETS = (3, 5, 7)
RAW_SHAPES = ((0, 0), (1, 0), (0, 1))


def add_scaled(target, source, scale):
    for row, coefficient in source.items():
        value = (target.get(row, 0) + scale * coefficient) % P
        if value:
            target[row] = value
        else:
            target.pop(row, None)


def quotient_rank(columns):
    echelon = M.ColumnEchelon()
    for index, column in enumerate(columns):
        echelon.add(column, index)
    return echelon.rank


def quotient_defects(columns, targets):
    rank = quotient_rank(columns)
    individual = tuple(
        quotient_rank(columns + (target,)) - rank for target in targets)
    joint = quotient_rank(columns + targets) - rank
    return individual, joint


def build_literal():
    n, w, g, m, degree, slope, curvature, jet, seed = CASE
    actual_agreement = tuple(range(g))
    actual_error = tuple(range(g, n))
    anchors = tuple(range(w + 1))

    lambda_h = F.locator(anchors)
    q = F.poly_add(Q_H, F.poly_mul(lambda_h, Q_COFACTOR))
    assert len(q) - 1 == g - 1
    relative = F.poly_add(q, Q_H, -1)
    assert relative == F.poly_mul(lambda_h, Q_COFACTOR)
    assert len(relative) - 1 == g - 1 > w

    u0 = tuple(0 if node in actual_agreement else 1
               for node in range(n))
    polynomial_values = tuple(F.poly_eval(q, node) for node in range(n))
    u1 = list(polynomial_values)
    for node, offset in zip(actual_error, ERROR_OFFSETS):
        u1[node] = (u1[node] + offset) % P
    u1 = tuple(u1)
    assert u1[:g] == polynomial_values[:g]
    assert u1[g:] != polynomial_values[g:]
    assert all(u1)

    monomials = T.support(w, degree, slope, curvature, jet, seed)
    support_index = {monomial: index
                     for index, monomial in enumerate(monomials)}
    raw_columns = []
    for xp, y, r, s, z in monomials:
        column = {}
        for node in range(n):
            for local, coefficient in translated_column(
                    xp, (y, r, s), z, node, u0[node], u1[node],
                    m, 2, P).items():
                if coefficient:
                    column[("C", node, local)] = coefficient
        raw_columns.append(column)

    F.GAMMA = 0
    F.MULTIPLICITY = m
    locator_g = F.locator(actual_agreement)
    normals = list(F.centered_locator_normals(locator_g, (0,), q))
    q_h = T.interpolate(tuple(u1[node] for node in anchors), anchors)
    q_h = F.poly_trim(q_h)
    assert q_h == Q_H
    complement = tuple(node for node in actual_agreement
                       if node not in anchors)
    b = F.poly_mul(
        F.poly_pow(F.locator(anchors), m - 1),
        F.poly_pow(F.locator(complement), m))
    f3 = F.sparse_mul(
        F.sparse_embed_x(b),
        F.sparse_add(F.Y, F.sparse_mul(
            F.Z, F.sparse_embed_x(q_h)), -1))
    normals.append(f3)
    normals = tuple(normals)
    normal_missing = tuple(tuple(
        monomial for monomial in normal if monomial not in support_index)
        for normal in normals)
    assert not any(normal_missing)

    # Literal agreement-contact check before adding boundary rows.
    contact_supports = []
    for normal in normals:
        image = {}
        for monomial, coefficient in normal.items():
            add_scaled(image, raw_columns[support_index[monomial]], coefficient)
        assert not any(row[1] in actual_agreement for row in image)
        assert any(row[1] in actual_error for row in image)
        contact_supports.append(len(image))

    coupled_columns = []
    for monomial, contact in zip(monomials, raw_columns):
        column = dict(contact)
        xp, y, r, s, z = monomial
        shape = (y, r, s, z)
        if sum(shape) == 1:
            coordinate = shape.index(1)
            column[("J", coordinate, xp)] = 1
        coupled_columns.append(column)
    target_rows = tuple(M.exact_vertical_rows(normal, 4)
                        for normal in normals)
    all_rows = sorted(
        {row for column in coupled_columns for row in column}
        | {row for target in target_rows for row in target}, key=repr)
    row_index = {row: index for index, row in enumerate(all_rows)}
    columns = tuple({row_index[row]: coefficient
                     for row, coefficient in column.items()}
                    for column in coupled_columns)
    targets = tuple({row_index[row]: coefficient
                     for row, coefficient in target.items()}
                    for target in target_rows)
    return {
        "monomials": monomials,
        "columns": columns,
        "targets": targets,
        "q": q,
        "q_h": q_h,
        "relative": relative,
        "u1": u1,
        "polynomial_values": polynomial_values,
        "normal_support_sizes": tuple(map(len, normals)),
        "normal_contact_support_sizes": tuple(contact_supports),
        "row_count": len(all_rows),
        "support_index": support_index,
    }


def centered_carrier_legality(literal):
    _n, _w, _g, m, _degree, _q, _t, jet, _seed = CASE
    centered = F.sparse_add(
        F.Y, F.sparse_mul(F.Z, F.sparse_embed_x(literal["q"])), -1)
    rows = []
    for r, s in RAW_SHAPES:
        z = jet + 1 - m - r - s
        assert z >= 0
        carrier = F.sparse_mul(F.sparse_pow(centered, m),
                               F.sparse_pow(F.R, r))
        carrier = F.sparse_mul(carrier, F.sparse_pow(F.S, s))
        carrier = F.sparse_mul(carrier, F.sparse_pow(F.Z, z))
        missing = tuple(sorted(
            monomial for monomial in carrier
            if monomial not in literal["support_index"]))
        rows.append({
            "shape_r_s": (r, s),
            "formula": f"R^{r} S^{s} (Y-QZ)^{m} Z^{z}",
            "expanded_support_size": len(carrier),
            "source_legal": not missing,
            "missing_monomial_count": len(missing),
            "first_missing_monomials": missing[:4],
        })
    return tuple(rows)


def analyze(literal):
    monomials = literal["monomials"]
    columns = literal["columns"]
    targets = literal["targets"]
    jet = CASE[-2]
    prefix = tuple(index for index, monomial in enumerate(monomials)
                   if sum(monomial[1:]) <= jet)

    # The conservative affine-error safe test is explicit.  In this chamber
    # all three available derivative shapes are safe, so the deletion is
    # vacuous rather than silently omitted.
    case_dict = dict(zip(
        ("n", "w", "g", "m", "D", "q", "t", "J", "L"), CASE))
    case_dict["prime"] = P
    safe, unsafe, _ = A.safe_polytope(case_dict, CASE[0] - CASE[2])
    assert safe == RAW_SHAPES and unsafe == ()
    restricted_prefix = tuple(index for index in prefix)

    prefix_echelon = M.ColumnEchelon()
    for index in restricted_prefix:
        prefix_echelon.add(columns[index], index)
    residues = tuple(prefix_echelon.reduce(target) for target in targets)

    shell_groups = {}
    for index, monomial in enumerate(monomials):
        if sum(monomial[1:]) == jet + 1:
            shell_groups.setdefault((monomial[2], monomial[3]), []).append(
                index)
    shell_groups = {shape: tuple(indices)
                    for shape, indices in sorted(shell_groups.items())}
    assert set(shell_groups) == set(RAW_SHAPES)
    group_residues = {
        shape: tuple(prefix_echelon.reduce(columns[index])
                     for index in indices)
        for shape, indices in shell_groups.items()
    }

    subset_rows = []
    for size in range(1, len(RAW_SHAPES) + 1):
        for subset in combinations(RAW_SHAPES, size):
            source = tuple(residue for shape in subset
                           for residue in group_residues[shape])
            individual, joint = quotient_defects(source, residues)
            subset_rows.append({
                "raw_shell_shapes": subset,
                "column_count": sum(len(shell_groups[x]) for x in subset),
                "shell_quotient_rank": quotient_rank(source),
                "packet_individual_defects": individual,
                "packet_joint_defect": joint,
            })
    closing = tuple(row["raw_shell_shapes"] for row in subset_rows
                    if row["packet_joint_defect"] == 0)
    minimal = tuple(subset for subset in closing
                    if not any(set(other) < set(subset) for other in closing))

    full_echelon = M.ColumnEchelon()
    for index, column in enumerate(columns):
        full_echelon.add(column, index)
    full_residues = tuple(full_echelon.reduce(target) for target in targets)
    return {
        "safe_and_unsafe_terminal_shapes": (safe, unsafe),
        "safe_final_face_deletion_is_vacuous": not unsafe,
        "prefix_columns_and_rank": (len(restricted_prefix),
                                    prefix_echelon.rank),
        "packet_prefix_individual_nonzero": tuple(bool(x) for x in residues),
        "packet_prefix_quotient_rank": quotient_rank(residues),
        "first_shell_group_column_counts": tuple(
            (shape, len(indices)) for shape, indices in shell_groups.items()),
        "subset_rows": tuple(subset_rows),
        "inclusion_minimal_closing_shape_sets": minimal,
        "full_L12_columns_and_rank": (len(columns), full_echelon.rank),
        "full_L12_packet_individual_defects": tuple(
            bool(x) for x in full_residues),
        "full_L12_packet_joint_defect": quotient_rank(full_residues),
    }


def main():
    started = time.monotonic()
    M.PRIME = M.T.PRIME = M.F.PRIME = P
    F.PRIME = T.PRIME = P
    literal = build_literal()
    analysis = analyze(literal)
    stable = {
        "scope": (
            "predeclared coefficientwise F101 high-degree-Q arbitrary-error "
            "connector discriminator; finite control, not Full187"),
        "field": P,
        "parameters_n_w_g_m_D_q_t_J_L": CASE,
        "agreement_nodes_error_nodes_anchor_nodes": (
            tuple(range(7)), tuple(range(7, 10)), tuple(range(5))),
        "q_H_coefficients": literal["q_h"],
        "Q_coefficients": literal["q"],
        "degrees_Q_qH_QminusqH": (
            len(literal["q"]) - 1, len(literal["q_h"]) - 1,
            len(literal["relative"]) - 1),
        "Q_has_maximal_allowed_degree_g_minus_1": (
            len(literal["q"]) - 1 == CASE[2] - 1),
        "retained_bad_degree_exceeds_w": (
            len(literal["relative"]) - 1 > CASE[1]),
        "agreement_values_equal_Q": (
            literal["u1"][:7] == literal["polynomial_values"][:7]),
        "error_offsets_and_actual_values": (
            ERROR_OFFSETS, literal["u1"][7:]),
        "all_actual_U1_values_nonzero": all(literal["u1"]),
        "normal_support_and_error_contact_sizes": (
            literal["normal_support_sizes"],
            literal["normal_contact_support_sizes"]),
        "raw_centered_carrier_legality": centered_carrier_legality(literal),
        "analysis": analysis,
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    result = {
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(
            Path(__file__).read_bytes()).hexdigest(),
        "runtime": {
            "elapsed_seconds": round(time.monotonic() - started, 6),
            "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            "external_memory_cap_bytes": 4 * 1024**3,
        },
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
