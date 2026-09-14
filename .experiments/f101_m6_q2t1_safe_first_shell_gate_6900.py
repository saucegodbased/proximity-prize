#!/usr/bin/env python3
"""q:t=2:1, target-weight, nonvacuous-safe-deletion connector gate.

This is the smallest direct extension of the green m6 raw-shell control that
simultaneously has:

* n=2w+2 and a retained-bad maximal agreement degree g-1>w;
* q:t=2:1 and J/m close to 82/60;
* arbitrary off-polynomial error values; and
* a genuinely unsafe first-shell terminal slice under the strong affine-error
  safe criterion.

It checks the exact four packet columns coefficientwise over F_101, both with
and without all noncandidate q=2 shell branches in the background, and both
with the unsafe slice deleted and restored.  No localization is used.
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
import f101_m6_highdegree_q_raw_shell_gate_6900 as G  # noqa: E402
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402
import prime_o2_conormal_threshold_falsifier as T  # noqa: E402
import safe_terminal_subsource_surjectivity_audit_6900 as A  # noqa: E402


P = 101
CASE = (10, 4, 6, 6, 36, 2, 1, 8, 9)
Q_H = (1, 1)
Q_COFACTOR = (1,)
ERROR_OFFSETS = (3, 5, 7, 11)
CANDIDATE_SHAPES = ((0, 0), (1, 0), (0, 1))


def rank_and_defects(columns, targets):
    # One echelon suffices: reduce all four targets through it, then only the
    # at-most-four residual target columns need a second tiny rank.  Rebuilding
    # the source echelon once per target is mathematically identical but much
    # slower in the q=2 background screens.
    echelon = M.ColumnEchelon()
    for index, column in enumerate(columns):
        echelon.add(column, index)
    residues = tuple(echelon.reduce(target) for target in targets)
    individual = tuple(int(bool(residue)) for residue in residues)
    joint = G.quotient_rank(residues)
    return echelon.rank, individual, joint


def background_screen(prefix_echelon, prefix_targets, prefix_shell,
                      shell_groups, background_indices, label):
    background = M.ColumnEchelon()
    for index in background_indices:
        background.add(prefix_shell[index], index)
    targets = tuple(background.reduce(target) for target in prefix_targets)
    candidate_residues = {
        shape: tuple(background.reduce(prefix_shell[index])
                     for index in shell_groups[shape])
        for shape in CANDIDATE_SHAPES
    }
    rows = []
    for size in range(len(CANDIDATE_SHAPES) + 1):
        for subset in combinations(CANDIDATE_SHAPES, size):
            columns = tuple(column for shape in subset
                            for column in candidate_residues[shape])
            quotient_rank, individual, joint = rank_and_defects(
                columns, targets)
            rows.append({
                "candidate_shapes": subset,
                "candidate_column_count": sum(
                    len(shell_groups[shape]) for shape in subset),
                "candidate_quotient_rank_over_background": quotient_rank,
                "packet_individual_defects": individual,
                "packet_joint_defect": joint,
            })
    closing = tuple(row["candidate_shapes"] for row in rows
                    if row["packet_joint_defect"] == 0)
    minimal = tuple(subset for subset in closing
                    if not any(set(other) < set(subset) for other in closing))
    return {
        "label": label,
        "background_column_count": len(background_indices),
        "background_quotient_rank": background.rank,
        "absolute_prefix_plus_background_rank": (
            prefix_echelon.rank + background.rank),
        "packet_quotient_rank_before_candidates": G.quotient_rank(targets),
        "subset_rows": tuple(rows),
        "inclusion_minimal_closing_candidate_sets": minimal,
    }


def main():
    started = time.monotonic()
    M.PRIME = M.T.PRIME = M.F.PRIME = P
    F.PRIME = T.PRIME = P

    # Reuse the audited literal constructor with only these frozen globals
    # changed.  The constructor itself checks exact F0..F3 source membership
    # and zero agreement contact.
    G.CASE = CASE
    G.Q_H = Q_H
    G.Q_COFACTOR = Q_COFACTOR
    G.ERROR_OFFSETS = ERROR_OFFSETS
    G.RAW_SHAPES = CANDIDATE_SHAPES
    literal = G.build_literal()

    n, w, g, m, degree, q, t, jet, seed = CASE
    assert n == 2 * w + 2
    assert (q, t) == (2, 1)
    assert abs(jet / m - 82 / 60) < 0.04
    assert len(literal["q"]) - 1 == g - 1 > w
    assert len(literal["relative"]) - 1 == g - 1 > w

    case_dict = {
        "prime": P, "n": n, "w": w, "g": g, "m": m,
        "D": degree, "q": q, "t": t, "J": jet, "L": seed,
    }
    safe, unsafe, corner = A.safe_polytope(
        case_dict, required_margin=n - g)
    assert safe == ((0, 0), (1, 0), (2, 0), (0, 1))
    assert unsafe == ((1, 1),)
    assert corner[(1, 1)] == ((1, 0, 1),)

    monomials = literal["monomials"]
    columns = literal["columns"]
    targets = literal["targets"]
    prefix_indices = tuple(
        index for index, monomial in enumerate(monomials)
        if sum(monomial[1:]) <= jet)
    shell_indices = tuple(
        index for index, monomial in enumerate(monomials)
        if sum(monomial[1:]) == jet + 1)
    assert len(prefix_indices) == 4140
    assert len(shell_indices) == 751

    prefix_echelon = M.ColumnEchelon()
    for index in prefix_indices:
        prefix_echelon.add(columns[index], index)
    prefix_targets = tuple(prefix_echelon.reduce(target)
                           for target in targets)
    prefix_shell = {
        index: prefix_echelon.reduce(columns[index])
        for index in shell_indices
    }
    shell_groups = {}
    for index in shell_indices:
        monomial = monomials[index]
        shell_groups.setdefault((monomial[2], monomial[3]), []).append(index)
    shell_groups = {shape: tuple(indices)
                    for shape, indices in sorted(shell_groups.items())}
    assert set(shell_groups) == set(safe) | set(unsafe)

    def deleted(index):
        _xp, y, r, s, z = monomials[index]
        return (y + r + s == jet and y + r + s + z == seed
                and (r, s) in unsafe)

    deleted_indices = tuple(index for index in shell_indices if deleted(index))
    assert len(deleted_indices) == 7
    assert all((monomials[index][2], monomials[index][3]) == (1, 1)
               and monomials[index][1:] == (
                   6, 1, 1, 1) for index in deleted_indices)

    noncandidate = tuple(index for index in shell_indices
                         if (monomials[index][2], monomials[index][3])
                         not in CANDIDATE_SHAPES)
    safe_noncandidate = tuple(index for index in noncandidate
                              if not deleted(index))
    full_noncandidate = noncandidate
    assert len(noncandidate) == 259
    assert len(safe_noncandidate) == 252

    screens = (
        background_screen(
            prefix_echelon, prefix_targets, prefix_shell, shell_groups,
            (), "isolated_candidate_groups"),
        background_screen(
            prefix_echelon, prefix_targets, prefix_shell, shell_groups,
            safe_noncandidate,
            "target_faithful_q2_background_with_unsafe_slice_deleted"),
        background_screen(
            prefix_echelon, prefix_targets, prefix_shell, shell_groups,
            full_noncandidate,
            "full_q2_background_with_unsafe_slice_restored"),
    )

    ledger = A.dimension_ledger(case_dict, required_margin=n - g)
    stable = {
        "scope": (
            "predeclared coefficientwise F101 q:t=2:1 target-weight and "
            "nonvacuous-safe-deletion connector discriminator; finite only"),
        "field": P,
        "parameters_n_w_g_m_D_q_t_J_L": CASE,
        "target_and_control_J_over_m": (82 / 60, jet / m),
        "minimality_conditions": {
            "n_equals_2w_plus_2": n == 2 * w + 2,
            "g_at_least_w_plus_2_for_retained_maximal_degree": g >= w + 2,
            "positive_curvature_weight_w_minus_2": w - 2,
        },
        "q_H_coefficients": literal["q_h"],
        "Q_coefficients": literal["q"],
        "degrees_Q_qH_QminusqH": (
            len(literal["q"]) - 1, len(literal["q_h"]) - 1,
            len(literal["relative"]) - 1),
        "agreement_values_equal_Q": (
            literal["u1"][:g] == literal["polynomial_values"][:g]),
        "error_offsets_and_actual_values": (
            ERROR_OFFSETS, literal["u1"][g:]),
        "all_actual_U1_values_nonzero": all(literal["u1"]),
        "normal_support_and_error_contact_sizes": (
            literal["normal_support_sizes"],
            literal["normal_contact_support_sizes"]),
        "raw_centered_carrier_legality": G.centered_carrier_legality(literal),
        "strong_safe_terminal_shapes": safe,
        "strong_unsafe_terminal_shapes": unsafe,
        "unsafe_corner_occurrences": corner[(1, 1)],
        "unsafe_deleted_first_shell_slice": {
            "shape_r_s": (1, 1),
            "y_r_s_z": (6, 1, 1, 1),
            "deleted_column_count": len(deleted_indices),
            "deleted_X_degree_interval": (
                min(monomials[index][0] for index in deleted_indices),
                max(monomials[index][0] for index in deleted_indices)),
        },
        "ledger_full_and_restricted_source": (
            ledger["full_source_one_node_contact_all_node_contact"][0],
            ledger["restricted_source_dimension"]),
        "prefix_columns_rank_and_packet_quotient_rank": (
            len(prefix_indices), prefix_echelon.rank,
            G.quotient_rank(prefix_targets)),
        "first_shell_shape_column_counts": tuple(
            (shape, len(indices)) for shape, indices in shell_groups.items()),
        "screens": screens,
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
            "external_memory_cap_bytes": 3 * 1024**3,
        },
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
