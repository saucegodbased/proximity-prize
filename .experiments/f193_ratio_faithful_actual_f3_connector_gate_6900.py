#!/usr/bin/env python3
"""Sparse exact connector gate in a target-ratio-faithful F_193 chamber.

The chamber is fixed at

  (N,g,e,w,m,J,L) = (64,44,20,31,4,6,10),

so ``w < 2e < g < e+w`` and ``g-(e+w)=-7``.  These are the same strict
degree inequalities as Full187.  Agreement direction is Xi_E^2 and the
error direction is X^(e-1).  We stream only the complete grade-at-most-J
prefix and the first grade-J+1 shell into a sparse exact quotient over
F_193, then test the raw pure/R/S shell groups against the actual four
locator packets.  No arbitrary terminal column or full-source matrix is
built.
"""

from __future__ import annotations

import argparse
import hashlib
from itertools import combinations
import json
from pathlib import Path
import resource
import sys
import time

sys.path.insert(0, ".experiments")
import f101_o2_bordered_filtration_mechanism_6900 as BM  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402
import prime_o2_conormal_threshold_falsifier as T  # noqa: E402
from higher_jet_literal_matrix import translated_column  # noqa: E402


P = 193
CASE = (64, 31, 44, 4, 176, 1, 1, 6, 10)
MEMORY_CAP_BYTES = 3 * 1024**3


def add_scaled(target, source, scale):
    for row, coefficient in source.items():
        value = (target.get(row, 0) + scale * coefficient) % P
        if value:
            target[row] = value
        else:
            target.pop(row, None)


def source_hash(source):
    return hashlib.sha256(
        repr(tuple(sorted(source.items()))).encode()).hexdigest()


def exact_vertical_rows(source):
    rows = {}
    wanted = {
        (1, 0, 0, 0): 0,
        (0, 1, 0, 0): 1,
        (0, 0, 1, 0): 2,
        (0, 0, 0, 1): 3,
    }
    for (xp, y, r, s, z), coefficient in source.items():
        coordinate = wanted.get((y, r, s, z))
        if coordinate is not None and coefficient % P:
            rows[("J", coordinate, xp)] = coefficient % P
    return rows


def coupled_column(monomial, u0, u1, m):
    xp, y, r, s, z = monomial
    column = {}
    for node in range(len(u0)):
        local_column = translated_column(
            xp, (y, r, s), z, node, u0[node], u1[node], m, 2, P)
        for local, coefficient in local_column.items():
            if coefficient:
                column[("C", node, local)] = coefficient
    coordinate = {
        (1, 0, 0, 0): 0,
        (0, 1, 0, 0): 1,
        (0, 0, 1, 0): 2,
        (0, 0, 0, 1): 3,
    }.get((y, r, s, z))
    if coordinate is not None:
        column[("J", coordinate, xp)] = 1
    return column


def literal_contact_image(source, u0, u1, m):
    image = {}
    for monomial, source_coefficient in source.items():
        xp, y, r, s, z = monomial
        for node in range(len(u0)):
            for local, coefficient in translated_column(
                    xp, (y, r, s), z, node, u0[node], u1[node],
                    m, 2, P).items():
                row = (node, local)
                value = (image.get(row, 0)
                         + source_coefficient * coefficient) % P
                if value:
                    image[row] = value
                else:
                    image.pop(row, None)
    return image


def quotient_rank(columns):
    echelon = BM.ColumnEchelon()
    for index, column in enumerate(columns):
        echelon.add(column, index)
    return echelon.rank


def quotient_profile(columns, targets):
    """One base elimination, then exact individual and joint defects."""
    echelon = BM.ColumnEchelon()
    for index, column in enumerate(columns):
        echelon.add(column, index)
    residues = tuple(echelon.reduce(target) for target in targets)
    individual = tuple(int(bool(residue)) for residue in residues)
    joint = quotient_rank(residues)
    return echelon.rank, (individual, joint)


def build_packet(case):
    n, w, agreement_count, m, degree, slope, curvature, jet, seed = case
    agreement = tuple(range(agreement_count))
    error = tuple(range(agreement_count, n))
    xi_error = F.locator(error)
    q = F.poly_pow(xi_error, 2)
    error_direction = (0,) * (len(error) - 1) + (1,)
    assert (len(q) - 1, len(error_direction) - 1) == (2 * len(error),
                                                        len(error) - 1)
    assert w < len(q) - 1 < agreement_count < n < P
    assert agreement_count - (len(error) + w) == -7

    u0 = tuple(0 if node in agreement else 1 for node in range(n))
    u1 = tuple(
        F.poly_eval(q, node) if node in agreement
        else F.poly_eval(error_direction, node)
        for node in range(n)
    )

    locator = F.locator(agreement)
    normals = list(F.centered_locator_normals(locator, (0,), q))
    anchors = tuple(range(w + 1))
    q_h = T.interpolate(tuple(F.poly_eval(q, node) for node in anchors),
                        anchors)
    assert len(q_h) - 1 <= w
    remaining = tuple(node for node in agreement if node not in anchors)
    multiplier = F.poly_mul(
        F.poly_pow(F.locator(anchors), m - 1),
        F.poly_pow(F.locator(remaining), m),
    )
    assert len(multiplier) - 1 == m * agreement_count - (w + 1)
    bracket = F.sparse_add(
        F.Y, F.sparse_mul(F.Z, F.sparse_embed_x(q_h)), -1)
    f3 = F.sparse_mul(F.sparse_embed_x(multiplier), bracket)
    normals.append(f3)
    normals = tuple(normals)

    # Literal agreement contact preflight for the actual packets.
    contact_supports = []
    for normal in normals:
        image = literal_contact_image(normal, u0, u1, m)
        agreement_image = tuple(
            row for row in image if row[0] in agreement)
        assert not agreement_image
        contact_supports.append(len(image))
    return {
        "agreement": agreement,
        "error": error,
        "xi_error": xi_error,
        "agreement_direction": q,
        "error_direction": error_direction,
        "u0": u0,
        "u1": u1,
        "q_h": q_h,
        "normals": normals,
        "targets": tuple(exact_vertical_rows(normal) for normal in normals),
        "contact_supports_outside_agreement": tuple(contact_supports),
    }


def analyze(progress_every, decisive_only, full_shell_only):
    n, w, g, m, degree, slope, curvature, jet, seed = CASE
    packet = build_packet(CASE)
    all_monomials = T.support(w, degree, slope, curvature, jet, seed)
    admitted = tuple(
        monomial for monomial in all_monomials
        if sum(monomial[1:]) <= jet + 1
    )
    prefix = tuple(
        monomial for monomial in admitted if sum(monomial[1:]) <= jet)
    shell = tuple(
        monomial for monomial in admitted if sum(monomial[1:]) == jet + 1)
    shell_shapes = tuple(sorted({(row[2], row[3]) for row in shell}))
    assert shell_shapes == ((0, 0), (0, 1), (1, 0))

    prefix_echelon = BM.ColumnEchelon()
    started_prefix = time.monotonic()
    for position, monomial in enumerate(prefix, 1):
        prefix_echelon.add(
            coupled_column(monomial, packet["u0"], packet["u1"], m),
            position - 1,
        )
        if progress_every and position % progress_every == 0:
            print(
                f"prefix {position}/{len(prefix)} rank={prefix_echelon.rank} "
                f"elapsed={time.monotonic()-started_prefix:.1f}s",
                file=sys.stderr,
                flush=True,
            )
    target_residues = tuple(
        prefix_echelon.reduce(target) for target in packet["targets"])
    packet_rank = quotient_rank(target_residues)

    if decisive_only or full_shell_only:
        selected_shapes = (
            shell_shapes if full_shell_only else ((0, 0), (1, 0)))
        selected_shell = tuple(
            monomial for monomial in shell
            if (monomial[2], monomial[3]) in selected_shapes
        )
        shell_echelon = BM.ColumnEchelon()
        started_shell = time.monotonic()
        for position, monomial in enumerate(selected_shell, 1):
            column = coupled_column(
                monomial, packet["u0"], packet["u1"], m)
            residue = prefix_echelon.reduce(column)
            shell_echelon.add(residue, position - 1)
            if progress_every and position % progress_every == 0:
                print(
                    f"selected shell {position}/{len(selected_shell)} "
                    f"quotient-rank={shell_echelon.rank} "
                    f"elapsed={time.monotonic()-started_shell:.1f}s",
                    file=sys.stderr,
                    flush=True,
                )
        packet_after_shell = tuple(
            shell_echelon.reduce(target) for target in target_residues)
        defects = (
            tuple(int(bool(row)) for row in packet_after_shell),
            quotient_rank(packet_after_shell),
        )
        return {
            "scope": (
                "exact sparse F193 target-ratio-faithful binary connector "
                "gate for actual F0..F3; not a Full187 theorem"
            ),
            "field": P,
            "parameters_n_w_g_m_D_s_t_J_L": CASE,
            "error_count_e": len(packet["error"]),
            "degree_balance_g_minus_e_plus_w": (
                g - (len(packet["error"]) + w)),
            "strict_target_degree_chamber_w_lt_2e_lt_g_lt_e_plus_w": (
                w < 2 * len(packet["error"]) < g
                < len(packet["error"]) + w),
            "agreement_direction_degree": (
                len(packet["agreement_direction"]) - 1),
            "error_direction_degree": len(packet["error_direction"]) - 1,
            "actual_packet_contact_supports_outside_agreement":
                packet["contact_supports_outside_agreement"],
            "complete_source_columns": len(all_monomials),
            "prefix_columns_and_rank": (len(prefix), prefix_echelon.rank),
            "prefix_packet_residue_supports": tuple(map(len, target_residues)),
            "prefix_packet_quotient_rank": packet_rank,
            "tested_first_shell_shapes": selected_shapes,
            "tested_first_shell_columns_and_quotient_rank": (
                len(selected_shell), shell_echelon.rank),
            "packet_individual_and_joint_defects_after_selected_shell":
                defects,
            "decision": (
                ("RATIO_FAITHFUL_FULL_FIRST_SHELL_CONNECTOR_GREEN"
                 if full_shell_only else
                 "RATIO_FAITHFUL_PURE_PLUS_R_CONNECTOR_GREEN")
                if defects[1] == 0 else
                ("RATIO_FAITHFUL_FULL_FIRST_SHELL_CONNECTOR_RED"
                 if full_shell_only else
                 "RATIO_FAITHFUL_PURE_PLUS_R_CONNECTOR_RED")
            ),
            "minimality_not_claimed": True,
            "verified_prior_pure_plus_R_quotient_rank": (
                1011 if full_shell_only else None),
            "marginal_quotient_rank_contributed_by_S_over_pure_plus_R": (
                shell_echelon.rank - 1011 if full_shell_only else None),
            "streamed_monomials_sha256": hashlib.sha256(
                repr(prefix + selected_shell).encode()).hexdigest(),
        }

    shell_residues = {shape: [] for shape in shell_shapes}
    started_shell = time.monotonic()
    for position, monomial in enumerate(shell, 1):
        column = coupled_column(monomial, packet["u0"], packet["u1"], m)
        shell_residues[(monomial[2], monomial[3])].append(
            prefix_echelon.reduce(column))
        if progress_every and position % progress_every == 0:
            print(
                f"shell {position}/{len(shell)} "
                f"elapsed={time.monotonic()-started_shell:.1f}s",
                file=sys.stderr,
                flush=True,
            )
    shell_residues = {
        shape: tuple(rows) for shape, rows in shell_residues.items()
    }

    group_rows = []
    for shape in shell_shapes:
        rank, defects = quotient_profile(
            shell_residues[shape], target_residues)
        group_rows.append({
            "shape_r_s": shape,
            "columns": len(shell_residues[shape]),
            "quotient_rank": rank,
            "packet_individual_and_joint_defects": defects,
            "actual_F3_defect": defects[0][3],
        })

    subset_rows = []
    for size in range(1, len(shell_shapes) + 1):
        for subset in combinations(shell_shapes, size):
            columns = tuple(
                column for shape in subset for column in shell_residues[shape])
            _rank, defects = quotient_profile(columns, target_residues)
            subset_rows.append({
                "shapes": subset,
                "columns": len(columns),
                "packet_individual_and_joint_defects": defects,
                "actual_F3_defect": defects[0][3],
            })
    closing = tuple(
        row["shapes"] for row in subset_rows
        if row["packet_individual_and_joint_defects"][1] == 0
    )
    minimal = tuple(
        subset for subset in closing
        if not any(set(other) < set(subset) for other in closing)
    )
    f3_closing = tuple(
        row["shapes"] for row in subset_rows if row["actual_F3_defect"] == 0)
    f3_minimal = tuple(
        subset for subset in f3_closing
        if not any(set(other) < set(subset) for other in f3_closing)
    )

    return {
        "scope": (
            "exact sparse F193 target-ratio-faithful prefix plus first-shell "
            "connector gate for actual F0..F3; not a Full187 theorem"
        ),
        "field": P,
        "parameters_n_w_g_m_D_s_t_J_L": CASE,
        "error_count_e": len(packet["error"]),
        "degree_balance_g_minus_e_plus_w": g - (len(packet["error"]) + w),
        "strict_target_degree_chamber_w_lt_2e_lt_g_lt_e_plus_w": (
            w < 2 * len(packet["error"]) < g < len(packet["error"]) + w),
        "agreement_nodes": packet["agreement"],
        "error_nodes": packet["error"],
        "agreement_direction_degree_and_sha256": (
            len(packet["agreement_direction"]) - 1,
            hashlib.sha256(repr(packet["agreement_direction"]).encode()).hexdigest(),
        ),
        "error_direction_degree": len(packet["error_direction"]) - 1,
        "interpolated_q_H_degree_and_sha256": (
            len(packet["q_h"]) - 1, source_hash(
                {(i, 0, 0, 0, 0): value
                 for i, value in enumerate(packet["q_h"]) if value}),
        ),
        "actual_packet_contact_supports_outside_agreement":
            packet["contact_supports_outside_agreement"],
        "complete_source_columns": len(all_monomials),
        "streamed_prefix_plus_shell_columns": len(admitted),
        "streamed_monomials_sha256": hashlib.sha256(
            repr(admitted).encode()).hexdigest(),
        "prefix_columns_and_rank": (len(prefix), prefix_echelon.rank),
        "prefix_packet_residue_supports": tuple(map(len, target_residues)),
        "prefix_packet_quotient_rank": packet_rank,
        "first_shell_columns": len(shell),
        "first_shell_groups": tuple(group_rows),
        "first_shell_subset_ablations": tuple(subset_rows),
        "minimal_shapes_closing_actual_F3": f3_minimal,
        "minimal_shapes_closing_all_four_packets": minimal,
        "decision": (
            "RATIO_FAITHFUL_FIRST_SHELL_CONNECTOR_GREEN"
            if minimal else "RATIO_FAITHFUL_FIRST_SHELL_CONNECTOR_RED"
        ),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--progress-every", type=int, default=250)
    parser.add_argument(
        "--decisive-only", action="store_true",
        help="test pure+R first and skip all redundant shape ablations")
    parser.add_argument(
        "--full-shell-only", action="store_true",
        help="test pure+R+S once and skip all redundant shape ablations")
    args = parser.parse_args()
    if args.decisive_only and args.full_shell_only:
        parser.error("choose at most one single-pass shell gate")
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY_CAP_BYTES, MEMORY_CAP_BYTES))
    BM.PRIME = BM.T.PRIME = BM.F.PRIME = F.PRIME = T.PRIME = P
    F.GAMMA = 0
    started = time.monotonic()
    stable = analyze(
        args.progress_every, args.decisive_only, args.full_shell_only)
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    print(json.dumps({
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "runtime_receipt": {
            "elapsed_seconds": round(time.monotonic() - started, 6),
            "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            "hard_address_space_cap_bytes": MEMORY_CAP_BYTES,
        },
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
