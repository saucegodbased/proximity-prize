#!/usr/bin/env python3
"""Small exact matched controls for post-prefix connector-shape scaling.

The chamber N=7,w=3,g=5 is the smallest order-two matched chamber with
positive curvature weight and deg(Xi_E^2)=4 strictly between w and g.  At a
requested multiplicity m it uses J=m+2, L=J+1 and exact F0..F3.  It reports
which first-shell derivative-shape subsets kill the coefficientwise packet
residue modulo the complete grade-J prefix.  No localization is used.
"""

from __future__ import annotations

import argparse
from itertools import combinations
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

sys.path.insert(0, ".experiments")
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402


P = 101
ERROR_OFFSETS = (3, 5)


def rank(columns):
    echelon = M.ColumnEchelon()
    for index, column in enumerate(columns):
        echelon.add(column, index)
    return echelon.rank


def defects(columns, targets):
    base = rank(columns)
    individual = tuple(rank(columns + (target,)) - base for target in targets)
    return individual, rank(columns + targets) - base


def analyze(m, slope, curvature, jet_offset, error_offsets=None):
    jet = m + jet_offset
    case = (7, 3, 5, m, 5 * m, slope, curvature, jet, jet + 1)
    literal = M.build_case(
        f"small_matched_m{m}_q{slope}_t{curvature}", case,
        actual_agreement_count=5,
        anchor_count=5,
        normal_coordinates=4,
        error_direction_offsets=error_offsets,
    )
    prefix = tuple(
        index for index, monomial in enumerate(literal.monomials)
        if sum(monomial[1:]) <= jet)
    prefix_echelon = M.ColumnEchelon()
    for index in prefix:
        prefix_echelon.add(literal.columns[index], index)
    targets = tuple(prefix_echelon.reduce(target) for target in literal.targets)

    group_indices = {}
    for index, monomial in enumerate(literal.monomials):
        if sum(monomial[1:]) == jet + 1:
            group_indices.setdefault((monomial[2], monomial[3]), []).append(index)
    group_indices = {
        shape: tuple(indices) for shape, indices in sorted(group_indices.items())}
    groups = {
        shape: tuple(prefix_echelon.reduce(literal.columns[index])
                     for index in indices)
        for shape, indices in group_indices.items()}

    subset_rows = []
    shapes = tuple(groups)
    for size in range(1, len(shapes) + 1):
        for subset in combinations(shapes, size):
            columns = tuple(column for shape in subset for column in groups[shape])
            individual, joint = defects(columns, targets)
            subset_rows.append((subset, individual, joint))
    closing = tuple(subset for subset, _individual, joint in subset_rows if joint == 0)
    minimal = tuple(
        subset for subset in closing
        if not any(set(other) < set(subset) for other in closing))
    return {
        "parameters_n_w_g_m_D_q_t_J_L": case,
        "error_direction_offsets": error_offsets,
        "prefix_columns_rank": (len(prefix), prefix_echelon.rank),
        "packet_individual_nonzero": tuple(bool(target) for target in targets),
        "packet_quotient_rank": rank(targets),
        "shell_group_columns_and_quotient_ranks": tuple(
            (shape, len(group_indices[shape]), rank(groups[shape]))
            for shape in shapes),
        "inclusion_minimal_closing_shape_subsets": minimal,
        "all_shapes_joint_defect": defects(
            tuple(column for shape in shapes for column in groups[shape]), targets)[1],
        "subset_rows": tuple(subset_rows),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--m", type=int, required=True)
    parser.add_argument("--slope", type=int, default=1)
    parser.add_argument("--curvature", type=int, default=1)
    parser.add_argument("--jet-offset", type=int, default=2)
    parser.add_argument(
        "--offset-errors", action="store_true",
        help="replace the two error-node Q values by Q+(3,5)")
    args = parser.parse_args()
    started = time.monotonic()
    M.PRIME = M.T.PRIME = M.F.PRIME = F.PRIME = P
    error_offsets = ERROR_OFFSETS if args.offset_errors else None
    row = analyze(
        args.m, args.slope, args.curvature, args.jet_offset, error_offsets)
    stable = {
        "scope": (
            "smallest positive-weight matched F101 chamber, exact "
            "coefficientwise F0..F3 connector shape scan; finite control only"
        ),
        "field": P,
        "error_direction_offsets": error_offsets,
        "row": row,
        "scope_guard": (
            "This scaling discriminator changes N,w,g and does not prove a "
            "uniform Full187 recurrence or target nonvanishing."
        ),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    print(json.dumps({
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "runtime_receipt": {
            "elapsed_seconds": round(time.monotonic() - started, 6),
            "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            "external_memory_cap_bytes": 4 * 1024**3,
        },
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
