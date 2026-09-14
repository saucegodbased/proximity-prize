#!/usr/bin/env python3
"""Exact coefficientwise Z1 gate through the complete m5 passive tower.

This is a narrow finite-control discriminator for the lower-6900 Full187
terminal recurrence.  It reuses the complete literal m5 contact map from the
transposed four-residue audit and computes every centered total-grade prefix
from grade 7 through the legal combined cap 11.  In particular it never
localizes from F_101[X] to F_101(X): the three locator RHS and the pure
constant-Z target are tested in the full coefficientwise boundary matrix.

The calculation is finite discovery evidence, not a target theorem.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import resource
import sys
import time

sys.path.insert(0, ".experiments")
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import f101_transposed_four_residue_mapping_cone_gate_6900 as X  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402


P = 101
CASE = X.CASES["m5"]
EXPECTED = (
    # grade, (prefix, terminal, full), (rank, nullity), RHS defects, joint,
    # (boundary rows, boundary image rank), Z1 defect
    (7, (1841, 455, 2296), (2296, 0), (1, 1, 1), 3, (131, 0), 1),
    (8, (2296, 455, 2751), (2680, 71), (0, 0, 0), 0, (131, 12), 1),
    (9, (2751, 455, 3206), (3060, 146), (0, 0, 0), 0, (131, 12), 1),
    (10, (3206, 455, 3661), (3440, 221), (0, 0, 0), 0, (131, 12), 1),
    (11, (3661, 455, 4116), (3820, 296), (0, 0, 0), 0, (131, 12), 1),
)


def main() -> None:
    started = time.monotonic()
    X.P = P
    M.PRIME = M.T.PRIME = M.F.PRIME = F.PRIME = P
    literal = M.build_case(
        "m5_complete_passive_tower",
        CASE,
        actual_agreement_count=7,
        anchor_count=7,
        normal_coordinates=3,
        error_direction_offsets=X.OFFSETS,
    )

    rows = []
    for grade in range(7, 12):
        receipt = X.transposed_boundary_residues(literal, grade)
        gate = receipt["coefficientwise_F101_target_gate"]
        rows.append((
            grade,
            receipt["source_prefix_terminal_full_dimensions"],
            receipt["contact_rank_nullity"],
            gate["individual_locator_F0_F1_F2_defects"],
            gate["joint_locator_F0_F1_F2_defect"],
            gate["YRSZ_rows_image_rank"],
            gate["pure_constant_Z1_defect"],
        ))

    rows = tuple(rows)
    assert rows == EXPECTED
    nullities = tuple(row[2][1] for row in rows)
    boundary_ranks = tuple(row[5][1] for row in rows)
    assert tuple(
        nullities[index + 1] - nullities[index]
        for index in range(1, len(nullities) - 1)
    ) == (75, 75, 75)
    assert boundary_ranks[1:] == (12, 12, 12, 12)
    assert all(row[6] == 1 for row in rows)

    stable = {
        "scope": (
            "complete literal F101 m5 coefficientwise filtered contact and "
            "boundary gate; no localization; finite control, not target theorem"
        ),
        "parameters_N_w_g_m_D_s_t_J_L": CASE,
        "field": P,
        "error_direction_offsets": X.OFFSETS,
        "grade_rows": rows,
        "post_birth_nullity_increments_grades_9_10_11": (75, 75, 75),
        "post_birth_boundary_rank_increments_grades_9_10_11": (0, 0, 0),
        "last_legal_combined_grade": CASE[-1],
        "decision": "STOP_PASSIVE_DEPTH_ALONE_DOES_NOT_RESCUE_Z1_IN_M5",
        "interpretation": (
            "grade 8 makes all three locator RHS coefficientwise reachable; "
            "grades 9 through 11 add 225 kernel dimensions but no boundary "
            "direction, and constant Z1 remains defect one"
        ),
        "scope_guard": (
            "This rejects a parameter-uniform or m5-evidenced passive-depth "
            "argument.  It neither proves target Z1 failure nor excludes a "
            "target-only active/derivative coupling among the safe 105 shapes."
        ),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    payload = {
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "runtime_receipt": {
            "elapsed_seconds": round(time.monotonic() - started, 6),
            "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            "external_memory_cap_bytes": 4 * 1024**3,
        },
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
