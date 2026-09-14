#!/usr/bin/env python3
"""Targeted integration of q26 FD9 with the all-noncapacity projection.

This does not repeat the 20-million-origin census.  It checks only the eleven
physical f=8,q=26 blocks and the 99 lower-active physical coordinates used by
the ninth-finite-difference bypass.
"""

from __future__ import annotations

from collections import Counter
import hashlib
import json
from pathlib import Path
import resource

import full187_terminal_lowT_hasse_closure_audit_6900 as H
import full187_q26_ninth_difference_bypass_6900 as Q


P = Q.P
N = Q.N
L = Q.L


def group_noncapacity_qset(r: int, s: int, f: int):
    qset = set()
    statuses = Counter()
    for a_e in range(f + 1):
        for c_s in range(f - a_e + 1):
            for q in range(H.M - (f + 2 * a_e + c_s)):
                status, _row, _margin = H.origin_status(
                    r, s, f, a_e, c_s, q, H.ERRORS)
                statuses[status] += 1
                if status != "capacity":
                    qset.add(q)
    return tuple(sorted(qset)), statuses


def original_residual_blocks():
    status_count = Counter()
    margins = []
    qsets = []
    direct_depth27_deficits = []
    rows = set()
    for source_s in range(Q.CURVATURE + 1):
        r = Q.SLOPE - source_s
        qset, _statuses = group_noncapacity_qset(r, source_s, Q.ORIGINAL_F)
        assert qset == tuple(range(14))
        qsets.append((source_s, qset))

        direct_width = Q.width(Q.ORIGINAL_F, r, source_s)
        assert direct_width == 7_023_742 + source_s
        deficit = 27 * N - direct_width
        assert deficit == 54_146 - source_s > 0
        direct_depth27_deficits.append(deficit)

        for a_e in range(Q.ORIGINAL_F + 1):
            for c_s in range(Q.ORIGINAL_F - a_e + 1):
                status, terminal_row, margin = H.origin_status(
                    r, source_s, Q.ORIGINAL_F, a_e, c_s,
                    Q.ORIGINAL_Q, H.ERRORS)
                assert status == "capacity"
                expected = Q.row(
                    Q.ORIGINAL_Y, r, source_s, Q.ORIGINAL_Z,
                    Q.ORIGINAL_F, Q.ORIGINAL_Y - Q.ORIGINAL_F,
                    a_e, c_s, Q.ORIGINAL_Q)
                assert terminal_row == (*expected[:4], expected[4] - (L-H.J))
                status_count[status] += 1
                margins.append(margin)
                rows.add(expected)

    assert status_count == Counter(capacity=495)
    assert len(rows) == 495
    assert (min(margins), max(margins)) == (2_333_004, 5_219_622)
    return {
        "physical_common_blocks": 11,
        "expanded_aE_cS_origins_and_rows": (495, len(rows)),
        "all_q26_origins_after_projection_status": tuple(
            sorted(status_count.items())),
        "strong_margin_before_error_min_max": (min(margins), max(margins)),
        "strong_slack_after_error_min_max": (
            min(margins) - H.ERRORS, max(margins) - H.ERRORS),
        "noncapacity_qset_in_same_f8_physical_coordinate": tuple(qsets),
        "interpretation": (
            "The Pascal projection prescribes q=0..13 in each direct P8 "
            "coordinate. The q=26 block is already strong-capacity and is "
            "therefore deliberately left in its residual quotient."
        ),
        "direct_P8_depth27_window_deficit_min_max": (
            min(direct_depth27_deficits), max(direct_depth27_deficits)),
    }


def finite_difference_coordinate_overlap():
    records = []
    root_qmax_histogram = Counter()
    target_head_statuses = Counter()
    coordinates = set()
    minimum_uniform_A26_slack = None
    for source_s in range(Q.CURVATURE + 1):
        original_r = Q.SLOPE - source_s
        for k in range(1, Q.DIFFERENCE_ORDER + 1):
            y = Q.ORIGINAL_F + k
            r = original_r - k
            s = source_s
            z = Q.CORRECTION_Z
            q_fd = Q.ORIGINAL_Q - k
            coordinate = (y, r, s, z)
            assert coordinate not in coordinates
            coordinates.add(coordinate)
            assert z == L - y - r - s

            root_qset, root_statuses = group_noncapacity_qset(r, s, y)
            assert root_qset == tuple(range(14 - k))
            root_qmax = max(root_qset)
            assert root_qmax == 13 - k
            assert q_fd == 26 - k
            assert q_fd - root_qmax == 13
            assert q_fd not in root_qset
            root_qmax_histogram[root_qmax] += 1

            source_width = Q.width(y, r, s)
            uniform_slack = source_width - 26 * N
            assert uniform_slack >= 207_989
            minimum_uniform_A26_slack = (
                uniform_slack if minimum_uniform_A26_slack is None
                else min(minimum_uniform_A26_slack, uniform_slack))

            # These are the exact 45 low-contact-degree heads entering FD9.
            # Each is itself residual strong-capacity, so FD9 is a relation
            # inside the residual capacity quotient, not part of the prior
            # noncapacity projection.
            for a_e in range(Q.ORIGINAL_F + 1):
                for c_s in range(Q.ORIGINAL_F - a_e + 1):
                    status, _row, _margin = H.origin_status(
                        r, s, y, a_e, c_s, q_fd, H.ERRORS)
                    assert status == "capacity"
                    target_head_statuses[status] += 1

            records.append((
                source_s, k, coordinate, root_qset, q_fd, source_width,
                tuple(sorted(root_statuses.items()))))

    assert len(coordinates) == 99
    assert target_head_statuses == Counter(capacity=99 * 45)
    assert root_qmax_histogram == Counter({q: 11 for q in range(4, 13)})
    assert minimum_uniform_A26_slack == 207_989
    return {
        "FD9_physical_coordinates": len(coordinates),
        "coordinates_already_used_by_Pascal_projection": len(records),
        "root_projection_qmax_histogram": tuple(sorted(
            root_qmax_histogram.items())),
        "root_qmax_formula": "Qroot(k)=13-k",
        "FD9_q_formula": "Qfd(k)=26-k",
        "constant_jet_separation": 13,
        "intermediate_unassigned_jet_count": 12,
        "jet_coordinate_conflicts": 0,
        "combined_section": (
            "Superpose the existing root prescriptions at q<=13-k and the "
            "FD9 prescription at q=26-k in one A_26 residue; set remaining "
            "q<26 as desired. Linearity and Hasse-order separation preserve "
            "the descending Pascal cancellations."
        ),
        "minimum_combined_A26_window_slack": minimum_uniform_A26_slack,
        "FD9_low_degree_head_statuses": tuple(sorted(
            target_head_statuses.items())),
        "record_digest": hashlib.sha256(json.dumps(
            records, separators=(",", ":")).encode()).hexdigest(),
    }


def main():
    original = original_residual_blocks()
    overlap = finite_difference_coordinate_overlap()
    factorization = Q.sharp_basis_factorization_receipt()
    stable = {
        "scope": (
            "targeted integration of commit 7504148 noncapacity projection "
            "with d1620d8 q26 FD9; eleven q26 blocks and their 99 physical "
            "correction coordinates only"
        ),
        "target_p_N_w_g_errors_m_D_J_L_q_t": (
            P, N, H.W, H.G, H.ERRORS, H.M, H.D, H.J, L,
            H.SLOPE, H.CURVATURE),
        "original_capacity_residual": original,
        "physical_coordinate_overlap": overlap,
        "same_Z_residual_after_FD9": {
            "block_count": 11,
            "formula": factorization["exact_factorization_per_stream"],
            "existing_sharp_flag_d_q_t": (
                factorization["existing_sharp_flag_d_q_t"]),
            "basis_pivot_weight_min_max": (
                factorization["all_basis_pivot_weights"]),
            "minimum_d29_width_minus_26N": (
                factorization["minimum_flag_width_minus_26N"]),
            "meaning": (
                "FD9 removes the complete degree<=8 projection of each "
                "q26 contactY^8 block (495 expanded origins). Its same-Z "
                "remainder is eleven structured U^9 order-two blocks, not "
                "1,111 unrelated capacity coordinates."
            ),
        },
        "weak_projection_q26_common_coefficient": {
            "formula": (
                "R_s=binom(61,8)*U1^53*H26(C_s)"
                "+sum_{f=8}^{57}binom(f,8)*U1^(f-8)*H26(P_{f,s})"),
            "contributors_per_stream_and_total_expanded_provenance": (
                51, 11 * 45 * 51),
            "required_general_FD9_prescription": (
                "H_(26-k)(Q_(k,s))=(-1)^k*binom(9,k)*R_s"),
            "specialization_guard": (
                "The older coefficient binom(61,8)U1^53H26(C_s) is valid "
                "only for a section setting every unprescribed H26(P_f,s) "
                "to zero. The universal prescription uses the full R_s."),
        },
        "subsumption_verdict": (
            "STRICT_EXTENSION: 7504148 leaves all 495 f8,q26 origins in the "
            "strong-capacity residual; FD9 removes their degree<=8 physical "
            "block without an illegal P8 depth-27 lift."
        ),
        "simultaneous_capacity_verdict": (
            "LOCAL_COLLISION_RESOLVED_ONLY: all 99 FD9 source polynomials "
            "are already physical Pascal coordinates, but their prescribed "
            "jet sets are disjoint by exactly 13 orders and fit jointly in "
            "A_26. This removes the eleven direct P8 q26 demands and groups "
            "the 99 replacement heads into eleven U^9 residues. It does not "
            "construct or prove collision-freedom of the remaining global "
            "simultaneous capacity section."
        ),
        "complete_depth_supersession_guard": (
            "This compatibility statement is ONLY for commit 7504148. "
            "Commit 2d678e8 prescribes q=0..25 in all 99 FD coordinates, "
            "so the jet sets then collide. The exact adapted-basis rank gate "
            "full187_q26_complete_depth_rank_6900.py proves all eleven q26 "
            "classes remain independent modulo that stronger source box."),
        "exact_fourth_packet": "F3=B*(Y-P-(Z-gamma)*q_H)",
        "decision": "GREEN_ONLY_VS_WEAK_750__STOP_VS_COMPLETE_DEPTH_2D678E8",
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    print(json.dumps({
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
