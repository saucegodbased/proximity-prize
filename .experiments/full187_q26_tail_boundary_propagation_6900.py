#!/usr/bin/env python3
"""Propagate the exact q26 P8/P9 correction into its first tail quotient.

The adjacent Hankel certificate in 14b5109 closes every f=8,q=26 common
coefficient while preserving q=0..25.  This audit expands every structural
q>=26 term of those P8/P9 variations, identifies the unique lowest centered
grade tail, and tests its coupled contact/boundary class.

The smallest tail is the P9 (f,h)=(0,0), q=26 term at centered grade 2694.
It is error-only, its boundary normal is exactly zero, and it lies in the
q=26 complete-depth slot of a legal grade-2694 P0 source.  That source has no
Y, so this smallest-grade cancellation creates no still-lower u0 tail.

The rest of the expansion is partitioned, blockwise, between lower-grade
copies of the complete-depth Pascal recurrence and the already identified
strong-capacity residual region.  This is a structural propagation theorem,
not a simultaneous section for all strong-capacity blocks and not a packet
prelift.
"""

from __future__ import annotations

from collections import Counter, defaultdict
import hashlib
import json
from math import comb, factorial
from pathlib import Path
import resource

import full187_complete_depth_pascal_hermite_slide_6900 as CD
import full187_packet_vs_deep_slide_filtration_separator_6900 as PS
import full187_q26_adjacent_fringe_hankel_6900 as ADJ
import full187_terminal_lowT_hasse_closure_audit_6900 as H


P = ADJ.P
N = H.N
M = H.M
J = H.J
L = ADJ.L
G = H.G
ERRORS = H.ERRORS
SLOPE = H.SLOPE
CURVATURE = H.CURVATURE
INV2 = pow(2, -1, P)


def multinomial(f, a_e, c_s):
    return factorial(f) // (
        factorial(a_e) * factorial(c_s) * factorial(f - a_e - c_s))


def contact_scalar(source_y, contact_f, h, a_e, c_s):
    """Non-u0/u1 scalar in one local P_y contact term."""
    return (
        comb(source_y, contact_f)
        * comb(source_y - contact_f, h)
        * multinomial(contact_f, a_e, c_s)
        * pow(-INV2 % P, c_s, P)
    ) % P


def contact_row(r, s, source_z, contact_f, h, a_e, c_s, q):
    return (
        q + contact_f - a_e + c_s,
        a_e,
        r + contact_f - a_e - c_s,
        s + c_s,
        source_z + h,
    )


def qmax_staircase_and_residual_capacity():
    """Exact complete-prefix staircase for all possible induced blocks."""
    qmax_by_f = []
    counts = Counter()
    minimum_remaining_margin = None
    minimum_remaining_witness = None

    for f in range(10):
        values = {
            CD.complete_qmax(SLOPE - s, s, f)
            for s in range(CURVATURE + 1)
        }
        assert len(values) == 1
        qmax = values.pop()
        qmax_by_f.append(qmax)

    assert tuple(qmax_by_f) == (29, 29, 28, 28, 27, 27, 26, 26, 25, 25)

    for s in range(CURVATURE + 1):
        r = SLOPE - s
        for f, qmax in enumerate(qmax_by_f):
            for q in range(26, M - f):
                block_class = "complete" if q <= qmax else "capacity"
                counts[(block_class, "blocks")] += 1
                for a_e in range(f + 1):
                    for c_s in range(f - a_e + 1):
                        if q + f + 2 * a_e + c_s >= M:
                            continue
                        counts[(block_class, "origins")] += 1
                        status, row, margin = H.origin_status(
                            r, s, f, a_e, c_s, q, ERRORS)
                        assert status == "capacity"
                        if block_class == "capacity" and not (
                                f == 8 and q == 26):
                            if (minimum_remaining_margin is None
                                    or margin < minimum_remaining_margin):
                                minimum_remaining_margin = margin
                                minimum_remaining_witness = (
                                    s, f, a_e, c_s, q, row)

    assert counts == Counter({
        ("complete", "blocks"): 220,
        ("capacity", "blocks"): 3_025,
        ("complete", "origins"): 2_200,
        ("capacity", "origins"): 47_410,
    })
    assert minimum_remaining_margin == 2_382_346
    assert minimum_remaining_witness == (
        0, 9, 0, 0, 26, (35, 0, 30, 0, 52))
    return {
        "complete_qmax_for_f0_through_f9": tuple(qmax_by_f),
        "q_ge_26_block_and_literal_origin_counts": tuple(
            (kind, unit, counts[(kind, unit)])
            for kind in ("complete", "capacity")
            for unit in ("blocks", "origins")),
        "complete_staircase": (
            "q26:f<=7; q27:f<=5; q28:f<=3; q29:f<=1"),
        "all_49610_q_ge_26_local_origins_are_strong_capacity_licensed": True,
        "minimum_margin_after_removing_solved_f8_q26": (
            minimum_remaining_margin),
        "minimum_remaining_capacity_witness_s_f_aE_cS_q_row": (
            minimum_remaining_witness),
        "minimum_remaining_margin_minus_errors": (
            minimum_remaining_margin - ERRORS),
    }


def induced_tail_census():
    """Enumerate every structural q>=26 P8/P9 occurrence exactly."""
    counts = Counter()
    distinct_rows = {name: set() for name in (
        "solved",
        "full_complete", "full_capacity",
        "u0_complete", "u0_capacity",
    )}
    grade_ranges = {}
    row_streams = defaultdict(set)
    row_provenance = Counter()
    payload_hasher = hashlib.sha256()
    nonsolved_records = []

    for s in range(CURVATURE + 1):
        r = SLOPE - s
        for source_name, source_y, source_z in (
                ("P8", 8, 2_674), ("P9", 9, 2_673)):
            for contact_f in range(source_y + 1):
                qmax = CD.complete_qmax(r, s, contact_f)
                for a_e in range(contact_f + 1):
                    for c_s in range(contact_f - a_e + 1):
                        for h in range(source_y - contact_f + 1):
                            u0_power = source_y - contact_f - h
                            scalar = contact_scalar(
                                source_y, contact_f, h, a_e, c_s)
                            assert scalar
                            for q in range(
                                    26,
                                    M - (contact_f + 2 * a_e + c_s)):
                                row = contact_row(
                                    r, s, source_z, contact_f, h,
                                    a_e, c_s, q)
                                grade = (
                                    contact_f + r + s + source_z + h)
                                assert grade == L - u0_power
                                is_solved = (
                                    q == 26 and contact_f == 8
                                    and u0_power == 0 and row[-1] == 2_674)
                                if is_solved:
                                    category = "solved"
                                else:
                                    prefix = "u0" if u0_power else "full"
                                    suffix = (
                                        "complete" if q <= qmax
                                        else "capacity")
                                    category = f"{prefix}_{suffix}"

                                counts[category] += 1
                                distinct_rows[category].add(row)
                                row_streams[(category, row)].add(s)
                                row_provenance[(category, row)] += 1
                                old_range = grade_ranges.get(category)
                                grade_ranges[category] = (
                                    grade if old_range is None
                                    else min(old_range[0], grade),
                                    grade if old_range is None
                                    else max(old_range[1], grade),
                                )
                                record = (
                                    category, source_name, s, source_y,
                                    contact_f, h, u0_power, a_e, c_s, q,
                                    grade, row, scalar)
                                payload_hasher.update(repr(record).encode())
                                if not is_solved:
                                    nonsolved_records.append(record)

    assert counts == Counter({
        "solved": 990,
        "full_complete": 4_400,
        "full_capacity": 84_150,
        "u0_complete": 17_864,
        "u0_capacity": 207_922,
    })
    assert {name: len(rows) for name, rows in distinct_rows.items()} == {
        "solved": 495,
        "full_complete": 1_740,
        "full_capacity": 15_575,
        "u0_complete": 7_552,
        "u0_capacity": 50_366,
    }
    assert grade_ranges == {
        "solved": (2_703, 2_703),
        "full_complete": (2_703, 2_703),
        "full_capacity": (2_703, 2_703),
        "u0_complete": (2_694, 2_702),
        "u0_capacity": (2_694, 2_702),
    }

    # Centered grade first, then contact/Hasse weight.  The unique smallest
    # structural operator per stream is P9,f=h=aE=cS=0,q=26.
    minimum_key = min(
        (record[10], record[9] + record[4] + 2 * record[7] + record[8])
        for record in nonsolved_records)
    minimum = tuple(record for record in nonsolved_records
                    if (record[10],
                        record[9] + record[4] + 2 * record[7] + record[8])
                    == minimum_key)
    assert minimum_key == (2_694, 26)
    assert len(minimum) == 11
    for record in minimum:
        (category, source_name, s, source_y, contact_f, h, u0_power,
         a_e, c_s, q, grade, row, scalar) = record
        assert (category, source_name, source_y, contact_f, h, u0_power,
                a_e, c_s, q, grade, scalar) == (
                    "u0_complete", "P9", 9, 0, 0, 9,
                    0, 0, 26, 2_694, 1)
        assert row == (26, 0, 21 - s, s, 2_673)

    cross_shape_receipts = []
    expected_multirow_counts = {
        "solved": 0,
        "full_complete": 424,
        "full_capacity": 11_252,
        "u0_complete": 2_255,
        "u0_capacity": 32_086,
    }
    for category in sorted(distinct_rows):
        rows = distinct_rows[category]
        stream_multiplicity = Counter(
            len(row_streams[(category, row)]) for row in rows)
        provenance_multiplicity = Counter(
            row_provenance[(category, row)] for row in rows)
        multiple_stream_rows = sum(
            multiplicity > 1
            for multiplicity in (
                len(row_streams[(category, row)]) for row in rows))
        assert multiple_stream_rows == expected_multirow_counts[category]
        cross_shape_receipts.append((
            category, multiple_stream_rows,
            tuple(sorted(stream_multiplicity.items())),
            tuple(sorted(provenance_multiplicity.items())),
        ))

    assert all(len(row_streams[("u0_complete", record[11])]) == 1
               and row_provenance[("u0_complete", record[11])] == 1
               for record in minimum)

    return {
        "occurrences_by_class": tuple(sorted(counts.items())),
        "distinct_contact_rows_by_class": tuple(sorted(
            (name, len(rows)) for name, rows in distinct_rows.items())),
        "centered_grade_ranges_by_class": tuple(sorted(grade_ranges.items())),
        "literal_occurrence_sha256": payload_hasher.hexdigest(),
        "minimum_tail_grade_and_contact_weight": minimum_key,
        "minimum_tail_records": tuple(minimum),
        "cross_shape_row_receipts_category_multirow_streamhist_provhist": (
            tuple(cross_shape_receipts)),
        "cross_shape_interpretation": (
            "The minimum grade-2694 sink rows are stream-disjoint and have "
            "one P9 provenance each. Later tails have extensive cross-stream "
            "row collisions (reported exactly), so their aggregate target-"
            "specific coefficients must be retained; local per-shape "
            "capacity does not prove their simultaneous containment."),
        "minimum_tail_formula": (
            "at error nodes: H26(deltaP9_s)(x) * "
            "R^(21-s)S^s Z^2673 = "
            "(N*x^-1)^26 B_s(x) R^(21-s)S^s Z^2673"),
    }


def minimum_tail_augmented_preimage():
    """Give the exact complete-depth, boundary-zero sink for the minimum."""
    records = []
    total_nonzero_operator_rank = 0
    for s in range(CURVATURE + 1):
        r = SLOPE - s
        width0 = H.width(0, r, s)
        qmax0 = CD.complete_qmax(r, s, 0)
        fringe0 = width0 - 30 * N
        b_dimension = 76_927 + s
        hankel_dimension = 54_146 - s
        assert width0 == 8_072_310 + s
        assert qmax0 == 29
        assert fringe0 == 207_990 + s
        assert 30 * N <= width0
        assert 26 <= qmax0
        assert b_dimension < ERRORS

        # The selected Hankel inverse in 14b5109 maps an arbitrary nonzero
        # high quotient vector to a nonzero B_s supported in degree <b_s.
        # Evaluation on E distinct error nodes is injective because b_s<E.
        # Multiplication by (N*x^-1)^26 is an invertible diagonal.
        total_nonzero_operator_rank += hankel_dimension
        records.append({
            "s_r": (s, r),
            "tail_row": (26, 0, r, s, 2_673),
            "tail_centered_grade": 2_694,
            "P0_absorber": (0, r, s, 2_673),
            "P0_active_total_boundary_degrees": (21, 2_694, 0),
            "P0_width_complete_depth_qmax_fringe": (
                width0, 30, qmax0, fringe0),
            "B_degree_bound_and_error_nodes": (b_dimension, ERRORS),
            "nonzero_tail_operator_rank": hankel_dimension,
        })

    assert total_nonzero_operator_rank == 595_551
    return {
        "per_stream_receipts": tuple(records),
        "minimum_tail_operator_total_rank": total_nonzero_operator_rank,
        "nonzero_argument": (
            "the selected q26 Hankel right inverse has B_s-rank 54146-s; "
            "deg B_s<76927+s<81731, so restriction to the 81731 distinct "
            "error nodes is injective, and the H26(Omega^26) diagonal is "
            "nonzero"),
        "exact_augmented_preimage": (
            "Use the legal grade-2694 source Q_s(X)R^(21-s)S^sZ^2673. "
            "Its width contains a complete 30N all-node Hermite section; "
            "set its q26 jet to the negative error-supported tail and the "
            "other q<=29 jets as required by the block recurrence. Since "
            "Y-degree is zero, this creates no lower-contact or u0 tail."),
        "only_new_terms": (
            "unprescribed coefficient jets q>=30, all in the residual "
            "strong-capacity region"),
        "boundary_normal_of_tail_and_absorber": (0, 0, 0, 0),
        "decision": "GREEN_MINIMUM_Q26_U0_TAIL_COMPLETE_DEPTH_SINK",
    }


def triangular_and_packet_quotient_receipt():
    """Orient the whole induced expansion and compute its boundary class."""
    legal_sources = 0
    minimum_outer_z = None
    for grade in range(2_694, L + 1):
        for f in range(10):
            for s in range(CURVATURE + 1):
                r = SLOPE - s
                z = grade - f - r - s
                assert z >= 0
                assert f + r + s <= 30 < J
                assert f + r + s + z == grade <= L
                assert grade > 1
                minimum_outer_z = z if minimum_outer_z is None else min(
                    minimum_outer_z, z)
                legal_sources += 1
    assert legal_sources == 1_100
    assert minimum_outer_z == 2_664

    # A source at centered grade ell and Y-degree y contributes a term with
    # contact degree f and u1-Z choice h at grade ell-(y-f-h).  Equality is
    # the u0-free Pascal diagonal; otherwise the grade strictly falls.
    orientation_checks = 0
    for grade in range(2_694, L + 1):
        for y in range(10):
            for f in range(y + 1):
                for h in range(y - f + 1):
                    u0_power = y - f - h
                    output_grade = grade - u0_power
                    assert output_grade <= grade
                    if u0_power:
                        assert output_grade < grade
                    else:
                        assert h == y - f and f <= y
                    orientation_checks += 1

    packet_rows = set().union(*PS.packet_shape_rows()[1].values())
    assert all(row[2] + row[3] <= 1 and row[4] <= 1
               for row in packet_rows)
    # Every recursive source retains outer R^(21-s)S^s and Z>=2664.
    # More importantly for the augmented quotient, its raw non-X degree is
    # 2694..2703, never one, so the exact first-boundary normal map is zero.
    assert minimum_outer_z > 1
    return {
        "legal_recursive_source_shapes_checked": legal_sources,
        "centered_grade_range": (2_694, 2_703),
        "minimum_outer_passive_Z": minimum_outer_z,
        "triangular_orientation_checks": orientation_checks,
        "orientation": (
            "descending centered grade; at equal grade, descending contact "
            "Y-degree. Positive-u0 terms strictly lower the grade. The "
            "u0-free terms stay at the grade and form the unitriangular "
            "Pascal contact recurrence."),
        "complete_block_action": (
            "At every grade, replace the q<=Q_f prescriptions on the one "
            "physical P_f polynomial by the aggregate correlated RHS; one "
            "common coefficient cancels the whole A^f block."),
        "residual_action": (
            "q>Q_f blocks remain in the strong-capacity quotient; this audit "
            "proves their local license but not their simultaneous section."),
        "exact_first_boundary_normal": (0, 0, 0, 0),
        "boundary_reason": (
            "the literal normal map keeps only raw source monomials of total "
            "non-X degree one; every tail/absorber source has degree at "
            "least2694"),
        "packet_contact_invariant": "packet Z<=1 and R+S<=1",
        "tail_contact_invariant": "tail Z>=2664 and R+S>=21",
        "augmented_packet_quotient_class": (
            "nonzero terminal contact tail with beta=0; it cannot initiate "
            "F0..F3 and must be discharged by the endpoint quotient"),
    }


def main():
    staircase = qmax_staircase_and_residual_capacity()
    census = induced_tail_census()
    minimum = minimum_tail_augmented_preimage()
    quotient = triangular_and_packet_quotient_receipt()
    stable = {
        "scope": (
            "exact structural propagation of the 14b5109 P8/P9 q26 "
            "correction through its first u0/full-contact tails and exact "
            "boundary normal; no global strong-capacity section or packet "
            "prelift"),
        "target_p_N_g_errors_m_D_J_L_slope_curvature": (
            P, N, G, ERRORS, M, H.D, J, L, SLOPE, CURVATURE),
        "upstream_q26_commit": "14b5109",
        "upstream_q26_canonical_sha256": (
            "6389613e383344a60cc67f1f60952ab2277bcf6516fa9d6db2c5dea32d5b2e38"),
        "endpoint_packet_STOP_commit": "4ad9979",
        "exact_F3": "B*(Y-P-(Z-gamma)*q_H)",
        "qmax_staircase_and_capacity": staircase,
        "literal_induced_tail_census": census,
        "smallest_tail_augmented_preimage": minimum,
        "triangular_boundary_packet_quotient": quotient,
        "decision": (
            "GREEN_SMALLEST_U0_TAIL_COMPLETE_DEPTH_SINK__"
            "GREEN_ZERO_BOUNDARY_CLASS__"
            "STOP_GLOBAL_STRONG_CAPACITY_CONFLUENCE_STILL_REQUIRED"),
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
