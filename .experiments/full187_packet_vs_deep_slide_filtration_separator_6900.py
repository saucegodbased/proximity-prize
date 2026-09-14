#!/usr/bin/env python3
"""Exact packet/support audit for the committed Full187 deep Hermite slide.

The deep slide in commit 249b160 cancels 7,282 final-grade contact row shapes.
This script asks whether any of those are *raw* rows of the four exact packet
columns and constructs a literal separator for the complete three-layer slide
submodule (including every nonprincipal/lower-grade contact tail).

It intentionally does not promote the separator to the whole Full187 source:
low-passive source columns do hit the packet rows.  The result instead proves
that a packet-to-terminal causal transfer is mandatory before the deep slide
can enter an augmented Schur calculation.
"""

from __future__ import annotations

from collections import Counter
import hashlib
import json
from pathlib import Path
import resource

import full187_ntt_ring_and_deep_hermite_slide_audit_6900 as S
import full187_target_charge13_transposed_four_residue_gate_6900 as T


P = 2_130_706_433
N = 262_144
G = 180_413
M = 60


def packet_shape_rows():
    """Raw non-X row envelope of the exact F0,F1,F2,F3 source shapes.

    F0 uses Y; F1 uses R and Y; F2 uses S, R, and Y; at gamma=P=0,
    F3=B*(Y-Z*q_H) uses Y and Z.  Coefficient Hasse differentiation changes
    only T.  The local order-two substitution of Y contributes scalar, Z, E,
    T*R, and T^2*S terms.  Thus this is an exact support envelope (some scalar
    coefficients may cancel between packet summands, which can only shrink it).
    """
    by_shape = {name: set() for name in ("scalar", "Y", "R", "S", "Z")}
    for q in range(M):
        # A scalar X-polynomial.
        by_shape["scalar"].add((q, 0, 0, 0, 0))
        # R, S, and outer passive Z are unchanged by local substitution.
        by_shape["R"].add((q, 0, 1, 0, 0))
        by_shape["S"].add((q, 0, 0, 1, 0))
        by_shape["Z"].add((q, 0, 0, 0, 1))
        # Y -> u0 + u1*Z + E + T*R - T^2*S/2.
        by_shape["Y"].add((q, 0, 0, 0, 0))
        by_shape["Y"].add((q, 0, 0, 0, 1))
        if q + 3 < M:
            by_shape["Y"].add((q, 1, 0, 0, 0))
        if q + 1 < M:
            by_shape["Y"].add((q + 1, 0, 1, 0, 0))
        if q + 2 < M:
            by_shape["Y"].add((q + 2, 0, 0, 1, 0))

    packets = {
        "F0": set(by_shape["Y"]),
        "F1": set().union(by_shape["R"], by_shape["Y"]),
        "F2": set().union(by_shape["S"], by_shape["R"], by_shape["Y"]),
        # P=gamma=0 in the frozen target, so the literal fourth packet is
        # B*(Y-Z*q_H), never a pure-Z replacement.
        "F3": set().union(by_shape["Y"], by_shape["Z"]),
    }
    for rows in packets.values():
        assert all(z <= 1 and r + s <= 1 and e <= 1
                   for _t, e, r, s, z in rows)
    return by_shape, packets


def canceled_slide_rows():
    f8_terms, f8_rows, _ = S.selected_top_terms(8, 25)
    f7_terms, f7_rows, _ = S.selected_top_terms(7, 26)
    assert (len(f8_terms), len(f8_rows)) == (12_870, 3_870)
    assert (len(f7_terms), len(f7_rows)) == (10_692, 3_412)
    assert f8_rows.isdisjoint(f7_rows)
    rows = f8_rows | f7_rows
    assert len(rows) == 7_282
    # Exact invariant: for f=7/8 on r+s=21, R+S=21+f-aE >=21;
    # their top-passive Z rows are 2675/2674.
    assert all(z in (2674, 2675) and r + s >= 21
               for _t, _e, r, s, z in rows)
    return f8_terms, f7_terms, rows


def q26_audit(f7_terms, canceled_rows):
    canceled_q26 = tuple(term for term in f7_terms if term[4] == 26)
    assert len(canceled_q26) == 396
    assert len({term[-1] for term in canceled_q26}) == 396

    f8_through26, _rows, _ = S.selected_top_terms(8, 26)
    unsupported_f8_q26 = tuple(
        term for term in f8_through26 if term[4] == 26)
    unsupported_rows = {term[-1] for term in unsupported_f8_q26}
    assert len(unsupported_f8_q26) == len(unsupported_rows) == 495
    # q26 can hit a row also reached at q25 after the usual source-s/cS
    # trade.  Therefore "7,282 canceled rows" must mean row shapes touched by
    # canceled provenance, not zero aggregated output coordinates.
    assert len(unsupported_rows & canceled_rows) == 360
    assert len(unsupported_rows - canceled_rows) == 135
    assert all(row[4] == 2674 and row[2] + row[3] >= 21
               for row in unsupported_rows)
    return canceled_q26, unsupported_f8_q26, unsupported_rows


def all_top_terms(f: int):
    terms = []
    for source_s in range(11):
        source_r = 21 - source_s
        for a_e in range(f + 1):
            for c_s in range(f - a_e + 1):
                for q in range(max(0, M - (f + 2 * a_e + c_s))):
                    key = (
                        q + f - a_e + c_s,
                        a_e,
                        source_r + f - a_e - c_s,
                        source_s + c_s,
                        2621 + 61 - f,
                    )
                    terms.append((source_s, f, a_e, c_s, q, key))
    return tuple(terms)


def higher_q_recontamination(f8_terms, f7_terms):
    selected8 = {term[-1] for term in f8_terms}
    selected7 = {term[-1] for term in f7_terms}
    high8_terms = tuple(term for term in all_top_terms(8) if term[4] >= 26)
    high7_terms = tuple(term for term in all_top_terms(7) if term[4] >= 27)
    high8 = {term[-1] for term in high8_terms}
    high7 = {term[-1] for term in high7_terms}
    assert (len(high8_terms), len(high8), len(selected8 & high8)) == (
        8_910, 2_430, 360)
    assert (len(high7_terms), len(high7), len(selected7 & high7)) == (
        7_524, 2_204, 280)
    assert selected8.isdisjoint(selected7)
    assert high8.isdisjoint(high7)

    # The 33 principal rows are nevertheless clean.  The exhaustive raw
    # provenance audit in ba5d126 found exactly their 80 listed contributors;
    # reconstruct the keys here and independently exclude all higher-q terms.
    principal = set()
    for f, a_e, c_s in ((7, 6, 1), (8, 5, 3), (8, 6, 1)):
        for output_s in range(11):
            principal.add((
                f - a_e + c_s,
                a_e,
                21 - output_s + f - a_e - c_s,
                output_s + c_s,
                2621 + 61 - f,
            ))
    assert len(principal) == 33
    assert principal.isdisjoint(high8 | high7)
    clean_selected = (selected8 - high8) | (selected7 - high7)
    assert len(clean_selected) == 6_642
    return {
        "higher_q_provenance_f8_f7": (len(high8_terms), len(high7_terms)),
        "higher_q_distinct_rows_f8_f7": (len(high8), len(high7)),
        "selected_rows_recontaminated_f8_f7": (
            len(selected8 & high8), len(selected7 & high7)),
        "selected_rows_support_clean_after_higher_q": len(clean_selected),
        "principal_A_B_C_rows_support_clean_after_higher_q": len(principal),
        "interpretation": (
            "termwise cancellation is exact, but 640 selected row shapes "
            "still receive unsupported higher-q provenance"
        ),
    }


def main():
    shape_rows, packet_rows = packet_shape_rows()
    f8_terms, f7_terms, slide_rows = canceled_slide_rows()
    canceled_q26, unsupported_q26, unsupported_q26_rows = q26_audit(
        f7_terms, slide_rows)
    recontamination = higher_q_recontamination(f8_terms, f7_terms)

    intersections = {
        name: tuple(sorted(slide_rows & rows))
        for name, rows in packet_rows.items()
    }
    assert all(not intersection for intersection in intersections.values())
    assert all(not (unsupported_q26_rows & rows)
               for rows in packet_rows.values())

    # Build the actual frozen target F3 scalar error syndrome.  At the first
    # error node, lambda is the normalized coordinate projection onto
    # (T,E,R,S,Z)=(0,0,0,0,0).  Every source in the complete slide submodule
    # has initial passive exponent at least 2621 and contact substitution never
    # decreases it, so lambda annihilates *all* its tails, not just 7,282 heads.
    instance = T.build_target_instance()
    b0 = instance.f3_selected_error_syndrome[0]
    assert b0 != 0
    inverse_b0 = pow(b0, -1, P)
    assert b0 * inverse_b0 % P == 1
    separator_row = (G, 0, 0, 0, 0, 0)  # node plus (T,E,R,S,Z)

    slide_source_layers = ((61, 2621), (8, 2674), (7, 2675))
    assert min(z for _y, z in slide_source_layers) == 2621
    # For a source Z^z, every contact monomial has output Z exponent z+h,
    # h>=0.  Hence no term in any layer can reach separator_row's Z=0.
    complete_tail_minimum_z = min(z for _y, z in slide_source_layers)
    assert complete_tail_minimum_z > separator_row[-1]

    packet_union = set().union(*packet_rows.values())
    stable = {
        "scope": (
            "exact raw packet-vs-deep-slide support separation; literal "
            "F3 separator for the complete three-layer slide submodule; "
            "not a dual for the whole Full187 source"
        ),
        "target_p_N_g_m": (P, N, G, M),
        "exact_packets": {
            "F0": "Lambda_G^59*Y",
            "F1": "Lambda_G^58*(Lambda_G*R-Lambda_G'*Y)",
            "F2": (
                "Lambda_G^57*(Lambda_G^2*S-2Lambda_G Lambda_G'*R+"
                "(2Lambda_G'^2-Lambda_G Lambda_G'')*Y)"
            ),
            "F3": "B*(Y-P-(Z-gamma)*q_H); frozen P=gamma=0",
            "pure_Z1_rejected": True,
        },
        "raw_packet_shape_row_counts": tuple(
            (name, len(rows)) for name, rows in sorted(packet_rows.items())),
        "raw_packet_union_row_count": len(packet_union),
        "raw_packet_support_invariant": "Z<=1, R+S<=1, E<=1",
        "deep_slide": {
            "cancelled_original_provenance_terms": len(f8_terms) + len(f7_terms),
            "cancelled_distinct_rows": len(slide_rows),
            "cancelled_support_invariant": "Z in {2674,2675}, R+S>=21",
            "packet_intersection_counts": tuple(
                (name, len(intersection))
                for name, intersection in sorted(intersections.items())),
            "packet_relevant_cancelled_rows": 0,
            "higher_q_recontamination": recontamination,
            "q26_canceled_f7_provenance_and_rows": (
                len(canceled_q26), len({term[-1] for term in canceled_q26})),
            "q26_first_unsupported_f8_provenance_and_rows": (
                len(unsupported_q26), len(unsupported_q26_rows)),
            "q26_first_unsupported_rows_already_in_selected_shape_union": (
                len(unsupported_q26_rows & slide_rows)),
            "q26_packet_intersection": 0,
        },
        "literal_augmented_separator": {
            "error_node_index": G,
            "contact_coordinate_node_T_E_R_S_Z": separator_row,
            "contact_weight": inverse_b0,
            "boundary_covector": (0, 0, 0, 0),
            "F3_pairing": 1,
            "F3_unscaled_coordinate": b0,
            "annihilates_every_contact_tail_of_slide_layers": True,
            "slide_layers_y_z": slide_source_layers,
            "minimum_slide_output_Z": complete_tail_minimum_z,
            "F3_syndrome_hash": instance.hashes[
                "F3_selected_error_syndrome_on_E_u32_le"],
            "whole_source_dual": False,
        },
        "rigorous_stop": (
            "The deep slide has no raw packet row and cannot by itself be "
            "Rlt13(Fi). A complete proof must first construct a low-passive "
            "packet correction/precycle, retain its causal higher-Z tail, "
            "and only then show that the terminal tail enters the deep-slide "
            "or mixed pivot/capacity image."
        ),
        "decision": (
            "RED_DIRECT_PACKET_TO_DEEP_SLIDE__GO_CAUSAL_LOWZ_TO_TERMINAL_TRANSFER"
        ),
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
