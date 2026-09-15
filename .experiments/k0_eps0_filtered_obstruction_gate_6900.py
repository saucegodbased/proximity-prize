#!/usr/bin/env python3
"""Exact literal gate for epsilon-zero detection of the K0 face obstruction.

For a passive-cap step ``L -> L+1`` write

    C : old cap-L source -> contact rows of passive degree <= L,
    A : new exact face   -> contact rows of passive degree L+1,
    B : new exact face   -> contact rows of passive degree <= L.

The filtered connecting obstruction is the induced map

    ker(A) -> coker(C),       v |-> [B v].

For each explicitly named row packet E this script computes, by exact ranks
over F_101, the rank of E restricted to ker(A), and the rank of the connecting
obstruction restricted to ``ker(A) intersect ker(E)``.  Thus a zero restricted
rank is exactly the desired kernel inclusion; it is not inferred from a raw
projection rank.

Contact is the corrected literal formal substitution

    X = x + eps,
    Y = u0 + u1*Z + eps*R - eps^2*S + eps^3*T  (mod eps^m).

Boundary evaluation is not part of this gate.  When mentioned for orientation,
the formal boundary convention is S=Hasse_2(P)=P''/2, never ordinary P''.
"""

from __future__ import annotations

from dataclasses import asdict, replace
import gc
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import k0_first_positive_passive_universal_falsifier_6900 as Old  # noqa: E402
from k0_centered_head_y_correction_gate_6900 import (  # noqa: E402
    P, flattened_raw_column,
)


FOUR_POINT_TWO_GB = 4_200_000_000
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
if soft < 0 or soft > FOUR_POINT_TWO_GB:
    resource.setrlimit(resource.RLIMIT_AS, (FOUR_POINT_TWO_GB, hard))


Row = tuple[int, tuple[int, int, int, int, int]]


def contact_column(profile, receipt, monomial) -> dict[Row, int]:
    answer: dict[Row, int] = {}
    for node in receipt.nodes:
        for local, coefficient in flattened_raw_column(
                monomial, node, receipt.u0[node], receipt.u1[node],
                profile.m).items():
            if coefficient % P:
                answer[(node, local)] = coefficient % P
    return answer


def passive_degree(row: Row) -> int:
    # Local coordinates are (eps,S,T,R,Z).  Every one of S,T,R,Z has
    # passive degree one in the associated filtration.
    return sum(row[1][1:])


def exact_rank(columns: tuple[dict[Row, int], ...], rows: tuple[Row, ...],
               label: str) -> int:
    row_index = {row: i for i, row in enumerate(rows)}
    matrix = nmod_mat(len(rows), len(columns), P)
    for j, column in enumerate(columns):
        for row, value in column.items():
            i = row_index.get(row)
            if i is not None:
                matrix[i, j] = value
    print(f"rank {label}: {matrix.nrows()}x{matrix.ncols()}",
          file=sys.stderr, flush=True)
    _, rank = matrix.rref(inplace=True)
    del matrix
    gc.collect()
    return rank


def face_constraint_rank(face_columns: tuple[dict[Row, int], ...],
                         top_rows: tuple[Row, ...],
                         packet_rows: tuple[Row, ...], label: str) -> int:
    """Rank of [A;E] on the face; duplicate row labels stay independent."""
    top_index = {row: i for i, row in enumerate(top_rows)}
    packet_index = {row: i for i, row in enumerate(packet_rows)}
    matrix = nmod_mat(len(top_rows) + len(packet_rows), len(face_columns), P)
    for j, column in enumerate(face_columns):
        for row, value in column.items():
            i = top_index.get(row)
            if i is not None:
                matrix[i, j] = value
            i = packet_index.get(row)
            if i is not None:
                matrix[len(top_rows) + i, j] = value
    print(f"rank face constraints {label}: "
          f"{matrix.nrows()}x{matrix.ncols()}", file=sys.stderr, flush=True)
    _, rank = matrix.rref(inplace=True)
    del matrix
    gc.collect()
    return rank


def masked_combined_rank(base_columns: tuple[dict[Row, int], ...],
                         face_columns: tuple[dict[Row, int], ...],
                         all_rows: tuple[Row, ...],
                         packet_rows: tuple[Row, ...], label: str) -> int:
    """Rank of full contact plus a face-only copy of packet E.

    The packet copy is zero on old columns.  This is the block matrix whose
    rank gives the obstruction on ker[A,E], rather than the misleading rank
    obtained by merely projecting all contact rows to E.
    """
    all_index = {row: i for i, row in enumerate(all_rows)}
    packet_index = {row: i for i, row in enumerate(packet_rows)}
    columns = base_columns + face_columns
    matrix = nmod_mat(len(all_rows) + len(packet_rows), len(columns), P)
    for j, column in enumerate(columns):
        for row, value in column.items():
            matrix[all_index[row], j] = value
            if j >= len(base_columns):
                i = packet_index.get(row)
                if i is not None:
                    matrix[len(all_rows) + i, j] = value
    print(f"rank masked combined {label}: "
          f"{matrix.nrows()}x{matrix.ncols()}", file=sys.stderr, flush=True)
    _, rank = matrix.rref(inplace=True)
    del matrix
    gc.collect()
    return rank


def row_packets(all_rows: tuple[Row, ...], receipt, profile, new_cap: int):
    errors = set(receipt.nodes) - set(receipt.agreement)
    lower = tuple(row for row in all_rows if passive_degree(row) < new_cap)

    def choose(predicate):
        return tuple(row for row in lower
                     if row[0] in errors and predicate(row[1]))

    scalar = lambda local: local[1:] == (0, 0, 0, 0)
    packets = {
        # Primary claim: literally one scalar coordinate at epsilon order zero
        # for each error node.
        "error_eps0_scalar_1e": choose(
            lambda local: scalar(local) and local[0] == 0),
        # Stronger fallback data: every lower-passive row at epsilon order 0
        # on an error node.  This is not a one-row-per-error packet.
        "error_eps0_all_rows": choose(lambda local: local[0] == 0),
        # Precisely <=3e scalar packets, in both orientations of the epsilon
        # filtration.  These should not be confused with all rows in those
        # epsilon layers.
        "error_first3_scalar_le_3e": choose(
            lambda local: scalar(local) and local[0] < min(3, profile.m)),
        "error_last3_scalar_le_3e": choose(
            lambda local: scalar(local) and
            local[0] >= max(0, profile.m - 3)),
        # Whole epsilon-layer diagnostics (larger than 3e in general).
        "error_first3_all_rows": choose(
            lambda local: local[0] < min(3, profile.m)),
        "error_last3_all_rows": choose(
            lambda local: local[0] >= max(0, profile.m - 3)),
    }
    expected_errors = len(errors)
    assert len(packets["error_eps0_scalar_1e"]) == expected_errors
    assert len(packets["error_first3_scalar_le_3e"]) <= 3 * expected_errors
    assert len(packets["error_last3_scalar_le_3e"]) <= 3 * expected_errors
    return tuple(sorted(errors)), packets


def analyze_case(name: str, old_profile, receipt) -> dict[str, object]:
    next_profile = replace(old_profile, L=old_profile.L + 1)
    old_monomials = tuple(Old.K0.support(old_profile))
    old_set = set(old_monomials)
    next_monomials = tuple(Old.K0.support(next_profile))
    face_monomials = tuple(q for q in next_monomials if q not in old_set)
    assert all(sum(q[1:]) == next_profile.L for q in face_monomials)
    assert len(old_monomials) + len(face_monomials) == len(next_monomials)

    print(f"{name}: building {len(old_monomials)} old + "
          f"{len(face_monomials)} face columns", file=sys.stderr, flush=True)
    base_columns = tuple(contact_column(next_profile, receipt, q)
                         for q in old_monomials)
    face_columns = tuple(contact_column(next_profile, receipt, q)
                         for q in face_monomials)
    flattened_raw_column.cache_clear()
    gc.collect()

    all_rows = tuple(sorted(set().union(
        *(set(column) for column in base_columns + face_columns)), key=repr))
    top_rows = tuple(row for row in all_rows
                     if passive_degree(row) == next_profile.L)
    lower_rows = tuple(row for row in all_rows
                       if passive_degree(row) < next_profile.L)
    assert len(all_rows) == len(top_rows) + len(lower_rows)
    assert all(not (set(column) & set(top_rows)) for column in base_columns)
    assert all(passive_degree(row) <= next_profile.L for row in all_rows)

    rank_old = exact_rank(base_columns, lower_rows, f"{name} old C")
    rank_top = exact_rank(face_columns, top_rows, f"{name} top A")
    rank_full = exact_rank(base_columns + face_columns, all_rows,
                           f"{name} full [C B;0 A]")
    obstruction_rank = rank_full - rank_old - rank_top
    assert obstruction_rank >= 0
    top_kernel_dimension = len(face_monomials) - rank_top
    liftable_top_kernel_dimension = top_kernel_dimension - obstruction_rank

    errors, packets = row_packets(
        all_rows, receipt, next_profile, next_profile.L)
    packet_results = []
    for packet_name, packet_rows in packets.items():
        rank_constraints = face_constraint_rank(
            face_columns, top_rows, packet_rows, f"{name} {packet_name}")
        packet_rank_on_top_kernel = rank_constraints - rank_top
        constrained_top_kernel_dimension = (
            top_kernel_dimension - packet_rank_on_top_kernel)

        # If the entire connecting map is zero, every restriction is zero.
        # Otherwise compute the exact masked block rank for this packet.
        if obstruction_rank == 0:
            rank_masked = rank_full
            restricted_obstruction_rank = 0
            masked_rank_shortcut = "whole connecting obstruction already zero"
        else:
            rank_masked = masked_combined_rank(
                base_columns, face_columns, all_rows, packet_rows,
                f"{name} {packet_name}")
            restricted_obstruction_rank = (
                rank_masked - rank_old - rank_constraints)
            masked_rank_shortcut = None
        assert 0 <= restricted_obstruction_rank <= obstruction_rank
        packet_results.append({
            "packet": packet_name,
            "packet_row_count": len(packet_rows),
            "packet_rank_on_associated_top_kernel": packet_rank_on_top_kernel,
            "associated_top_kernel_with_packet_zero_dimension":
                constrained_top_kernel_dimension,
            "packet_zero_and_liftable_dimension":
                constrained_top_kernel_dimension -
                restricted_obstruction_rank,
            "masked_combined_rank": rank_masked,
            "masked_rank_shortcut": masked_rank_shortcut,
            "restricted_connecting_obstruction_rank":
                restricted_obstruction_rank,
            "factorization_kernel_inclusion_holds":
                restricted_obstruction_rank == 0,
        })

    return {
        "name": name,
        "old_profile_n_w_g_m_B_s_U_L_k_n0":
            tuple(asdict(old_profile).values()),
        "new_profile_n_w_g_m_B_s_U_L_k_n0":
            tuple(asdict(next_profile).values()),
        "agreement_nodes": receipt.agreement,
        "error_nodes": errors,
        "candidate_and_tangent_degrees": (
            Old.degree(receipt.polynomial, P),
            Old.degree(receipt.tangent, P)),
        "old_face_column_counts": (len(old_monomials), len(face_monomials)),
        "contact_row_counts_all_lower_top": (
            len(all_rows), len(lower_rows), len(top_rows)),
        "rank_old_C_top_A_full": (rank_old, rank_top, rank_full),
        "associated_top_kernel_dimension": top_kernel_dimension,
        "connecting_obstruction_rank": obstruction_rank,
        "liftable_associated_top_kernel_dimension":
            liftable_top_kernel_dimension,
        "all_associated_top_kernel_lifts": obstruction_rank == 0,
        "packets": tuple(packet_results),
    }


def main() -> None:
    started = time.monotonic()

    m6_l8 = Old.K0.Profile(11, 5, 8, 6, 2, 1, 8, 8, 0, 1)
    m6_receipt = Old.make_custom_receipt(
        m6_l8, P, 0, "random", "mid", "minimal", "arbitrary",
        "alternating", 2)

    # The m4 profile is the F_101 member of the independent first-positive
    # cap suite: cap 5 is its first source-positive cap, so the tested step is
    # L4 -> L5.
    m4_l4 = Old.K0.Profile(6, 2, 4, 4, 2, 1, 6, 4, 0, 1)
    m4_receipt = Old.make_custom_receipt(
        m4_l4, P, 0, "random", "mid", "minimal", "arbitrary",
        "alternating", 2)

    cases = (
        analyze_case("corrected_m6_L8_to_L9", m6_l8, m6_receipt),
        analyze_case("corrected_m4_L4_to_L5", m4_l4, m4_receipt),
    )
    m6, m4 = cases
    assert m6["rank_old_C_top_A_full"] == (4719, 726, 5445)
    assert m6["associated_top_kernel_dimension"] == 133
    assert m6["connecting_obstruction_rank"] == 0
    assert tuple(
        (row["packet_row_count"],
         row["packet_rank_on_associated_top_kernel"],
         row["restricted_connecting_obstruction_rank"])
        for row in m6["packets"]
    ) == ((3, 0, 0), (96, 36, 0), (9, 0, 0), (9, 0, 0),
          (420, 133, 0), (1215, 133, 0))

    assert m4["rank_old_C_top_A_full"] == (539, 180, 734)
    assert m4["associated_top_kernel_dimension"] == 45
    assert m4["connecting_obstruction_rank"] == 15
    assert tuple(
        (row["packet_row_count"],
         row["packet_rank_on_associated_top_kernel"],
         row["restricted_connecting_obstruction_rank"])
        for row in m4["packets"]
    ) == ((2, 2, 15), (32, 16, 15), (6, 6, 15), (6, 5, 15),
          (128, 45, 0), (180, 45, 0))
    error_count_m4 = len(m4["error_nodes"])
    assert m4["connecting_obstruction_rank"] > 3 * error_count_m4
    payload = {
        "scope": (
            "exact filtered lower-grade obstruction of the complete new "
            "passive face; literal formal contact over F_101"
        ),
        "field": P,
        "contact_semantics": (
            "rows (node,eps,S,T,R,Z); "
            "Y=u0+u1*Z+eps*R-eps^2*S+eps^3*T mod eps^m"
        ),
        "filtration_semantics": (
            "passive degree=S+T+R+Z; A is exact degree L+1, B is lower "
            "degree <=L, C is complete old-cap contact"
        ),
        "boundary_convention_guard": (
            "not used by this contact-only obstruction gate; the formal "
            "boundary is S=Hasse2(P)=P''/2"
        ),
        "rank_identity": (
            "rank(obstruction on ker[A,E]) = "
            "rank([full contact; face-only E])-rank(C)-rank([A;E])"
        ),
        "cases": cases,
        "verdict": {
            "m6_L8_to_L9": (
                "GREEN but vacuous for detection: the whole connecting "
                "obstruction is already zero, so all 133 associated-kernel "
                "directions lift without imposing epsilon data"
            ),
            "m4_L4_to_L5": (
                "RED: epsilon-zero scalar, all epsilon-zero, and both "
                "three-scalar packets leave the full rank-15 obstruction; "
                "because e=2 and 15>3e, no uniform factorization through "
                "any <=3e-dimensional terminal packet is possible here"
            ),
            "uniform_consequence": (
                "the proposed factorization is not a generic formal-contact "
                "confluence lemma; a target proof would need additional "
                "target-specific structure"
            ),
        },
        "scope_guard": (
            "finite exact falsification controls only; even GREEN does not "
            "prove target-uniform confluence or the boundary connecting map"
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    payload["runtime"] = {
        "seconds": round(time.monotonic() - started, 3),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "address_space_cap_bytes": FOUR_POINT_TWO_GB,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
