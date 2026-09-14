#!/usr/bin/env python3
"""Exact last-conormal killer audit in the constant-T two-error chamber.

This continues ``k0_constantT_packet_conormal_ablation_6900.py``.  The base
space is the union of all ten legal size-three partial-locator packets.  Its
normal image has dimension three and its unique compatible boundary line is

    lambda = (1, 8, 2, 1) in F_11^(Y,R,S,Z).

Here we add literal raw monomials from the complete relaxed source.  Left
nullspace projection computes the *incremental* contact and augmented ranks,
so every family is tested modulo the entire packet without selecting a
contact pivot.  The audit is one fixed adversarial datum, not a parameter or
random search.
"""

from __future__ import annotations

from collections import defaultdict
import hashlib
from itertools import combinations
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import k0_constantT_packet_conormal_ablation_6900 as Base  # noqa: E402
import higher6810_secondjet_retarget_exact as Target  # noqa: E402


def select_columns(matrix: nmod_mat, columns: tuple[int, ...]) -> nmod_mat:
    return nmod_mat(
        matrix.nrows(), len(columns),
        [int(matrix[i, j])
         for i in range(matrix.nrows()) for j in columns],
        Base.PRIME,
    )


def first_nullspace_columns(matrix: nmod_mat) -> tuple[nmod_mat, int]:
    """Basis columns for the right nullspace returned by python-flint."""
    padded, nullity = matrix.nullspace()
    basis = nmod_mat(
        padded.nrows(), nullity,
        [int(padded[i, j])
         for i in range(padded.nrows()) for j in range(nullity)],
        Base.PRIME,
    )
    return basis, nullity


def dense_contact_on_rows(polynomials, rows: tuple[object, ...]) -> nmod_mat:
    sparse = tuple(Base.expand_contact(poly) for poly in polynomials)
    return nmod_mat(
        len(rows), len(polynomials),
        [sparse[j].get(row, 0)
         for row in rows for j in range(len(polynomials))],
        Base.PRIME,
    )


def family_receipt(label: str, columns: tuple[int, ...],
                   projected_contact: nmod_mat,
                   projected_augmented: nmod_mat) -> dict[str, object]:
    contact_increment = (select_columns(projected_contact, columns).rank()
                         if columns else 0)
    augmented_increment = (select_columns(projected_augmented, columns).rank()
                           if columns else 0)
    return {
        "family": label,
        "raw_columns": len(columns),
        "contact_rank_increment_mod_packet": contact_increment,
        "augmented_rank_increment_mod_packet": augmented_increment,
        "four_boundary_gain_after_adjoining": (
            3 + augmented_increment - contact_increment
        ),
    }


def global_minimum_band_union(
        by_band: dict[tuple[int, int, int, int], list[int]],
        projected_contact: nmod_mat,
        projected_augmented: nmod_mat) -> dict[str, object]:
    """Certify the global 20-column minimum among complete X-band unions.

    A killing 20-column pair is known.  Every band has at least six columns,
    and the three smallest sizes are 6, 7, 8, whose sum is 21.  Therefore a
    smaller union can only be a singleton or pair.  Singletons were already
    exhausted above; here we exhaust precisely the pairs of total size <=20.
    """
    bands = tuple((band, tuple(columns))
                  for band, columns in sorted(by_band.items()))
    sizes = sorted(len(columns) for _, columns in bands)
    assert sizes[:3] == [6, 7, 8]
    tested_pairs = []
    killers = []
    for left, right in combinations(bands, 2):
        names = (left[0], right[0])
        columns = left[1] + right[1]
        if len(columns) > 20:
            continue
        receipt = family_receipt(
            f"complete X-band pair {names}", columns,
            projected_contact, projected_augmented) | {
                "bands_Y_R_S_Z": names,
            }
        tested_pairs.append(receipt)
        if receipt["four_boundary_gain_after_adjoining"] == 4:
            killers.append(receipt)
    minimum = min(row["raw_columns"] for row in killers)
    assert minimum == 20
    assert not any(row["four_boundary_gain_after_adjoining"] == 4 and
                   row["raw_columns"] < minimum for row in tested_pairs)
    return {
        "minimum_raw_columns_among_complete_X_band_unions": minimum,
        "reason_larger_cardinality_cannot_be_smaller": (
            "the three smallest bands have 6+7+8=21 columns"
        ),
        "tested_pair_count_with_at_most_20_columns": len(tested_pairs),
        "all_minimum_killing_pairs": tuple(
            row for row in killers if row["raw_columns"] == minimum),
    }


def main() -> None:
    started = time.monotonic()
    packet = tuple(
        polynomial
        for anchor in combinations(Base.AGREEMENT, Base.PROFILE.w + 1)
        for polynomial in Base.anchor_packet(anchor, 2)
    )
    raw = tuple({monomial: 1} for monomial in Base.MONOMIALS)

    # Use the complete raw contact row universe.  Rows absent from the packet
    # are retained as zero rows; this is essential because a new raw family is
    # allowed to introduce contact coordinates and the conormal may extend to
    # them.
    raw_sparse_contact = tuple(Base.expand_contact(poly) for poly in raw)
    rows = tuple(sorted(set().union(*(set(c) for c in raw_sparse_contact)),
                        key=repr))
    packet_contact = dense_contact_on_rows(packet, rows)
    packet_boundary = Base.dense_boundary(
        tuple(Base.expand_boundary(poly) for poly in packet))
    packet_augmented = Base.stack(packet_contact, packet_boundary)
    raw_contact = nmod_mat(
        len(rows), len(raw),
        [raw_sparse_contact[j].get(row, 0)
         for row in rows for j in range(len(raw))],
        Base.PRIME,
    )
    raw_boundary = Base.dense_boundary(
        tuple(Base.expand_boundary(poly) for poly in raw))
    raw_augmented = Base.stack(raw_contact, raw_boundary)

    packet_contact_rank = packet_contact.rank()
    packet_augmented_rank = packet_augmented.rank()
    assert (packet_contact_rank, packet_augmented_rank) == (297, 300)

    contact_left, contact_left_nullity = first_nullspace_columns(
        packet_contact.transpose())
    augmented_left, augmented_left_nullity = first_nullspace_columns(
        packet_augmented.transpose())
    projected_contact = contact_left.transpose() * raw_contact
    projected_augmented = augmented_left.transpose() * raw_augmented

    # Independent quotient-rank identity controls the projection method.
    assert projected_contact.rank() == raw_contact.rank() - packet_contact_rank
    assert (projected_augmented.rank() ==
            raw_augmented.rank() - packet_augmented_rank)
    assert (raw_contact.rank(), raw_augmented.rank()) == (1280, 1284)

    by_shape: dict[tuple[int, int], list[int]] = defaultdict(list)
    by_band: dict[tuple[int, int, int, int], list[int]] = defaultdict(list)
    by_total_active: dict[int, list[int]] = defaultdict(list)
    for j, (_, yp, rp, sp, zp) in enumerate(Base.MONOMIALS):
        by_shape[(rp, sp)].append(j)
        by_band[(yp, rp, sp, zp)].append(j)
        by_total_active[yp + rp + sp].append(j)

    shape_receipts = tuple(
        family_receipt(
            f"all raw monomials with (R-degree,S-degree)={shape}",
            tuple(columns), projected_contact, projected_augmented)
        | {"shape_R_S": shape}
        for shape, columns in sorted(by_shape.items())
    )
    assert all(row["four_boundary_gain_after_adjoining"] == 4
               for row in shape_receipts)

    band_receipts = tuple(
        family_receipt(
            f"complete X-band at (Y,R,S,Z)={band}",
            tuple(columns), projected_contact, projected_augmented)
        | {"band_Y_R_S_Z": band,
           "X_degrees": (Base.MONOMIALS[columns[0]][0],
                         Base.MONOMIALS[columns[-1]][0])}
        for band, columns in sorted(by_band.items())
    )
    killing_bands = tuple(
        row for row in band_receipts
        if row["four_boundary_gain_after_adjoining"] == 4)
    minimal_killing_band_size = (
        min(row["raw_columns"] for row in killing_bands)
        if killing_bands else None
    )
    smallest_killing_bands = tuple(
        row for row in killing_bands
        if row["raw_columns"] == minimal_killing_band_size)

    # A single column is a useful hard lower bound on how small the repair can
    # be.  This is not a random scan: it exhausts the fixed 1728-column source.
    singleton_receipts = tuple(
        family_receipt(
            f"raw monomial {monomial}", (j,),
            projected_contact, projected_augmented)
        | {"monomial_X_Y_R_S_Z": monomial}
        for j, monomial in enumerate(Base.MONOMIALS)
    )
    killing_singletons = tuple(
        row for row in singleton_receipts
        if row["four_boundary_gain_after_adjoining"] == 4)

    active_receipts = tuple(
        family_receipt(
            f"all raw monomials of active degree {degree}",
            tuple(columns), projected_contact, projected_augmented)
        | {"active_degree_Y_plus_R_plus_S": degree}
        for degree, columns in sorted(by_total_active.items())
    )
    minimum_band_union = global_minimum_band_union(
        by_band, projected_contact, projected_augmented)

    # Literal target analogue of the minimal small-chamber repair.  The two
    # bands are Y^(m+1) and Y^(m+1) Z.  They are source-legal, but their own
    # coefficient count is below even the error-only sum of the elementary
    # two-band local-rank cap 2m.  Hence the small circuit does not scale by a
    # dimension count; a relative recurrence with the packet is indispensable.
    target_m = 47
    target_active = target_m + 1
    target_width = target_m * Target.TARGET_A - Target.W * target_active
    target_pair_columns = 2 * target_width
    target_local_rank_cap = 2 * target_m
    target_errors = Target.N - Target.TARGET_A
    assert (target_width, target_pair_columns, target_local_rank_cap) == (
        2_188_003, 4_376_006, 94)
    assert target_active <= 64
    assert target_active + 1 <= 3757
    assert target_pair_columns - target_errors * target_local_rank_cap == -3_306_708
    assert target_pair_columns - Target.N * target_local_rank_cap == -20_265_530

    def target_source(B: int, s: int, U: int) -> dict[str, int]:
        columns = Target.coefficient_count(
            Target.TARGET_A, target_m, 3757, B, s, U, 0, 1)
        local_rank = Target.relaxed_rank_bound(target_m, 3757, B, s, U)
        return {
            "B": B, "s": s, "U": U,
            "columns": columns,
            "local_rank": local_rank,
            "all_node_margin": columns - Target.N * local_rank,
        }

    full_target_source = target_source(16, 8, 64)
    one_cap_lower_controls = (
        target_source(15, 7, 64),
        target_source(16, 7, 64),
        target_source(16, 8, 63),
    )
    assert full_target_source["all_node_margin"] == 2_371_080
    assert tuple(row["all_node_margin"] for row in one_cap_lower_controls) == (
        -108_395_787_462, -701_011_338, -27_189_454_746)

    payload = {
        "scope": (
            "one exact F11 constant-T/equal-ratio two-error adversary; "
            "all ranks are pivot-free quotient ranks, no random/grid search"
        ),
        "base": {
            "family": "all ten legal partial-locator packets",
            "columns": len(packet),
            "contact_rank": packet_contact_rank,
            "augmented_rank": packet_augmented_rank,
            "four_boundary_gain": 3,
            "unique_compatible_boundary_line_generator_Y_R_S_Z": (1, 8, 2, 1),
        },
        "complete_raw_source": {
            "columns": len(raw),
            "contact_rank": raw_contact.rank(),
            "augmented_rank": raw_augmented.rank(),
            "four_boundary_gain": 4,
        },
        "left_nullity_contact_augmented": (
            contact_left_nullity, augmented_left_nullity),
        "raw_derivative_shape_families": shape_receipts,
        "complete_X_band_summary": {
            "number_of_bands": len(band_receipts),
            "number_of_killing_bands": len(killing_bands),
            "minimum_killing_band_column_count": minimal_killing_band_size,
            "smallest_killing_bands": smallest_killing_bands,
        },
        "singleton_summary": {
            "number_of_raw_monomials": len(singleton_receipts),
            "number_of_killing_singletons": len(killing_singletons),
            "killing_singletons": killing_singletons,
        },
        "active_degree_families": active_receipts,
        "global_minimum_complete_X_band_union": minimum_band_union,
        "target_m47_analogue": {
            "raw_bands_Y_R_S_Z": (
                (target_active, 0, 0, 0),
                (target_active, 0, 0, 1),
            ),
            "X_degree_range_each": (0, target_width - 1),
            "columns": target_pair_columns,
            "source_legality": {
                "weighted_derivative_degree_le_B16": True,
                "curvature_degree_le_s8": True,
                "active_degree_48_le_U64": target_active <= 64,
                "active_plus_seed_49_le_L3757": target_active + 1 <= 3757,
                "strict_X_width_positive": target_width > 0,
            },
            "elementary_local_rank_cap": target_local_rank_cap,
            "margin_against_error_nodes_only": (
                target_pair_columns - target_errors * target_local_rank_cap),
            "margin_against_all_nodes": (
                target_pair_columns - Target.N * target_local_rank_cap),
            "capacity_verdict": (
                "RED standalone: legality is green, but even the error-only "
                "2m sum-rank count has negative margin; target use requires "
                "a proved relative contact recurrence with the packet"
            ),
        },
        "target_full_source_capacity": {
            "full_profile": full_target_source,
            "one_cap_lower_controls": one_cap_lower_controls,
            "verdict": (
                "the full (B,s,U)=(16,8,64) envelope has +2371080; lowering "
                "any one terminal cap in the displayed natural controls is red"
            ),
        },
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    payload["runtime"] = {
        "seconds": round(time.monotonic() - started, 3),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
