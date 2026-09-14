#!/usr/bin/env python3
"""Exact carrier-subset discriminator for the k=0 constant-T stress family.

The chamber is the first two-error exact-G control from
``k0_two_error_adjacent_probe_6900``.  Its generic case has

    Q_G(4,5) = (4,10),  u1(4,5) = (7,13),

so both error mismatches equal 3, while both value residuals equal 1.  The
agreement direction has exact degree ``w+1``.  This is therefore the small
literal analogue of the all-anchor scalar-collapse family.

The full relaxed source has only six derivative carrier shapes ``(R,S)``.
We enumerate all 64 shape subsets and compute the exact contact and bordered
ranks over F_101.  The purpose is to identify which non-scalar source shapes
are genuinely load-bearing after the scalar packet has collapsed.  It is a
finite mechanism discriminator, not a target theorem.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import resource
import time

from flint import nmod_mat

import k0_two_error_adjacent_probe_6900 as Base


def stack(top: nmod_mat, bottom: nmod_mat) -> nmod_mat:
    assert top.ncols() == bottom.ncols()
    return nmod_mat(
        top.nrows() + bottom.nrows(), top.ncols(),
        [int(top[i, j])
         for i in range(top.nrows()) for j in range(top.ncols())]
        + [int(bottom[i, j])
           for i in range(bottom.nrows()) for j in range(bottom.ncols())],
        Base.P,
    )


def appended_rank(matrix: nmod_mat, boundary: nmod_mat,
                  boundary_rows: tuple[int, ...]) -> int:
    """Rank after appending the named boundary-coordinate rows."""
    if not boundary_rows:
        return matrix.rank()
    selected = Base.submatrix(
        boundary, boundary_rows, tuple(range(boundary.ncols())))
    return stack(matrix, selected).rank()


def main() -> None:
    started = time.monotonic()
    monomials = Base.K0.support(Base.PROFILE)
    sparse = Base.columns(monomials, 1, 7, 13)
    rows = tuple(sorted(set().union(*(set(c) for c in sparse)), key=repr))
    contact = Base.dense(sparse, rows)
    boundary = Base.boundary(monomials)
    shapes = tuple(sorted(set((rp, sp) for _, _, rp, sp, _ in monomials)))
    assert shapes == ((0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (3, 0))
    assert (contact.rank(), stack(contact, boundary).rank()) == (724, 728)

    answers = []
    for mask in range(1 << len(shapes)):
        selected_shapes = tuple(
            shape for bit, shape in enumerate(shapes) if mask & (1 << bit))
        selected_set = set(selected_shapes)
        columns = tuple(
            j for j, (_, _, rp, sp, _) in enumerate(monomials)
            if (rp, sp) in selected_set)
        if not columns:
            contact_rank = augmented_rank = 0
        else:
            cmat = Base.submatrix(contact, tuple(range(contact.nrows())), columns)
            bmat = Base.submatrix(boundary, tuple(range(4)), columns)
            contact_rank = cmat.rank()
            augmented_rank = stack(cmat, bmat).rank()
        answers.append({
            "mask": mask,
            "shapes": selected_shapes,
            "columns": len(columns),
            "contact_rank": contact_rank,
            "augmented_rank": augmented_rank,
            "conormal_gain": augmented_rank - contact_rank,
        })

    gain4_masks = {row["mask"] for row in answers if row["conormal_gain"] == 4}
    minimal = []
    for row in answers:
        mask = row["mask"]
        if mask not in gain4_masks:
            continue
        if not any(
            proper in gain4_masks
            for proper in range(mask)
            if proper != mask and proper & mask == proper
        ):
            minimal.append(row)

    # Boundary rows are ordered (Y,R,S,Z).  Raw {1,R} supplies exactly the
    # three-dimensional (Y,R,Z) quotient.  Adding raw S then kills the last
    # conormal line.  Record both coordinate orders to distinguish this from
    # the weaker statement that each coordinate is separately visible.
    minimal_mask = sum(
        1 << shapes.index(shape) for shape in ((0, 0), (0, 1), (1, 0)))
    minimal_columns = tuple(
        j for j, (_, _, rp, sp, _) in enumerate(monomials)
        if (rp, sp) in {(0, 0), (0, 1), (1, 0)})
    minimal_contact = Base.submatrix(
        contact, tuple(range(contact.nrows())), minimal_columns)
    minimal_boundary = Base.submatrix(
        boundary, tuple(range(4)), minimal_columns)
    no_curvature_columns = tuple(
        j for j, (_, _, rp, sp, _) in enumerate(monomials)
        if (rp, sp) in {(0, 0), (1, 0)})
    no_curvature_contact = Base.submatrix(
        contact, tuple(range(contact.nrows())), no_curvature_columns)
    no_curvature_boundary = Base.submatrix(
        boundary, tuple(range(4)), no_curvature_columns)
    no_curvature_yrz_then_s = tuple(
        appended_rank(no_curvature_contact, no_curvature_boundary, rows)
        for rows in ((), (0,), (0, 1), (0, 1, 3), (0, 1, 3, 2))
    )
    no_curvature_yrsz = tuple(
        appended_rank(no_curvature_contact, no_curvature_boundary,
                      tuple(range(k)))
        for k in range(5)
    )
    yrz_then_s = tuple(
        appended_rank(minimal_contact, minimal_boundary, rows)
        for rows in ((), (0,), (0, 1), (0, 1, 3), (0, 1, 3, 2))
    )
    yrsz_order = tuple(
        appended_rank(minimal_contact, minimal_boundary, tuple(range(k)))
        for k in range(5)
    )
    assert minimal_mask == 7
    assert no_curvature_yrz_then_s == (351, 352, 353, 354, 354)
    assert no_curvature_yrsz == (351, 352, 353, 353, 354)
    assert yrz_then_s == (507, 508, 509, 510, 511)
    assert yrsz_order == (507, 508, 509, 510, 511)
    assert len(minimal) == 1 and minimal[0]["mask"] == minimal_mask

    payload = {
        "scope": (
            "exact F101 two-error constant-T/constant-ratio carrier-shape "
            "discriminator; finite mechanism test, not a target theorem"
        ),
        "profile_n_w_g_m_B_s_U_L_k_n0": (
            Base.PROFILE.n, Base.PROFILE.w, Base.PROFILE.agreements,
            Base.PROFILE.m, Base.PROFILE.B, Base.PROFILE.s, Base.PROFILE.U,
            Base.PROFILE.L, Base.PROFILE.k, Base.PROFILE.n0,
        ),
        "stress_family": {
            "agreement_Q_values_at_errors": (4, 10),
            "error_u1_values": (7, 13),
            "common_epsilon": 3,
            "common_delta": 1,
            "agreement_direction_degree": "w+1",
        },
        "all_shapes": shapes,
        "full_source_contact_augmented_gain": (724, 728, 4),
        "gain4_subset_count": len(gain4_masks),
        "inclusion_minimal_gain4_subsets": minimal,
        "minimal_raw_1_S_R_boundary_rank_profiles": {
            "boundary_row_order": ("Y", "R", "S", "Z"),
            "raw_1_R_Y_then_R_then_Z_then_S": no_curvature_yrz_then_s,
            "raw_1_R_Y_then_R_then_S_then_Z": no_curvature_yrsz,
            "Y_then_R_then_Z_then_S": yrz_then_s,
            "Y_then_R_then_S_then_Z": yrsz_order,
            "interpretation": (
                "each named boundary coordinate adds one rank; in particular "
                "raw {1,R} supplies Y/R/Z gain 3 and raw S kills the final line"
            ),
        },
        "all_subsets": answers,
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
