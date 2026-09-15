#!/usr/bin/env python3
"""Exact associated-passive-grade gate for the raw-1 last face.

For a raw last-face monomial ``X^a Y^y Z^(L-y)``, discard all contacted
terms of passive total degree below ``L``.  The remaining column is

    (x+eps)^a (u1 Z + eps R - eps^2 S + eps^3 T)^y Z^(L-y).

Hence the raw-1 face is a weighted bivariate Hermite evaluation map in
``(x,u1)``.  For speed this script builds the projection which discards the
``T`` rows and uses the divided-power ``-eps^2*S/2`` normalization.  In every
reported case that projection already attains the universal bivariate-Hermite
row cap.  Since adding ``T`` rows cannot exceed the same factorization cap,
the displayed rank is also the rank of the full formal associated map.

This is deliberately only the associated grade.  A kernel here is necessary
for a cap-L column to have contact correctable by cap L-1.  Full relative
correctability has additional lower-grade/global interpolation obligations.
"""

from __future__ import annotations

from dataclasses import asdict, replace
import gc
from math import comb, factorial
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

sys.path.insert(0, ".experiments")
from flint import nmod_mat  # noqa: E402
from higher_jet_literal_matrix import modular_rank, translated_column  # noqa: E402
import k0_degree4_degree5_full_sr_attribution_6900 as M8  # noqa: E402
import k0_target_ratio_constant_t_gate_6900 as Ratio  # noqa: E402


P = 101
S_FACTOR = (-pow(2, -1, P)) % P


def multinomial4(a: int, b: int, c: int, d: int) -> int:
    total = a + b + c + d
    return (factorial(total) //
            (factorial(a) * factorial(b) * factorial(c) * factorial(d)))


def raw1_last_face(profile):
    """All literal raw-1 coordinates newly born on total face ``L``."""
    D = profile.m * profile.agreements
    answer = []
    for y in range(min(profile.U, profile.L) + 1):
        z = profile.L - y
        for a in range(max(0, D - profile.w * y)):
            answer.append((a, y, z))
    return tuple(answer)


def associated_column(profile, receipt, monomial):
    """Sparse top-passive-degree contact column, with exact Hasse weights."""
    a, y, z = monomial
    assert y + z == profile.L
    answer = {}
    for node, x in enumerate(receipt.nodes):
        u1 = receipt.u1[node] % P
        # iR+iS+iZ=y.  The epsilon order contributed by the contacted
        # derivative variables is iR+2*iS.
        for iR in range(y + 1):
            for iS in range(y - iR + 1):
                iZ = y - iR - iS
                q = iR + 2 * iS
                weight = multinomial4(iR, iS, 0, iZ)
                # `higher_jet_literal_matrix` uses the divided-power S
                # coordinate, hence -eps^2/2.  The Lean associated theorem
                # uses the rescaled S coordinate with coefficient -1; this
                # is an invertible row scaling in F_101 and preserves ranks.
                weight = (weight * pow(u1, iZ, P) *
                          pow(S_FACTOR, iS, P)) % P
                for hx in range(min(a, profile.m - 1 - q) + 1):
                    outer = q + hx
                    if outer >= profile.m:
                        continue
                    value = weight * comb(a, hx) * pow(x, a - hx, P) % P
                    if not value:
                        continue
                    # Contact rows are (epsilon-order,R,S,Z).  The final Z
                    # exponent is z+iZ = L-(iR+iS).
                    row = (node, outer, iR, iS, z + iZ)
                    answer[row] = (answer.get(row, 0) + value) % P
    return {row: value for row, value in answer.items() if value}


def compressed_complete_column(profile, receipt, monomial):
    """Complete contact in the row-isomorphic compressed k=2 model.

    The formal proof ``K0CompressedFormalContactEquiv6900`` maps these rows
    injectively by E -> eps^3*T and V2 -> 2*S and rescales a source column
    with raw-S exponent ``s`` by the nonzero factor ``2^s``.  Thus ranks and
    relative contact kernels agree with the literal flattened formal model.
    Boundary augmentation is intentionally absent: that scaling is not
    compatible with the formal raw-S boundary evaluation.
    """
    xp, yp, rp, sp, zp = monomial
    answer = {}
    for node in receipt.nodes:
        for term, value in translated_column(
                xp, (yp, rp, sp), zp, node, receipt.u0[node],
                receipt.u1[node], profile.m, 2, P).items():
            if value:
                answer[(node, term)] = value
    return answer


def dense_rank(columns):
    rows = tuple(sorted(set().union(*(set(c) for c in columns)), key=repr))
    matrix = nmod_mat(
        len(rows), len(columns),
        [columns[j].get(row, 0)
         for row in rows for j in range(len(columns))],
        P)
    _, rank = matrix.rref(inplace=True)
    del matrix
    gc.collect()
    return rank


def full_relative_contact_control(profile, receipt, face):
    """Raw-1 face modulo complete cap-(L-1), contact rows only."""
    old_profile = replace(profile, L=profile.L - 1)
    old = tuple(Ratio.K0.support(old_profile))
    face_full = tuple((a, y, 0, 0, z) for a, y, z in face)
    old_sparse = tuple(compressed_complete_column(
        profile, receipt, monomial) for monomial in old)
    face_sparse = tuple(compressed_complete_column(
        profile, receipt, monomial) for monomial in face_full)
    old_contact_rank = dense_rank(old_sparse)
    combined_contact_rank = dense_rank(old_sparse + face_sparse)
    relative_rank = combined_contact_rank - old_contact_rank
    return {
        "old_complete_columns": len(old),
        "adjoined_raw1_face_columns": len(face),
        "old_contact_rank": old_contact_rank,
        "combined_contact_rank": combined_contact_rank,
        "relative_contact_rank": relative_rank,
        "relative_contact_kernel": len(face) - relative_rank,
        "boundary_augmentation_scope": (
            "not computed here; formal conjugacy uses raw S=HasseDeriv2 "
            "and compressed V2=ordinary derivative2=2*S"
        ),
    }


def run_case(name, profile, receipt):
    columns = raw1_last_face(profile)
    sparse = [associated_column(profile, receipt, monomial)
              for monomial in columns]
    rank = modular_rank(sparse, P)
    # The image factors through all two-variable Hasse coordinates
    # D_X^h D_U^d of total order <=m-1, giving this universal row cap.
    hermite_rows_per_node = profile.m * (profile.m + 1) // 2
    answer = {
        "name": name,
        "profile_n_w_g_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "columns": len(columns),
        "bivariate_hermite_row_cap": profile.n * hermite_rows_per_node,
        "projected_no_T_sparse_rows": len(
            set().union(*(set(c) for c in sparse))),
        "rank": rank,
        "nullity": len(columns) - rank,
        "injective": rank == len(columns),
        "no_T_projection_saturates_bivariate_cap": (
            rank == profile.n * hermite_rows_per_node),
        "full_formal_with_T_rank": rank,
    }
    assert answer["no_T_projection_saturates_bivariate_cap"]
    if name.startswith("target_ratio"):
        answer["modulo_complete_previous_cap_contact"] = (
            full_relative_contact_control(profile, receipt, columns))
        relative_kernel = answer["modulo_complete_previous_cap_contact"][
            "relative_contact_kernel"]
        answer["associated_kernel_minus_liftable_relative_kernel"] = (
            answer["nullity"] - relative_kernel)
    return answer


def target_count():
    n, w, g, m, U, L = 262144, 131071, 180413, 47, 64, 3757
    D = m * g
    columns = sum(max(0, D - w * y) for y in range(min(U, L) + 1))
    hermite_cap = n * m * (m + 1) // 2
    return {
        "profile_n_w_g_m_U_L": (n, w, g, m, U, L),
        "raw1_last_face_columns": columns,
        "bivariate_hermite_row_cap": hermite_cap,
        "column_minus_row_cap": columns - hermite_cap,
        "consequence": (
            "raw-1 has no dimension-forced associated-grade kernel; "
            "a uniform repair needs special interpolation structure or the "
            "other raw derivative shapes"
        ),
    }


def main():
    started = time.monotonic()
    m8_profile = replace(M8.PROFILE, L=11)
    m8_receipt = M8.Full.M8.monomial_tangent_receipt(
        replace(M8.PROFILE, L=10), M8.TRIAL, 0)
    cases = (
        run_case("m8_positive_last_face", m8_profile, m8_receipt),
        run_case("target_ratio_m5_last_face", Ratio.EXACT,
                 Ratio.constant_t_receipt(Ratio.EXACT)),
        run_case("target_ratio_m6_last_face", Ratio.CEILING,
                 Ratio.constant_t_receipt(Ratio.CEILING)),
    )
    # In all three exact controls the no-T projection already saturates the
    # universal bivariate-Hermite factorization cap.  The full formal map,
    # including T, is squeezed between this rank and the same cap.
    assert tuple((case["columns"], case["rank"], case["nullity"])
                 for case in cases) == (
        (378, 324, 54),
        (180, 165, 15),
        (252, 231, 21),
    )
    assert cases[1]["modulo_complete_previous_cap_contact"] == {
        "old_complete_columns": 3001,
        "adjoined_raw1_face_columns": 180,
        "old_contact_rank": 2901,
        "combined_contact_rank": 3070,
        "relative_contact_rank": 169,
        "relative_contact_kernel": 11,
        "boundary_augmentation_scope": (
            "not computed here; formal conjugacy uses raw S=HasseDeriv2 "
            "and compressed V2=ordinary derivative2=2*S"
        ),
    }
    assert cases[2]["modulo_complete_previous_cap_contact"] == {
        "old_complete_columns": 3905,
        "adjoined_raw1_face_columns": 252,
        "old_contact_rank": 3867,
        "combined_contact_rank": 4115,
        "relative_contact_rank": 248,
        "relative_contact_kernel": 4,
        "boundary_augmentation_scope": (
            "not computed here; formal conjugacy uses raw S=HasseDeriv2 "
            "and compressed V2=ordinary derivative2=2*S"
        ),
    }
    payload = {
        "scope": "exact raw-1 associated-last-face Hermite factor gate",
        "field": "F_101",
        "cases": cases,
        "target_dimension_ledger": target_count(),
        "verdict": (
            "GREEN factorization; RED for a dimension-only raw-1 target "
            "argument: the target raw-1 domain is 17,164,397 below its "
            "universal bivariate-Hermite row cap.  Exact target-ratio "
            "controls exhibit strictness gaps 4 and 17 after quotienting by "
            "the complete old contact.  No boundary-rank claim is made"
        ),
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
