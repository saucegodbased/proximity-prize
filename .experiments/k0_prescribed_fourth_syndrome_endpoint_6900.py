#!/usr/bin/env python3
"""Exact prescribed-syndrome endpoint test for the k=0 complete face.

This is intentionally narrower than complete-face strictness.  It selects
controls whose old complete-contact kernel has boundary image rank exactly
three, computes its unique annihilating boundary covector ``ell``, and asks
whether ``ell`` still extends to a contact-row identity after adjoining the
successor face.  Equivalently, it asks whether one liftable face relation has
nonzero ``ell``-boundary syndrome.

All contact and boundary matrices are literal and exact.  Boundary coordinate
S is Hasse_2(P)=P''/2.  The primary profile has 2*g-w=n-1, matching the target
side of the ratio inequality rather than the earlier equality controls.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import asdict, replace
import argparse
import gc
import hashlib
import json
from math import comb
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat, nmod_poly

sys.path.insert(0, ".experiments")
import k0_first_positive_passive_universal_falsifier_6900 as Old  # noqa: E402
import k0_flattened_contact_sweep_regression_6900 as Flat  # noqa: E402


CAP = 4_200_000_000
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
if soft < 0 or soft > CAP:
    resource.setrlimit(resource.RLIMIT_AS, (CAP, hard))


def passive_degree(row):
    # Literal flattened row: (node,eps,S,T,R,Z).
    return sum(row[2:])


def dense_contact(columns, rows, prime):
    row_index = {row: i for i, row in enumerate(rows)}
    matrix = nmod_mat(len(rows), len(columns), prime)
    for j, column in enumerate(columns):
        for row, value in column.items():
            i = row_index.get(row)
            if i is not None:
                matrix[i, j] = value
    return matrix


def dense_boundary(boundaries, prime):
    matrix = nmod_mat(4, len(boundaries), prime)
    for j, vector in enumerate(boundaries):
        for i, value in enumerate(vector):
            matrix[i, j] = value
    return matrix


def dense_contact_boundary(columns, rows, boundaries, prime):
    """Stack contact and four boundary rows without retaining two matrices."""
    row_index = {row: i for i, row in enumerate(rows)}
    offset = len(rows)
    matrix = nmod_mat(offset + 4, len(columns), prime)
    for j, (column, boundary) in enumerate(zip(columns, boundaries)):
        for row, value in column.items():
            i = row_index.get(row)
            if i is not None:
                matrix[i, j] = value
        for i, value in enumerate(boundary):
            matrix[offset + i, j] = value
    return matrix


def compact_nullspace(matrix):
    square, nullity = matrix.nullspace()
    compact = nmod_mat(matrix.ncols(), nullity, [
        int(square[i, j])
        for i in range(matrix.ncols()) for j in range(nullity)
    ], matrix.modulus())
    del square
    gc.collect()
    return compact, nullity


def normalized_column(matrix, column, prime):
    values = [int(matrix[i, column]) % prime
              for i in range(matrix.nrows())]
    first = next(value for value in values if value)
    scale = pow(first, -1, prime)
    return tuple(value * scale % prime for value in values)


def dot(left, right, prime):
    return sum(a * b for a, b in zip(left, right)) % prime


def boundary_column(matrix, column):
    return tuple(int(matrix[i, column]) for i in range(4))


def small_column_rank(columns, prime):
    if not columns:
        return 0
    matrix = nmod_mat(4, len(columns), prime)
    for j, column in enumerate(columns):
        for i, value in enumerate(column):
            matrix[i, j] = value
    return matrix.rank()


def independent_boundary_basis(image, desired, prime):
    selected = []
    rank = 0
    for j in range(image.ncols()):
        column = boundary_column(image, j)
        new_rank = small_column_rank(selected + [column], prime)
        if new_rank > rank:
            selected.append(column)
            rank = new_rank
            if rank == desired:
                return tuple(selected)
    raise AssertionError((rank, desired))


def shape(monomial):
    _x, _y, r, s, _z = monomial
    if s:
        return "S"
    if r == 1:
        return "R"
    if r >= 2:
        return "R2+"
    return "raw"


def witness_receipt(vector, monomials, old_count, prime, receipt, profile):
    support = tuple(
        (i, monomials[i], int(vector[i, 0]) % prime)
        for i in range(vector.nrows()) if int(vector[i, 0]) % prime)
    counts = Counter(
        ("old" if i < old_count else "face", shape(monomial))
        for i, monomial, _ in support)
    face_cells = tuple(sorted(set(
        monomial[1:] for i, monomial, _ in support if i >= old_count)))
    canonical = json.dumps(support, separators=(",", ":"))
    face_support = tuple(
        (monomial, coefficient) for i, monomial, coefficient in support
        if i >= old_count)
    face_polynomials = {}
    raw_only = all(r == 0 and s == 0
                   for (_x, _y, r, s, _z), _coefficient in face_support)
    expected_power = profile.agreements
    z_base = profile.L + 1 - expected_power
    expected_cells = raw_only and all(
        z == z_base + expected_power - y
        for (_x, y, _r, _s, z), _coefficient in face_support)
    if raw_only:
        terms_by_y = {}
        for (x, y, _r, _s, _z), coefficient in face_support:
            terms_by_y.setdefault(y, {})[x] = coefficient
        for y, terms in terms_by_y.items():
            coefficients = [0] * (max(terms) + 1)
            for exponent, coefficient in terms.items():
                coefficients[exponent] = coefficient
            face_polynomials[y] = nmod_poly(coefficients, prime)
    tangent = nmod_poly(list(receipt.tangent), prime)
    carrier_holds = (
        expected_cells and set(face_polynomials) == set(range(
            expected_power + 1)))
    multiplier = nmod_poly([], prime)
    if carrier_holds:
        multiplier = face_polynomials[expected_power]
        if expected_power % 2:
            multiplier = -multiplier
        for y in range(expected_power + 1):
            scalar = comb(expected_power, y)
            if y % 2:
                scalar = -scalar
            expected = multiplier * tangent ** (expected_power - y) * scalar
            if face_polynomials[y] != expected:
                carrier_holds = False
                break
    multiplier_coefficients = tuple(int(value) for value in multiplier.coeffs())
    return {
        "support_size_old_face": (
            len(support),
            sum(i < old_count for i, _, _ in support),
            sum(i >= old_count for i, _, _ in support)),
        "support_by_part_and_shape": tuple(sorted(counts.items())),
        "face_cell_types_Y_R_S_Z": face_cells,
        "face_terms_X_Y_R_S_Z_coefficient": face_support,
        "raw_tangent_power_carrier": {
            "holds": carrier_holds,
            "form": (
                "M(X) * Z^(L+1-g) * (Q(X)*Z-Y)^g, "
                "where g=agreements and Q=tangent"),
            "power_g_and_z_base": (expected_power, z_base),
            "tangent_coefficients": tuple(receipt.tangent),
            "multiplier_coefficients": multiplier_coefficients,
            "multiplier_sha256": hashlib.sha256(json.dumps(
                multiplier_coefficients, separators=(",", ":")).encode()
            ).hexdigest(),
        },
        "support_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
    }


def analyze(name, profile, prime, receipt, extract_witness=True):
    started = time.monotonic()
    successor = replace(profile, L=profile.L + 1)
    old = tuple(Old.K0.support(profile))
    old_set = set(old)
    face = tuple(q for q in Old.K0.support(successor) if q not in old_set)
    monomials = old + face
    assert len(monomials) == len(Old.K0.support(successor))
    assert all(sum(q[1:]) == successor.L for q in face)

    print(f"{name}: build {len(old)} old + {len(face)} face",
          file=sys.stderr, flush=True)
    columns = tuple(Flat.flattened_column(
        successor, receipt, monomial, prime) for monomial in monomials)
    boundaries = tuple(Flat.formal_boundary_gradient(
        monomial, receipt, profile.n, prime) for monomial in monomials)
    rows = tuple(sorted(set().union(*(set(column) for column in columns)),
                        key=repr))
    top_rows = tuple(row for row in rows
                     if passive_degree(row) == successor.L)
    lower_rows = tuple(row for row in rows
                       if passive_degree(row) < successor.L)
    assert all(not (set(column) & set(top_rows))
               for column in columns[:len(old)])

    print(f"{name}: old nullspace", file=sys.stderr, flush=True)
    old_contact = dense_contact(columns[:len(old)], lower_rows, prime)
    old_rank = old_contact.rank()
    old_nullity = len(old) - old_rank
    if extract_witness:
        old_kernel, checked_nullity = compact_nullspace(old_contact)
        assert checked_nullity == old_nullity
        old_boundary_matrix = dense_boundary(boundaries[:len(old)], prime)
        old_boundary_image = old_boundary_matrix * old_kernel
        old_boundary_rank = old_boundary_image.rank()
        assert old_boundary_rank == 3

        # ell is the unique (normalized) covector annihilating the old
        # boundary image.  Therefore ell*D_old lies in row(C_old).
        ell_square, ell_nullity = old_boundary_image.transpose().nullspace()
        assert ell_nullity == 1
        ell = normalized_column(ell_square, 0, prime)
        assert all(dot(ell, boundary_column(old_boundary_image, j), prime) == 0
                   for j in range(old_boundary_image.ncols()))
        old_boundary_basis = independent_boundary_basis(
            old_boundary_image, 3, prime)
        del old_kernel, old_boundary_matrix, old_boundary_image, ell_square
        del old_contact
    else:
        del old_contact
        gc.collect()
        old_augmented = dense_contact_boundary(
            columns[:len(old)], lower_rows, boundaries[:len(old)], prime)
        old_boundary_rank = old_augmented.rank() - old_rank
        assert old_boundary_rank == 3
        del old_augmented
        ell = None
        old_boundary_basis = None
    gc.collect()

    print(f"{name}: top/full nullspaces", file=sys.stderr, flush=True)
    top_contact = dense_contact(columns[len(old):], top_rows, prime)
    top_rank = top_contact.rank()
    del top_contact
    full_contact = dense_contact(columns, rows, prime)
    full_rank = full_contact.rank()
    full_nullity = len(monomials) - full_rank
    if extract_witness:
        full_kernel, checked_nullity = compact_nullspace(full_contact)
        assert checked_nullity == full_nullity
        full_boundary_matrix = dense_boundary(boundaries, prime)
        full_boundary_image = full_boundary_matrix * full_kernel
        full_boundary_rank = full_boundary_image.rank()
        assert full_boundary_rank == 4

        escaping = []
        for j in range(full_nullity):
            boundary = boundary_column(full_boundary_image, j)
            pairing = dot(ell, boundary, prime)
            if not pairing:
                continue
            support = sum(bool(int(full_kernel[i, j]) % prime)
                          for i in range(full_kernel.nrows()))
            escaping.append((support, j, pairing))
        assert escaping
        _, witness_index, pairing = min(escaping)
        scale = pow(pairing, -1, prime)
        witness = nmod_mat(full_kernel.nrows(), 1, [
            int(full_kernel[i, witness_index]) * scale % prime
            for i in range(full_kernel.nrows())
        ], prime)
        witness_boundary_matrix = full_boundary_matrix * witness
        witness_boundary = boundary_column(witness_boundary_matrix, 0)
        assert dot(ell, witness_boundary, prime) == 1
        zero = full_contact * witness
        assert all(int(zero[i, 0]) == 0 for i in range(zero.nrows()))

        boundary_minor_columns = old_boundary_basis + (witness_boundary,)
        boundary_minor = nmod_mat(4, 4, prime)
        for j, column in enumerate(boundary_minor_columns):
            for i, value in enumerate(column):
                boundary_minor[i, j] = value
        boundary_minor_determinant = int(boundary_minor.det()) % prime
        assert boundary_minor_determinant
        witness_result = witness_receipt(
            witness, monomials, len(old), prime, receipt, profile)
        escaping_summary = (witness_index, len(escaping))
    else:
        del full_contact
        gc.collect()
        print(f"{name}: augmented ranks", file=sys.stderr, flush=True)
        full_augmented = dense_contact_boundary(
            columns, rows, boundaries, prime)
        full_boundary_rank = full_augmented.rank() - full_rank
        assert full_boundary_rank == 4
        del full_augmented
        witness_boundary = None
        boundary_minor_columns = None
        boundary_minor_determinant = None
        witness_result = None
        escaping_summary = None

    obstruction = full_rank - old_rank - top_rank
    top_kernel = len(face) - top_rank
    liftable = top_kernel - obstruction
    combined_obstruction = obstruction + (
        full_boundary_rank - old_boundary_rank)
    result = {
        "name": name,
        "field": prime,
        "profile_n_w_g_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "target_ratio_sign_2g_minus_w_minus_n": (
            2 * profile.agreements - profile.w - profile.n),
        "agreement_nodes": receipt.agreement,
        "candidate_tangent_degrees": (
            Old.degree(receipt.polynomial, prime),
            Old.degree(receipt.tangent, prime)),
        "columns_old_face": (len(old), len(face)),
        "rows_lower_top": (len(lower_rows), len(top_rows)),
        "contact_ranks_old_top_full": (old_rank, top_rank, full_rank),
        "contact_nullities_old_full": (old_nullity, full_nullity),
        "top_kernel_obstruction_liftable_dimensions": (
            top_kernel, obstruction, liftable),
        "boundary_image_ranks_old_full": (
            old_boundary_rank, full_boundary_rank),
        "combined_contact_boundary_obstruction_rank": combined_obstruction,
        "relative_prescribed_syndrome_rank": (
            full_boundary_rank - old_boundary_rank),
        "old_missing_covector_Y_R_S_Z": ell,
        "sparsest_escaping_flint_basis_index_and_candidates":
            escaping_summary,
        "normalized_witness_boundary_Y_R_S_Z": witness_boundary,
        "missing_covector_pairing": 1 if extract_witness else None,
        "boundary_minor_columns_and_determinant": (
            boundary_minor_columns, boundary_minor_determinant),
        "witness": witness_result,
        "dual_extension_criterion": {
            "ell_annihilates_old_contact_kernel_boundary": True,
            "ell_fails_to_annihilate_full_contact_kernel_boundary": True,
            "old_contact_row_identity_extends_across_face": False,
            "certificate": (
                "explicit covector/minor/witness" if extract_witness else
                "rank([C;D])-rank(C) changes from 3 to 4"),
        },
        "seconds": round(time.monotonic() - started, 3),
    }
    if extract_witness:
        del full_contact, full_kernel, full_boundary_matrix
    del columns
    gc.collect()
    return result


def make_cases(profile):
    cases = [
        ("prefix_max_minpoly_p101_gamma0", 101,
         Old.make_receipt(profile, 101, 0, 0)),
        ("prefix_max_minpoly_p101_gamma5", 101,
         Old.make_receipt(profile, 101, 0, 5)),
        ("prefix_max_minpoly_p17_gamma0", 17,
         Old.make_receipt(profile, 17, 0, 0)),
        ("spread_mid_minpoly_p101", 101, Old.make_custom_receipt(
            profile, 101, 0, "spread", "mid", "minimal", "poly",
            "varying", 1)),
        ("random_zero_spike_p101", 101, Old.make_custom_receipt(
            profile, 101, 5, "random", "zero", "spike", "poly",
            "alternating", 2)),
    ]
    # Adversarial retained-bad perturbation: preserve u0/agreement at gamma=0
    # but move u1 by the same nonzero amount on all three error nodes.  This no
    # longer equals the recovered tangent polynomial off the agreement set.
    base = Old.make_receipt(profile, 101, 0, 0)
    u1 = list(base.u1)
    for node in set(base.nodes) - set(base.agreement):
        u1[node] = (u1[node] + 1) % 101
    perturbed = Old.K0.Receipt(
        base.nodes, base.agreement, base.seed, base.polynomial, base.u0,
        tuple(u1), base.tangent)
    cases.append(("all_error_directions_plus1_p101", 101, perturbed))
    return cases


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--quick", action="store_true")
    parser.add_argument(
        "--large-only", action="store_true",
        help="run the independent n=12,m=6 target-sign endpoint control")
    parser.add_argument("--summary", action="store_true")
    args = parser.parse_args()
    started = time.monotonic()
    profile = Old.K0.Profile(8, 3, 5, 5, 4, 2, 7, 7, 0, 1)
    cases = make_cases(profile)
    if args.large_only:
        profile = Old.K0.Profile(12, 5, 8, 6, 4, 2, 8, 8, 0, 1)
        cases = [("larger_prefix_max_minpoly_p101", 101,
                  Old.make_receipt(profile, 101, 0, 0))]
    if args.quick:
        cases = cases[:1]
    rows = [analyze(name, profile, prime, receipt,
                    extract_witness=not args.large_only)
            for name, prime, receipt in cases]
    assert all(row["target_ratio_sign_2g_minus_w_minus_n"] < 0
               for row in rows)
    assert all(row["boundary_image_ranks_old_full"] == (3, 4)
               for row in rows)
    assert all(row["relative_prescribed_syndrome_rank"] == 1
               for row in rows)
    payload = {
        "scope": (
            "exact prescribed fourth-boundary-syndrome endpoint on a "
            "target-sign old-rank-three chamber"),
        "contact": (
            "X=x+eps; Y=u0+u1 Z+eps R-eps^2 S+eps^3 T mod eps^m"),
        "boundary": "(Y,R,Hasse2(P),Z) at x=n",
        "cases": rows,
        "verdict": (
            "GREEN in every stated control: although most associated top "
            "directions are obstructed, a liftable direction has nonzero "
            "pairing with the unique missing old boundary covector"),
        "scope_guard": (
            "finite exact mechanism evidence, not a target theorem; all "
            "tested controls satisfy the old-boundary-rank-three premise"),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(
        canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    payload["runtime"] = {
        "seconds": round(time.monotonic() - started, 3),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "address_space_cap_bytes": CAP,
    }
    if args.summary:
        summaries = []
        for row in rows:
            witness = row["witness"]
            if witness is None:
                summaries.append({
                    key: row[key] for key in (
                        "name", "field", "agreement_nodes",
                        "candidate_tangent_degrees",
                        "contact_ranks_old_top_full",
                        "contact_nullities_old_full",
                        "top_kernel_obstruction_liftable_dimensions",
                        "boundary_image_ranks_old_full",
                        "relative_prescribed_syndrome_rank",
                        "seconds")
                } | {"witness": None})
                continue
            face_terms = witness["face_terms_X_Y_R_S_Z_coefficient"]
            summaries.append({
                key: row[key] for key in (
                    "name", "field", "agreement_nodes",
                    "candidate_tangent_degrees", "contact_ranks_old_top_full",
                    "contact_nullities_old_full",
                    "top_kernel_obstruction_liftable_dimensions",
                    "boundary_image_ranks_old_full",
                    "relative_prescribed_syndrome_rank",
                    "old_missing_covector_Y_R_S_Z",
                    "normalized_witness_boundary_Y_R_S_Z",
                    "boundary_minor_columns_and_determinant",
                    "sparsest_escaping_flint_basis_index_and_candidates",
                    "seconds")
            } | {"witness": {
                "support_size_old_face": witness["support_size_old_face"],
                "support_by_part_and_shape":
                    witness["support_by_part_and_shape"],
                "face_cell_type_count": len(
                    witness["face_cell_types_Y_R_S_Z"]),
                "face_cell_types_if_at_most_10": (
                    witness["face_cell_types_Y_R_S_Z"]
                    if len(witness["face_cell_types_Y_R_S_Z"]) <= 10
                    else None),
                "face_terms_if_at_most_10": (
                    face_terms if len(face_terms) <= 10 else None),
                "support_sha256": witness["support_sha256"],
                "raw_tangent_power_carrier":
                    witness["raw_tangent_power_carrier"],
            }})
        payload = {
            "cases": summaries,
            "full_receipt_canonical_sha256": payload["canonical_sha256"],
            "script_sha256": payload["script_sha256"],
            "runtime": payload["runtime"],
        }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
