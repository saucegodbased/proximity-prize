#!/usr/bin/env python3
"""Exact target-ratio control for the passive-seed product-rule repair.

The m8 control changes normal rank three to four when one passive reach layer
is added.  This script asks whether that *same* mechanism survives in the two
constant-T target-ratio controls.  For each m=5,6 profile it compares

* the complete literal source at L=7;
* the largest L=8 subsource which adds the new active, Z=0 face but omits the
  positive-Z frontier; and
* the complete literal source at L=8.

Thus the last transition differs only by one passive reach layer.  On the L=7
contact kernel the script computes both the boundary-gradient image and the
extra boundary-value row.  It then shifts every old relation by Z, verifies
its contact image is literally zero, and checks the product rule

    grad(Z*f) = gamma*grad(f) + f*e_Z.

If these direct shifts do not account for the passive-stage rank change, the
script also computes the intrinsic relative connecting rank: compatible new
passive coefficients modulo the old contact kernel, followed by boundary
values modulo the old kernel-boundary image.  All arithmetic is over F_101;
the process installs a hard 3900-MiB address-space limit.
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
import k0_target_ratio_constant_t_gate_6900 as Gate  # noqa: E402
import k0_target_ratio_raw_1rs_layer_gate_6900 as Raw  # noqa: E402
from higher6810_secondjet_retarget_exact import relaxed_rank_bound  # noqa: E402


P = Gate.P
K0 = Gate.K0
LIMIT_BYTES = 3900 * 1024 * 1024
BOUNDARY_XS = (11, 12, 13)


def install_memory_limit() -> None:
    soft, hard = resource.getrlimit(resource.RLIMIT_AS)
    requested = LIMIT_BYTES
    if hard != resource.RLIM_INFINITY:
        requested = min(requested, hard)
    resource.setrlimit(resource.RLIMIT_AS, (requested, requested))


def select_columns(matrix: nmod_mat, columns: tuple[int, ...]) -> nmod_mat:
    return nmod_mat(
        matrix.nrows(), len(columns),
        [int(matrix[i, j])
         for i in range(matrix.nrows()) for j in columns], P)


def select_rows(matrix: nmod_mat, rows: tuple[int, ...]) -> nmod_mat:
    return nmod_mat(
        len(rows), matrix.ncols(),
        [int(matrix[i, j])
         for i in rows for j in range(matrix.ncols())], P)


def horizontal(left: nmod_mat, right: nmod_mat) -> nmod_mat:
    assert left.nrows() == right.nrows()
    return nmod_mat(
        left.nrows(), left.ncols() + right.ncols(),
        [value
         for i in range(left.nrows())
         for value in (
             [int(left[i, j]) for j in range(left.ncols())]
             + [int(right[i, j]) for j in range(right.ncols())])], P)


def vertical(top: nmod_mat, bottom: nmod_mat) -> nmod_mat:
    assert top.ncols() == bottom.ncols()
    return nmod_mat(
        top.nrows() + bottom.nrows(), top.ncols(),
        [int(top[i, j])
         for i in range(top.nrows()) for j in range(top.ncols())]
        + [int(bottom[i, j])
           for i in range(bottom.nrows()) for j in range(bottom.ncols())], P)


def is_zero(matrix: nmod_mat) -> bool:
    return not any(
        int(matrix[i, j]) % P
        for i in range(matrix.nrows()) for j in range(matrix.ncols()))


def kernel_basis(matrix: nmod_mat) -> tuple[nmod_mat, int, int]:
    """Return a cropped exact right-kernel basis, rank, and nullity."""
    padded, nullity = matrix.nullspace()
    basis = nmod_mat(
        matrix.ncols(), nullity,
        [int(padded[i, j])
         for i in range(matrix.ncols()) for j in range(nullity)], P)
    del padded
    rank = matrix.ncols() - nullity
    return basis, rank, nullity


def boundary_matrices(receipt: K0.Receipt, monomials, x: int):
    gradients = tuple(
        K0.monomial_gradient_polys(monomial, receipt)
        for monomial in monomials)
    gradient = nmod_mat(
        4, len(monomials),
        [int(gradients[j][coordinate](x)) % P
         for coordinate in range(4) for j in range(len(monomials))], P)
    value = nmod_mat(
        1, len(monomials),
        [int(K0.monomial_value_poly(monomial, receipt)(x)) % P
         for monomial in monomials], P)
    return gradient, value


def compatible_boundary_basis(image: nmod_mat) -> tuple[tuple[int, ...], ...]:
    padded, nullity = image.transpose().nullspace()
    answer = tuple(
        tuple(int(padded[i, j]) % P for i in range(4))
        for j in range(nullity))
    return answer


def add_to_basis(basis: dict[int, tuple[int, ...]], vector) -> bool:
    residual = [int(entry) % P for entry in vector]
    for pivot in sorted(basis):
        coefficient = residual[pivot]
        if coefficient:
            residual = [
                (entry - coefficient * basis[pivot][i]) % P
                for i, entry in enumerate(residual)]
    pivot = next((i for i, entry in enumerate(residual) if entry), None)
    if pivot is None:
        return False
    inverse = pow(residual[pivot], -1, P)
    basis[pivot] = tuple(entry * inverse % P for entry in residual)
    return True


def first_relative_boundary_witness(
        old_image: nmod_mat, new_image: nmod_mat, new_kernel: nmod_mat,
        old_columns: int) -> dict[str, object] | None:
    basis: dict[int, tuple[int, ...]] = {}
    for j in range(old_image.ncols()):
        add_to_basis(basis, tuple(
            int(old_image[i, j]) for i in range(old_image.nrows())))
    for j in range(new_image.ncols()):
        vector = tuple(
            int(new_image[i, j]) % P for i in range(new_image.nrows()))
        before = len(basis)
        if add_to_basis(basis, vector):
            new_coefficients = tuple(
                (row - old_columns, int(new_kernel[row, j]) % P)
                for row in range(old_columns, new_kernel.nrows())
                if int(new_kernel[row, j]) % P)
            return {
                "kernel_basis_column": j,
                "boundary_vector": vector,
                "old_boundary_rank_before_new_vector": before,
                "new_frontier_coefficient_support_size": len(new_coefficients),
                "new_frontier_coefficients_sha256": hashlib.sha256(
                    repr(new_coefficients).encode()).hexdigest(),
            }
    return None


def transition_summary(
        old_kernel: nmod_mat, new_kernel: nmod_mat,
        old_gradient: nmod_mat, new_gradient: nmod_mat,
        old_columns: int) -> dict[str, object]:
    old_image = old_gradient * old_kernel
    new_image = new_gradient * new_kernel
    old_rank = old_image.rank()
    new_rank = new_image.rank()
    new_coefficient_projection = select_rows(
        new_kernel, tuple(range(old_columns, new_kernel.nrows())))
    projection_rank = new_coefficient_projection.rank()
    expected_projection_rank = new_kernel.ncols() - old_kernel.ncols()
    assert projection_rank == expected_projection_rank
    assert horizontal(old_image, new_image).rank() == new_rank
    return {
        "old_new_kernel_dimensions": (
            old_kernel.ncols(), new_kernel.ncols()),
        "contact_compatible_new_coefficient_dimension": projection_rank,
        "dimension_check_new_nullity_minus_old_nullity":
            expected_projection_rank,
        "old_new_boundary_gradient_ranks": (old_rank, new_rank),
        "relative_connecting_boundary_quotient_rank": new_rank - old_rank,
        "first_boundary_witness_mod_old_image":
            first_relative_boundary_witness(
                old_image, new_image, new_kernel, old_columns),
    }


def run_boundary(
        profile: K0.Profile, receipt: K0.Receipt, monomials,
        base_count: int, prepassive_count: int,
        base_kernel: nmod_mat, prepassive_kernel: nmod_mat,
        full_kernel: nmod_mat, shifted_indices: tuple[int, ...], x: int
        ) -> dict[str, object]:
    gradient, value = boundary_matrices(receipt, monomials, x)
    base_columns = tuple(range(base_count))
    prepassive_columns = tuple(range(prepassive_count))
    base_gradient = select_columns(gradient, base_columns)
    prepassive_gradient = select_columns(gradient, prepassive_columns)
    base_value = select_columns(value, base_columns)

    base_image = base_gradient * base_kernel
    prepassive_image = prepassive_gradient * prepassive_kernel
    full_image = gradient * full_kernel
    base_value_image = base_value * base_kernel
    base_augmented_image = vertical(base_image, base_value_image)

    shifted_gradient = select_columns(gradient, shifted_indices)
    direct_shifted_image = shifted_gradient * base_kernel
    gamma = receipt.seed % P
    formula_shifted_image = nmod_mat(
        4, base_kernel.ncols(),
        [((gamma * int(base_image[row, j]))
          + (int(base_value_image[0, j]) if row == 3 else 0)) % P
         for row in range(4) for j in range(base_kernel.ncols())], P)
    assert direct_shifted_image == formula_shifted_image

    base_rank = base_image.rank()
    prepassive_rank = prepassive_image.rank()
    full_rank = full_image.rank()
    direct_combined_rank = horizontal(
        base_image, direct_shifted_image).rank()
    compatible = compatible_boundary_basis(base_image)
    if base_rank == 3:
        assert len(compatible) == 1
        lambda_z_status: bool | None = compatible[0][3] != 0
    else:
        lambda_z_status = None

    pre_to_full = transition_summary(
        prepassive_kernel, full_kernel,
        prepassive_gradient, gradient, prepassive_count)
    base_to_full = transition_summary(
        base_kernel, full_kernel, base_gradient, gradient, base_count)

    if base_rank != 3:
        direct_classification = "LACK_OF_OLD_RANK3"
    elif lambda_z_status is False:
        direct_classification = "LAMBDA_Z_ZERO"
    elif base_value_image.rank() == 0:
        direct_classification = "VALUE_RANK_FAILURE"
    elif direct_combined_rank < full_rank:
        direct_classification = "DIRECT_SHIFT_INCOMPLETE"
    else:
        direct_classification = "DIRECT_SHIFT_GREEN"

    return {
        "boundary_X": x,
        "stage_boundary_gradient_ranks_L7_prepassive_L8": (
            base_rank, prepassive_rank, full_rank),
        "L7_kernel_gradient_value_augmented_ranks": (
            base_rank, base_value_image.rank(), base_augmented_image.rank()),
        "L7_compatible_boundary_covector_basis_Y_R_S_Z": compatible,
        "unique_L7_lambda_Z_nonzero_if_rank3": lambda_z_status,
        "direct_Z_shift_image_rank_and_old_plus_shift_rank": (
            direct_shifted_image.rank(), direct_combined_rank),
        "direct_Z_shift_boundary_formula_verified": True,
        "direct_shift_classification": direct_classification,
        "relative_transition_L7_to_full_L8": base_to_full,
        "relative_transition_prepassive_to_full_L8": pre_to_full,
    }


def full_contact(profile: K0.Profile, receipt: K0.Receipt, monomials):
    sparse = []
    for monomial in monomials:
        xp, yp, rp, sp, zp = monomial
        column = {}
        for node in receipt.nodes:
            expansion = Raw.translated_column(
                xp, (yp, rp, sp), zp, node,
                receipt.u0[node], receipt.u1[node], profile.m, 2, P)
            for term, coefficient in expansion.items():
                if coefficient:
                    column[(node, term)] = coefficient
        sparse.append(column)
    rows = tuple(sorted(
        set().union(*(set(column) for column in sparse)), key=repr))
    matrix = nmod_mat(
        len(rows), len(monomials),
        [sparse[j].get(row, 0)
         for row in rows for j in range(len(monomials))], P)
    return matrix, len(rows)


def run_profile(profile: K0.Profile) -> dict[str, object]:
    receipt = Gate.constant_t_receipt(profile)
    profile7 = replace(profile, L=profile.L - 1)
    base = K0.support(profile7)
    base_set = set(base)
    full_set = set(K0.support(profile))
    frontier = full_set - base_set
    active_face = tuple(sorted(
        monomial for monomial in frontier if monomial[4] == 0))
    passive_frontier = tuple(sorted(
        monomial for monomial in frontier if monomial[4] > 0))
    assert frontier == set(active_face) | set(passive_frontier)
    assert not (set(active_face) & set(passive_frontier))
    assert all(sum(monomial[1:]) == profile.L
               for monomial in frontier)
    assert all(sum(monomial[1:4]) == profile.L
               for monomial in active_face)
    assert all(monomial[4] > 0 for monomial in passive_frontier)

    # Put the active face before the passive frontier.  The first two prefixes
    # are therefore complete L7 and the maximal pre-passive L8 subsource.
    monomials = base + active_face + passive_frontier
    base_count = len(base)
    prepassive_count = base_count + len(active_face)
    assert set(monomials) == full_set and len(monomials) == len(full_set)
    monomial_index = {monomial: i for i, monomial in enumerate(monomials)}

    shifted = tuple(
        (xp, yp, rp, sp, zp + 1) for xp, yp, rp, sp, zp in base)
    shift_legal = all(monomial in full_set for monomial in shifted)
    assert shift_legal
    shifted_indices = tuple(monomial_index[monomial]
                            for monomial in shifted)
    shifted_already_old = sum(monomial in base_set for monomial in shifted)
    shifted_new_passive = sum(
        monomial in set(passive_frontier) for monomial in shifted)
    assert shifted_already_old + shifted_new_passive == len(shifted)

    contact, contact_rows = full_contact(profile, receipt, monomials)
    print(
        f"m{profile.m} full contact {contact.nrows()}x{contact.ncols()}; "
        "three exact nullspaces", file=sys.stderr, flush=True)
    base_contact = select_columns(contact, tuple(range(base_count)))
    prepassive_contact = select_columns(
        contact, tuple(range(prepassive_count)))
    base_kernel, base_rank, base_nullity = kernel_basis(base_contact)
    print(f"m{profile.m} L7 rank/nullity {base_rank}/{base_nullity}",
          file=sys.stderr, flush=True)
    prepassive_kernel, prepassive_rank, prepassive_nullity = kernel_basis(
        prepassive_contact)
    print(
        f"m{profile.m} prepassive rank/nullity "
        f"{prepassive_rank}/{prepassive_nullity}",
        file=sys.stderr, flush=True)
    full_kernel, full_rank, full_nullity = kernel_basis(contact)
    print(f"m{profile.m} L8 rank/nullity {full_rank}/{full_nullity}",
          file=sys.stderr, flush=True)

    # Literal contact verification for every shifted old-kernel relation.
    shifted_contact = select_columns(contact, shifted_indices) * base_kernel
    assert is_zero(shifted_contact)

    # This is stronger than checking the value row at a few boundary points:
    # every old contact-kernel relation restricts to the zero polynomial on
    # the selected candidate graph.  In this constant-T receipt the candidate
    # and seed are both zero, so only the pure-X strip can contribute.  Its
    # strict width is m*g, while contact gives multiplicity m at all g
    # agreement nodes.
    base_value_polynomials = tuple(
        K0.monomial_value_poly(monomial, receipt) for monomial in base)
    specialized_kernel_values = K0.compose(
        base_value_polynomials, base_kernel, base_nullity)
    nonzero_specialized_values = sum(
        bool(polynomial) for polynomial in specialized_kernel_values)
    assert nonzero_specialized_values == 0
    pure_x_width = max(
        xp + 1 for xp, yp, rp, sp, zp in base
        if (yp, rp, sp, zp) == (0, 0, 0, 0))
    assert pure_x_width == profile.m * profile.agreements

    boundary_cases = tuple(
        run_boundary(
            profile, receipt, monomials, base_count, prepassive_count,
            base_kernel, prepassive_kernel, full_kernel, shifted_indices, x)
        for x in BOUNDARY_XS)

    local7 = relaxed_rank_bound(
        profile7.m, profile7.L, profile7.B, profile7.s, profile7.U)
    local8 = relaxed_rank_bound(
        profile.m, profile.L, profile.B, profile.s, profile.U)
    answer = {
        "profile_n_w_g_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "stage_source_columns_L7_active_face_prepassive_passive_frontier_L8": (
            base_count, len(active_face), prepassive_count,
            len(passive_frontier), len(monomials)),
        "published_local_bounds_and_full_source_margins_L7_L8": (
            (local7, base_count - profile.n * local7),
            (local8, len(monomials) - profile.n * local8)),
        "contact_rows": contact_rows,
        "stage_contact_rank_nullity_L7_prepassive_L8": (
            (base_rank, base_nullity),
            (prepassive_rank, prepassive_nullity),
            (full_rank, full_nullity)),
        "all_complete_L7_Z_shifts_legal_in_full_L8": shift_legal,
        "shifted_columns_already_L7_vs_new_passive_frontier": (
            shifted_already_old, shifted_new_passive),
        "literal_contact_zero_for_every_shifted_L7_kernel_basis_vector": True,
        "old_kernel_candidate_graph_value_polynomials_nonzero_count":
            nonzero_specialized_values,
        "pure_X_strict_width_and_agreement_root_multiplicity_count": (
            pure_x_width, profile.m * profile.agreements),
        "prepassive_active_face_is_not_uniformly_shift_legal": bool(
            active_face),
        "boundary_cases": boundary_cases,
    }
    del contact, base_contact, prepassive_contact
    del base_kernel, prepassive_kernel, full_kernel, shifted_contact
    gc.collect()
    return answer


def main() -> None:
    install_memory_limit()
    started = time.monotonic()
    cases = (run_profile(Gate.EXACT), run_profile(Gate.CEILING))
    expected = {
        5: {
            "source": (3001, 5, 3006, 598, 3604),
            "contact": ((2901, 100), (2906, 100), (3418, 186)),
            "compatible_new": 86,
        },
        6: {
            "source": (3905, 37, 3942, 822, 4764),
            "contact": ((3867, 38), (3904, 38), (4635, 129)),
            "compatible_new": 91,
        },
    }
    for case in cases:
        m = case["profile_n_w_g_m_B_s_U_L_k_n0"][3]
        want = expected[m]
        assert case[
            "stage_source_columns_L7_active_face_prepassive_passive_frontier_L8"
        ] == want["source"]
        assert case[
            "stage_contact_rank_nullity_L7_prepassive_L8"
        ] == want["contact"]
        assert case[
            "old_kernel_candidate_graph_value_polynomials_nonzero_count"
        ] == 0
        for boundary in case["boundary_cases"]:
            assert boundary[
                "stage_boundary_gradient_ranks_L7_prepassive_L8"
            ] == (4, 4, 4)
            assert boundary[
                "L7_kernel_gradient_value_augmented_ranks"
            ] == (4, 0, 4)
            assert boundary["direct_shift_classification"] == (
                "LACK_OF_OLD_RANK3")
            assert boundary[
                "direct_Z_shift_image_rank_and_old_plus_shift_rank"
            ] == (0, 4)
            relative = boundary[
                "relative_transition_prepassive_to_full_L8"]
            assert relative[
                "contact_compatible_new_coefficient_dimension"
            ] == want["compatible_new"]
            assert relative[
                "relative_connecting_boundary_quotient_rank"] == 0
    payload: dict[str, object] = {
        "scope": (
            "exact target-ratio m5/m6 control of the passive-seed "
            "product-rule repair, including the intrinsic relative map"
        ),
        "field": "F_101",
        "hard_address_space_limit_bytes": LIMIT_BYTES,
        "coordinate_order": "Y,R,S,Z; boundary value is the fifth row",
        "cap_comparison": (
            "complete L7; then add only the L8 active/Z=0 face; then add "
            "only the positive-Z L8 frontier"
        ),
        "decisive_verdict": (
            "RED for transport of the m8 rank-three-to-four passive-shift "
            "repair: both controls already have rank four at complete L7 "
            "and at the maximal pre-passive L8 stage; moreover every L7 "
            "old-kernel boundary value is identically zero, so its legal "
            "Z shifts have zero boundary gradient.  The passive relative "
            "connecting quotient has rank zero."
        ),
        "failure_taxonomy": {
            "old_rank3": "FAIL: rank is four in both controls",
            "lambdaZ": (
                "NOT APPLICABLE: there is no residual conormal after the "
                "already-surjective old boundary image"
            ),
            "value_rank": (
                "FAIL independently: value rank on every L7 contact kernel "
                "is zero, polynomially rather than at one specialization"
            ),
            "source_legality": (
                "PASS for all complete-L7 Z shifts into L8; the added active "
                "Z=0 face is deliberately excluded from the shift-closed base"
            ),
            "relative_passive_map": (
                "NO NEW BOUNDARY DIRECTION: quotient rank zero for both "
                "maximal pre-passive-to-full transitions"
            ),
        },
        "cases": cases,
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(
        canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    payload["runtime"] = {
        "seconds": round(time.monotonic() - started, 3),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
