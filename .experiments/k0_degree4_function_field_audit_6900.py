#!/usr/bin/env python3
"""Function-field audit of the degree-four L=10 full-source control.

This reuses one literal contact RREF.  Its canonical nonpivot relations are
applied simultaneously to boundary gradients at X=9,10,11 and to the exact
polynomial tangent contractions against (Q,Q',Q'',1).  Thus it distinguishes
a rank-three accident at X=9 from a genuine rank-three function-field image
without a second augmented elimination.
"""

from __future__ import annotations

from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat, nmod_poly

sys.path.insert(0, ".experiments")
import k0_degree4_degree5_full_sr_attribution_6900 as Degree  # noqa: E402
import k0_capacity_positive_layer_attribution_6900 as Layer  # noqa: E402


K0 = Degree.K0
P = Degree.P
PROFILE = Degree.PROFILE
BOUNDARY_XS = (9, 10, 11)


def agreement_locator(receipt):
    answer = nmod_poly([1], P)
    for x in receipt.agreement:
        answer *= nmod_poly([(-x) % P, 1], P)
    return answer


def main():
    started = time.monotonic()
    profile = PROFILE
    receipt = Degree.Full.M8.monomial_tangent_receipt(
        profile, Degree.TRIAL, 0)
    assert K0.poly_degree(receipt.tangent) == 4
    _groups, monomials = Degree.ordered_source(profile)
    matrix, _boundary_x9 = Degree.literal_contact_matrix(
        profile, receipt, monomials)

    tangent_bases = K0.tangent_bases(receipt)
    gradients = []
    pairings = []
    boundary_values = {x: [] for x in BOUNDARY_XS}
    for monomial in monomials:
        gradient = K0.monomial_gradient_polys(monomial, receipt)
        gradients.append(gradient)
        pairing = sum(
            (a * b for a, b in zip(tangent_bases, gradient)),
            nmod_poly([], P))
        pairings.append(pairing)
        for x in BOUNDARY_XS:
            boundary_values[x].append(tuple(
                int(coordinate(x)) % P for coordinate in gradient))

    print(f"degree4 literal contact {matrix.nrows()}x{matrix.ncols()}; rref",
          file=sys.stderr, flush=True)
    _, rank = matrix.rref(inplace=True)
    pivots = Layer.pivot_columns(matrix, rank)
    pivot_set = set(pivots)
    nonpivots = tuple(
        j for j in range(len(monomials)) if j not in pivot_set)
    nullity = len(nonpivots)
    assert (rank, nullity) == (10861, 317)

    coefficients = nmod_mat(rank, nullity, P)
    for relation, column in enumerate(nonpivots):
        for row in range(rank):
            value = int(matrix[row, column]) % P
            if value:
                coefficients[row, relation] = value
        if (relation + 1) % 50 == 0:
            print(f"relation coefficients {relation + 1}/{nullity}",
                  file=sys.stderr, flush=True)

    evaluation_rows = tuple(
        (x, coordinate) for x in BOUNDARY_XS for coordinate in range(4))
    pivot_boundary = nmod_mat(
        len(evaluation_rows), rank,
        [boundary_values[x][column][coordinate]
         for x, coordinate in evaluation_rows for column in pivots], P)
    nonpivot_boundary = nmod_mat(
        len(evaluation_rows), nullity,
        [boundary_values[x][column][coordinate]
         for x, coordinate in evaluation_rows for column in nonpivots], P)
    residual_boundary = nonpivot_boundary - pivot_boundary * coefficients

    boundary_audit = []
    for x_index, x in enumerate(BOUNDARY_XS):
        rows = tuple(range(4 * x_index, 4 * x_index + 4))
        image = nmod_mat(
            4, nullity,
            [int(residual_boundary[row, relation])
             for row in rows for relation in range(nullity)], P)
        image_rank = image.rank()
        tangent_jet = tuple(int(base(x)) % P for base in tangent_bases)
        tangent_annihilates = all(
            sum(tangent_jet[i] * int(image[i, j])
                for i in range(4)) % P == 0
            for j in range(nullity))
        boundary_audit.append({
            "X": x,
            "rank": image_rank,
            "tangent_jet_Q_Q1_Q2_1": tangent_jet,
            "tangent_jet_annihilates_every_kernel_normal":
                tangent_annihilates,
        })

    coefficient_cap = max(len(pairing) for pairing in pairings)
    pivot_pairing = nmod_mat(
        coefficient_cap, rank,
        [int(pairings[column][degree]) % P
         for degree in range(coefficient_cap) for column in pivots], P)
    nonpivot_pairing = nmod_mat(
        coefficient_cap, nullity,
        [int(pairings[column][degree]) % P
         for degree in range(coefficient_cap) for column in nonpivots], P)
    residual_pairing = nonpivot_pairing - pivot_pairing * coefficients
    nonzero_pairing_columns = tuple(
        relation for relation in range(nullity)
        if any(int(residual_pairing[degree, relation]) % P
               for degree in range(coefficient_cap)))

    locator_power = agreement_locator(receipt) ** profile.m
    locator_power_degree = len(locator_power) - 1
    quotient_constant_and_remainder_zero = []
    for relation in nonzero_pairing_columns:
        polynomial = nmod_poly([
            int(residual_pairing[degree, relation]) % P
            for degree in range(coefficient_cap)], P)
        quotient, remainder = divmod(polynomial, locator_power)
        quotient_constant_and_remainder_zero.append(
            (len(quotient) <= 1, not bool(remainder)))

    exact_function_field_rank = None
    if not nonzero_pairing_columns and any(
            row["rank"] == 3 for row in boundary_audit):
        # Every kernel normal is annihilated by a nonzero polynomial tangent
        # jet, giving rank <=3 over F_P(X); one rank-three specialization gives
        # the reverse inequality.
        exact_function_field_rank = 3

    payload = {
        "scope": "exact degree4 full-source function-field normal-rank audit",
        "field": "F_101",
        "profile_n_w_A_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "trial": Degree.TRIAL,
        "agreement_set": receipt.agreement,
        "candidate_and_tangent_degrees": (
            K0.poly_degree(receipt.polynomial),
            K0.poly_degree(receipt.tangent)),
        "contact_rows_columns_rank_nullity": (
            matrix.nrows(), matrix.ncols(), rank, nullity),
        "boundary_specializations": boundary_audit,
        "raw_tangent_pairing_max_degree": coefficient_cap - 1,
        "agreement_locator_power_degree": locator_power_degree,
        "nonzero_kernel_tangent_pairing_columns": nonzero_pairing_columns,
        "all_nonzero_pairings_are_constant_times_locator_power": all(
            constant and remainder_zero
            for constant, remainder_zero in
            quotient_constant_and_remainder_zero),
        "all_kernel_tangent_pairings_identically_zero":
            not nonzero_pairing_columns,
        "exact_function_field_boundary_rank": exact_function_field_rank,
        "interpretation": (
            "rank three is function-field exact only when every tangent "
            "pairing vanishes identically and a rank-three specialization "
            "exists"
        ),
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
