#!/usr/bin/env python3
"""Exact audit of the tempting L10 -> L11 Z-shift/value mechanism.

For a contact-kernel source polynomial f and boundary seed gamma,

    grad(Z*f)(p) = gamma * grad(f)(p) + f(p) * e_Z.

Every L10 monomial shifts legally into the passive-reach-only L11 source, and
no active-11/Z=0 column is used.  One exact L10 RREF computes the gradient and
value maps on its kernel.  It also computes the full specialization polynomial
of every canonical kernel relation, rather than trusting one boundary point.
If a shifted normal escapes the old image, the script extracts and literally
checks a witness.  Otherwise it emits an exact RED certificate for this simple
mechanism; the L11 gain must then come from a relative/cokernel relation rather
than Z times an old contact-kernel vector.
"""

from __future__ import annotations

from dataclasses import asdict, replace
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import k0_degree4_degree5_full_sr_attribution_6900 as Degree  # noqa: E402
import k0_capacity_positive_layer_attribution_6900 as Layer  # noqa: E402


K0 = Degree.K0
P = Degree.P


def main():
    started = time.monotonic()
    profile10 = replace(Degree.PROFILE, L=10)
    profile11 = replace(Degree.PROFILE, L=11)
    receipt = Degree.Full.M8.monomial_tangent_receipt(
        profile10, Degree.TRIAL, 0)
    monomials = K0.support(profile10)
    support11 = set(K0.support(profile11))
    shifted_monomials = tuple(
        (x, y, r, s, z + 1) for x, y, r, s, z in monomials)
    assert all(monomial in support11 for monomial in shifted_monomials)
    assert all(monomial[4] > 0 for monomial in shifted_monomials)

    matrix, boundaries = Degree.literal_contact_matrix(
        profile10, receipt, monomials)
    print(f"L10 contact {matrix.nrows()}x{matrix.ncols()}; rref",
          file=sys.stderr, flush=True)
    _, rank = matrix.rref(inplace=True)
    pivots = Layer.pivot_columns(matrix, rank)
    pivot_set = set(pivots)
    nonpivots = tuple(
        column for column in range(len(monomials)) if column not in pivot_set)
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

    monomial_value_polys = tuple(
        K0.monomial_value_poly(monomial, receipt) for monomial in monomials)
    monomial_values = tuple(
        int(polynomial(profile10.n)) % P
        for polynomial in monomial_value_polys)
    pivot_boundary = nmod_mat(
        4, rank,
        [boundaries[column][coordinate]
         for coordinate in range(4) for column in pivots], P)
    nonpivot_boundary = nmod_mat(
        4, nullity,
        [boundaries[column][coordinate]
         for coordinate in range(4) for column in nonpivots], P)
    gradient_image = nonpivot_boundary - pivot_boundary * coefficients
    pivot_value = nmod_mat(
        1, rank, [monomial_values[column] for column in pivots], P)
    nonpivot_value = nmod_mat(
        1, nullity, [monomial_values[column] for column in nonpivots], P)
    value_image = nonpivot_value - pivot_value * coefficients

    value_coefficient_cap = max(len(polynomial)
                                for polynomial in monomial_value_polys)
    pivot_value_polys = nmod_mat(
        value_coefficient_cap, rank,
        [int(monomial_value_polys[column][degree]) % P
         for degree in range(value_coefficient_cap) for column in pivots], P)
    nonpivot_value_polys = nmod_mat(
        value_coefficient_cap, nullity,
        [int(monomial_value_polys[column][degree]) % P
         for degree in range(value_coefficient_cap)
         for column in nonpivots], P)
    residual_value_polys = (
        nonpivot_value_polys - pivot_value_polys * coefficients)
    nonzero_specialization_relations = tuple(
        relation for relation in range(nullity)
        if any(int(residual_value_polys[degree, relation]) % P
               for degree in range(value_coefficient_cap)))

    gradient_rank = gradient_image.rank()
    gradient_and_value = nmod_mat(
        5, nullity,
        [int(gradient_image[row, relation])
         for row in range(4) for relation in range(nullity)]
        + [int(value_image[0, relation])
           for relation in range(nullity)], P)
    gradient_and_value_rank = gradient_and_value.rank()

    gamma = receipt.seed % P
    shifted_image = nmod_mat(
        4, nullity,
        [((gamma * int(gradient_image[row, relation]))
          + (int(value_image[0, relation]) if row == 3 else 0)) % P
         for row in range(4) for relation in range(nullity)], P)
    # Construct row-major concatenation explicitly; the deliberately separate
    # expression avoids any assumption about matrix view/slice support.
    original_and_shifted = nmod_mat(
        4, 2 * nullity,
        [value
         for row in range(4)
         for value in (
             [int(gradient_image[row, relation])
              for relation in range(nullity)]
             + [int(shifted_image[row, relation])
                for relation in range(nullity)])], P)

    normal_basis = {}
    for relation in range(nullity):
        Degree.add_to_basis(normal_basis, tuple(
            int(gradient_image[row, relation]) % P for row in range(4)))
    assert len(normal_basis) == gradient_rank == 3
    witness_relation = None
    for relation in range(nullity):
        shifted = tuple(
            int(shifted_image[row, relation]) % P for row in range(4))
        if Degree.add_to_basis(normal_basis, shifted):
            witness_relation = relation
            break
    assert len(normal_basis) == original_and_shifted.rank()

    coefficient_support = ()
    shifted_contact = {}
    direct_shifted_boundary = None
    original_gradient = None
    boundary_value = None
    formula_shifted_boundary = None
    column = None
    if witness_relation is not None:
        assert len(normal_basis) == 4
        column = nonpivots[witness_relation]
        relation_coefficients = {column: 1}
        for row, pivot_column in enumerate(pivots):
            coefficient = (-int(coefficients[row, witness_relation])) % P
            if coefficient:
                relation_coefficients[pivot_column] = coefficient
        coefficient_support = tuple(sorted(
            (monomials[source], coefficient)
            for source, coefficient in relation_coefficients.items()))

        direct_shifted_boundary_list = [0, 0, 0, 0]
        for source, coefficient in relation_coefficients.items():
            shifted_monomial = shifted_monomials[source]
            for contact_row, contact_value in Degree.Full.expansions(
                    profile11, receipt, shifted_monomial):
                value = (shifted_contact.get(contact_row, 0)
                         + coefficient * contact_value) % P
                if value:
                    shifted_contact[contact_row] = value
                else:
                    shifted_contact.pop(contact_row, None)
            shifted_boundary = Degree.boundary_value(
                profile11, receipt, shifted_monomial)
            direct_shifted_boundary_list = [
                (value + coefficient * shifted_boundary[i]) % P
                for i, value in enumerate(direct_shifted_boundary_list)
            ]
        assert not shifted_contact

        original_gradient = tuple(
            int(gradient_image[row, witness_relation]) % P
            for row in range(4))
        boundary_value = int(value_image[0, witness_relation]) % P
        formula_shifted_boundary = tuple(
            (gamma * original_gradient[row]
             + (boundary_value if row == 3 else 0)) % P
            for row in range(4))
        direct_shifted_boundary = tuple(direct_shifted_boundary_list)
        assert direct_shifted_boundary == formula_shifted_boundary
    tangent_bases = K0.tangent_bases(receipt)
    tangent_jet = tuple(int(base(profile10.n)) % P
                        for base in tangent_bases)
    tangent_on_original = None
    tangent_on_shifted = None
    if witness_relation is not None:
        tangent_on_original = sum(
            a * b for a, b in zip(tangent_jet, original_gradient)) % P
        tangent_on_shifted = sum(
            a * b for a, b in zip(tangent_jet,
                                  formula_shifted_boundary)) % P
        assert tangent_on_original == 0
        assert tangent_on_shifted == boundary_value != 0

    payload = {
        "scope": "exact L10 kernel-value / legal Z-shift fourth-normal mechanism",
        "field": "F_101",
        "L10_and_L11_profiles": (
            tuple(asdict(profile10).values()),
            tuple(asdict(profile11).values())),
        "trial": Degree.TRIAL,
        "agreement_set": receipt.agreement,
        "candidate_and_tangent_degrees": (
            K0.poly_degree(receipt.polynomial),
            K0.poly_degree(receipt.tangent)),
        "contact_rows_columns_rank_nullity": (
            matrix.nrows(), matrix.ncols(), rank, nullity),
        "gradient_rank_and_gradient_plus_value_rank": (
            gradient_rank, gradient_and_value_rank),
        "boundary_value_map_rank": value_image.rank(),
        "specialization_polynomial_coefficient_cap_and_max_degree": (
            value_coefficient_cap, value_coefficient_cap - 1),
        "nonzero_kernel_specialization_polynomial_relations":
            nonzero_specialization_relations,
        "all_kernel_specializations_identically_zero":
            not nonzero_specialization_relations,
        "agreement_multiplicity_root_count": (
            len(receipt.agreement) * profile10.m),
        "shifted_rank_and_original_plus_shifted_rank": (
            shifted_image.rank(), original_and_shifted.rank()),
        "all_L10_monomial_Z_shifts_L11_legal": True,
        "all_shifted_seeds_positive_so_active11_z0_excluded": True,
        "witness_canonical_relation_index_and_last_monomial": (
            witness_relation,
            monomials[column] if column is not None else None),
        "witness_coefficient_support_size": len(coefficient_support),
        "witness_coefficient_support_sha256": hashlib.sha256(
            repr(coefficient_support).encode()).hexdigest(),
        "literal_shifted_contact_support_size": (
            len(shifted_contact) if witness_relation is not None else None),
        "boundary_seed_gamma": gamma,
        "witness_original_gradient_and_value": (
            original_gradient, boundary_value),
        "witness_shifted_boundary_direct_and_formula": (
            direct_shifted_boundary, formula_shifted_boundary),
        "tangent_jet_and_pairings_original_shifted": (
            tangent_jet, tangent_on_original, tangent_on_shifted),
        "verified_identity": (
            "grad(Z*f)(p) = gamma*grad(f)(p) + f(p)*e_Z"
        ),
        "mechanism_verdict": (
            "GO: one Z-shifted old kernel relation supplies a new normal"
            if witness_relation is not None else
            "RED: old-kernel value map is zero; passive gain must be a "
            "relative/cokernel connecting relation"),
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
