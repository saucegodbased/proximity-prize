#!/usr/bin/env python3
"""Exact transport of the raw-1 relative killer from seed 42 to seed 0.

Write the old seed coordinate as ``W`` and the new one as ``Z``.  For a
desired new boundary seed gamma, put

    W = Z + (42 - gamma),
    u0_new = u0_old + (42 - gamma) * u1.

Then ``u0_new + u1*Z = u0_old + u1*W`` and the boundary point is unchanged.
Expanding ``W^z`` uses only powers ``Z^j`` with ``j <= z``.  The literal raw
source is downward-closed in this exponent, so translation is an invertible
source automorphism with no X/active/derivative-degree cost.

The script reconstructs the certified seed-42 relative relation, translates
it to seed zero, and checks source legality, invertibility, literal contact,
boundary normal, conormal pairing, and candidate specialization exactly.
"""

from __future__ import annotations

from dataclasses import asdict, replace
import hashlib
from math import comb
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_poly

sys.path.insert(0, ".experiments")
import k0_degree4_degree5_full_sr_attribution_6900 as Degree  # noqa: E402
import k0_capacity_positive_layer_attribution_6900 as Layer  # noqa: E402


K0 = Degree.K0
P = Degree.P
OLD_SEED = 42
NEW_SEED = 0
DELTA = (OLD_SEED - NEW_SEED) % P
KILLER = (2, 9, 0, 0, 2)


def translate(polynomial, delta):
    """Substitute old W = new Z + delta in a sparse source polynomial."""
    answer = {}
    for (xp, yp, rp, sp, zp), coefficient in polynomial.items():
        for new_zp in range(zp + 1):
            monomial = (xp, yp, rp, sp, new_zp)
            value = (answer.get(monomial, 0)
                     + coefficient * comb(zp, new_zp)
                     * pow(delta, zp - new_zp, P)) % P
            if value:
                answer[monomial] = value
            else:
                answer.pop(monomial, None)
    return answer


def dot(left, right):
    return sum(a * b for a, b in zip(left, right)) % P


def main():
    started = time.monotonic()
    profile10 = replace(Degree.PROFILE, L=10)
    profile11 = replace(Degree.PROFILE, L=11)
    receipt42 = Degree.Full.M8.monomial_tangent_receipt(
        profile10, Degree.TRIAL, 0)
    assert receipt42.seed == OLD_SEED

    base = K0.support(profile10)
    source11_tuple = K0.support(profile11)
    source11 = set(source11_tuple)
    added_raw1 = tuple(sorted(
        (q for q in source11 - set(base)
         if (q[2], q[3]) == (0, 0) and q[4] > 0),
        key=lambda q: (q[1], q[4], q[0])))
    raw_prefix = added_raw1[:added_raw1.index(KILLER) + 1]
    monomials = base + raw_prefix
    assert (len(monomials), monomials[-1]) == (11505, KILLER)

    matrix, _boundaries = Degree.literal_contact_matrix(
        profile11, receipt42, monomials)
    print(f"seed transport source {matrix.nrows()}x{matrix.ncols()}; rref",
          file=sys.stderr, flush=True)
    _, rank = matrix.rref(inplace=True)
    pivots = Layer.pivot_columns(matrix, rank)
    pivot_set = set(pivots)
    final_column = len(monomials) - 1
    assert final_column not in pivot_set
    assert all(column in pivot_set
               for column in range(len(base), final_column))
    assert (rank, len(monomials) - rank) == (11187, 318)

    relation_by_column = {final_column: 1}
    for row, pivot_column in enumerate(pivots):
        coefficient = (-int(matrix[row, final_column])) % P
        if coefficient:
            relation_by_column[pivot_column] = coefficient
    relation42 = {
        monomials[column]: coefficient
        for column, coefficient in relation_by_column.items()}
    relation42_tuple = tuple(sorted(relation42.items()))
    assert hashlib.sha256(repr(relation42_tuple).encode()).hexdigest() == (
        "e72e75718f1c0926a6da43e6d5306e5eeec845aa18fffd13c483418e2fd241ee")

    relation0 = translate(relation42, DELTA)
    inverse = translate(relation0, (-DELTA) % P)
    assert inverse == relation42
    assert set(relation0) <= source11
    assert all(
        (xp, yp, rp, sp, new_zp) in source11
        for xp, yp, rp, sp, zp in relation42
        for new_zp in range(zp + 1))

    u0_zero = tuple(
        (u0 + DELTA * u1) % P
        for u0, u1 in zip(receipt42.u0, receipt42.u1))
    receipt0 = replace(receipt42, seed=NEW_SEED, u0=u0_zero)
    assert all(
        (u0_zero[i] + receipt0.u1[i] * NEW_SEED) % P ==
        (receipt42.u0[i] + receipt42.u1[i] * OLD_SEED) % P
        for i in range(len(receipt0.nodes)))
    node_index = {x: i for i, x in enumerate(receipt0.nodes)}
    assert all(
        int(K0.as_poly(receipt0.polynomial)(x)) % P ==
        (receipt0.u0[node_index[x]] +
         receipt0.u1[node_index[x]] * receipt0.seed) % P
        for x in receipt0.agreement)

    contact0 = {}
    boundary0 = [0, 0, 0, 0]
    specialization0 = nmod_poly([], P)
    for monomial, coefficient in relation0.items():
        for row_key, row_value in Degree.Full.expansions(
                profile11, receipt0, monomial):
            value = (contact0.get(row_key, 0)
                     + coefficient * row_value) % P
            if value:
                contact0[row_key] = value
            else:
                contact0.pop(row_key, None)
        monomial_boundary = Degree.boundary_value(
            profile11, receipt0, monomial)
        boundary0 = [
            (entry + coefficient * monomial_boundary[i]) % P
            for i, entry in enumerate(boundary0)]
        specialization0 += coefficient * K0.monomial_value_poly(
            monomial, receipt0)
    assert not contact0
    assert not specialization0
    boundary0 = tuple(boundary0)
    assert boundary0 == (71, 5, 97, 79)

    conormal0 = tuple(
        int(polynomial(profile11.n)) % P
        for polynomial in K0.tangent_bases(receipt0))
    assert conormal0 == (97, 88, 63, 1)
    conormal_pairing0 = dot(conormal0, boundary0)
    assert conormal_pairing0 == 84

    relation0_tuple = tuple(sorted(relation0.items()))
    payload = {
        "scope": "exact affine seed transport of raw-1 relative killer",
        "field": "F_101",
        "profile": tuple(asdict(profile11).values()),
        "trial": Degree.TRIAL,
        "old_seed_new_seed_delta": (OLD_SEED, NEW_SEED, DELTA),
        "coordinate_change": "W = Z + delta",
        "anchor_change": "u0_new = u0_old + delta*u1",
        "contact_rows_prefix_columns_rank_nullity": (
            matrix.nrows(), len(monomials), rank, len(monomials) - rank),
        "original_and_translated_relation_support_sizes": (
            len(relation42), len(relation0)),
        "original_relation_sha256": hashlib.sha256(
            repr(relation42_tuple).encode()).hexdigest(),
        "translated_relation_sha256": hashlib.sha256(
            repr(relation0_tuple).encode()).hexdigest(),
        "translation_inverse_recovers_original": inverse == relation42,
        "all_translated_monomials_in_L11_source": set(relation0) <= source11,
        "literal_translated_contact_support_size": len(contact0),
        "translated_candidate_specialization_identically_zero":
            not specialization0,
        "translated_boundary_normal": boundary0,
        "translated_conormal_Q_Q1_Q2_1": conormal0,
        "translated_conormal_pairing": conormal_pairing0,
        "general_target_normalization": (
            "for arbitrary gamma choose c=gamma-1 and W=Z-c; then W=1 "
            "at the boundary and u0'=u0+c*u1"),
        "verdict": (
            "GREEN: constant seed translation removes the gamma=0 caveat "
            "for any already-proved nonzero-seed relative repair; it does "
            "not prove that the target relative repair exists"),
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
