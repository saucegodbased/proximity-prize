#!/usr/bin/env python3
"""Extract the first critical raw-S relations and boundary factors exactly.

This is deliberately one receipt, not a scan.  It refines the m=5
constant-T control at the first successful filtration prefix

  V_<m = raw {1,R} + {X^a Y^y S Z^z : y < m}

by adjoining ``X^a Y^m S`` in increasing X degree.  For each genuinely new
kernel relation it records its critical pivots, the lower layers it uses, and
the exact factorization of all four boundary-gradient polynomials over F_101.
The factorization is invariant up to the displayed normalization scalar.
"""

from __future__ import annotations

from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat, nmod_poly

sys.path.insert(0, ".experiments")
import k0_target_ratio_constant_t_gate_6900 as Gate  # noqa: E402
import k0_target_ratio_raw_1rs_layer_gate_6900 as Shape  # noqa: E402
import k0_target_ratio_raw_s_active_filtration_6900 as Active  # noqa: E402


K0 = Gate.K0
P = Gate.P


def poly_coefficients(poly: nmod_poly) -> tuple[int, ...]:
    return tuple(int(poly[i]) for i in range(len(poly)))


def factor_receipt(poly: nmod_poly):
    if not poly:
        return {"zero": True}
    unit, factors = poly.factor()
    return {
        "degree": poly.degree(),
        "leading_coefficient": int(poly[poly.degree()]),
        "coefficient_sha256": hashlib.sha256(json.dumps(
            poly_coefficients(poly), separators=(",", ":")).encode()
        ).hexdigest(),
        "factorization_unit": int(unit),
        "monic_factors_coefficients_multiplicity": tuple(
            (poly_coefficients(factor), multiplicity)
            for factor, multiplicity in factors),
    }


def gradient_polynomials(monomials, columns, kernel, relation, receipt):
    answer = [nmod_poly([], P) for _ in range(4)]
    for row, source_column in enumerate(columns):
        coefficient = int(kernel[row, relation])
        if not coefficient:
            continue
        gradients = K0.monomial_gradient_polys(
            monomials[source_column], receipt)
        for coordinate in range(4):
            answer[coordinate] += coefficient * gradients[coordinate]
    return tuple(answer)


def support_receipt(monomials, columns, kernel, relation):
    terms = tuple(
        (monomials[source_column], int(kernel[row, relation]))
        for row, source_column in enumerate(columns)
        if int(kernel[row, relation]))
    by_shape = Counter((q[2], q[3]) for q, _ in terms)
    by_s_y = Counter(q[1] for q, _ in terms if q[3] == 1)
    ranges = defaultdict(lambda: [10**9, -1, 10**9, -1, 0])
    for (xp, yp, rp, sp, zp), _ in terms:
        key = (rp, sp, yp)
        row = ranges[key]
        row[0] = min(row[0], xp)
        row[1] = max(row[1], xp)
        row[2] = min(row[2], zp)
        row[3] = max(row[3], zp)
        row[4] += 1
    return {
        "nonzero_terms": len(terms),
        "counts_by_R_S_shape": tuple(sorted(by_shape.items())),
        "counts_by_S_Y_degree": tuple(sorted(by_s_y.items())),
        "support_Xmin_Xmax_Zmin_Zmax_count_by_R_S_Y": tuple(
            (key, tuple(value)) for key, value in sorted(ranges.items())),
        "coefficient_list_sha256": hashlib.sha256(json.dumps(
            terms, separators=(",", ":")).encode()).hexdigest(),
    }


def main() -> None:
    started = time.monotonic()
    profile = Gate.EXACT
    receipt = Gate.constant_t_receipt(profile)
    monomials = K0.support(profile)
    contact = Shape.full_contact(profile, receipt, monomials)
    # Spell out the filtration locally so this extractor remains auditable.
    base = tuple(j for j, (_, _, rp, sp, _) in enumerate(monomials)
                 if (rp, sp) in {(0, 0), (1, 0)})
    subcritical = tuple(
        j for j, (_, yp, rp, sp, _) in enumerate(monomials)
        if (rp, sp) == (0, 1) and yp < profile.m)
    critical = tuple(
        j for j, (_, yp, rp, sp, zp) in enumerate(monomials)
        if (rp, sp, yp, zp) == (0, 1, profile.m, 0))
    columns = base + subcritical + critical
    cmat = Shape.select_columns(contact, columns)
    kernel, nullity = cmat.nullspace()
    pre_kernel_dimension = Active.analyze(
        contact, Shape.full_boundary(receipt, monomials, profile.n),
        monomials, base + subcritical)[
            "columns_contact_rank_kernel_boundary_gain"][2]

    critical_rows = tuple(range(len(base) + len(subcritical), len(columns)))
    new_relations = tuple(
        relation for relation in range(nullity)
        if any(int(kernel[row, relation]) for row in critical_rows))
    assert len(new_relations) == nullity - pre_kernel_dimension == 3

    answers = []
    s_polynomials = []
    for relation in new_relations:
        critical_terms = tuple(
            (monomials[columns[row]][0], int(kernel[row, relation]))
            for row in critical_rows if int(kernel[row, relation]))
        gradients = gradient_polynomials(
            monomials, columns, kernel, relation, receipt)
        s_polynomials.append(gradients[2])
        answers.append({
            "critical_X_degree_and_coefficient": critical_terms,
            "support": support_receipt(
                monomials, columns, kernel, relation),
            "boundary_gradient_Y_R_S_Z_factorizations": tuple(
                factor_receipt(poly) for poly in gradients),
        })

    common_s_factor = s_polynomials[0]
    for poly in s_polynomials[1:]:
        common_s_factor = common_s_factor.gcd(poly)
    agreement_locator = nmod_poly([1], P)
    for x in receipt.agreement:
        agreement_locator *= nmod_poly([(-x) % P, 1], P)
    tangent_second = K0.as_poly(
        K0.derivative_coefficients(receipt.tangent, 2))

    payload = {
        "scope": (
            "exact first new relations after the full subcritical raw-S "
            "staircase in the deterministic m5 constant-T control"
        ),
        "field": "F_101",
        "profile_n_w_A_m_B_s_U_L_k_n0": tuple(profile.__dict__.values()),
        "filtration_sizes_base_subcritical_critical": (
            len(base), len(subcritical), len(critical)),
        "precritical_and_postcritical_kernel_dimensions": (
            pre_kernel_dimension, nullity),
        "new_relations": tuple(answers),
        "common_boundary_S_factor": factor_receipt(common_s_factor),
        "tangent_second_derivative": factor_receipt(tangent_second),
        "tangent_second_derivative_divides_each_boundary_S_polynomial":
            tuple(not (poly % tangent_second) for poly in s_polynomials),
        "tangent_second_derivative_divides_common_boundary_S_factor":
            not (common_s_factor % tangent_second),
        "agreement_locator": factor_receipt(agreement_locator),
        "agreement_locator_divides_common_S_factor": (
            not (common_s_factor % agreement_locator)),
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
