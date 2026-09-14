#!/usr/bin/env python3
"""Exact small-field gate for the candidate-major second-jet Jacobian route.

This uses the literal order-two contact substitution from
``higher_jet_literal_matrix.py``.  The source is the *relaxed* source used by
the target Lean development:

    2*S_degree + R_degree <= B,
    S_degree <= s,
    Y_degree + R_degree + S_degree <= U,
    Y_degree + R_degree + S_degree + Z_degree <= L,

and the strict weighted X cutoff is degree-sensitive through
``reserve(k,n0,S_degree)``.  Thus these are actual selected-graph contact
kernels, not independently sampled forms.

Two claims are separated deliberately.

1.  For the target-positive k=0 shape, generic high-degree agreement
    tangents give four-coordinate gradient rank four over F_p(X).  A
    low-degree agreement tangent gives an exact rank-three counterexample to
    *universal* rank four: it is the tangent to a legal polynomial pencil.
2.  For the proposed k=4 curvature derivative W=(d/dS)^4 Q, the correct
    first root-count-unforced agreement-tangent order is already one, not
    fifteen.  A small faithful chamber also has D4(V)=0, illustrating that
    positive total kernel dimension says nothing about the derivative image.

Function-field rank is certified exactly.  A rank-r specialization at one X
value is a lower bound over F_p(X); the low-degree pencil gives a polynomial
row relation and hence the matching upper bound.  This is a falsifier and a
theorem-design discriminator, not a target proof.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
import hashlib
import json
import random
import resource
import sys

from flint import nmod_mat, nmod_poly

sys.path.insert(0, ".experiments")
from higher_jet_literal_matrix import translated_column  # noqa: E402
from prime_o2_conormal_threshold_falsifier import (  # noqa: E402
    dense_matrix,
    evaluate,
    interpolate,
)
from higher6810_secondjet_retarget_exact import (  # noqa: E402
    coefficient_count,
    relaxed_rank_bound,
)


PRIME = 101


@dataclass(frozen=True)
class Profile:
    n: int
    w: int
    agreements: int
    m: int
    B: int
    s: int
    U: int
    L: int
    k: int
    n0: int


@dataclass(frozen=True)
class Receipt:
    nodes: tuple[int, ...]
    agreement: tuple[int, ...]
    seed: int
    polynomial: tuple[int, ...]
    u0: tuple[int, ...]
    u1: tuple[int, ...]
    tangent: tuple[int, ...]


K0_SMALL = Profile(5, 2, 4, 3, 3, 1, 4, 6, 0, 1)
K0_RICH = Profile(5, 2, 4, 4, 4, 2, 5, 7, 0, 1)
K0_WIDER = Profile(7, 3, 5, 3, 3, 1, 4, 6, 0, 1)
K4_DERIVATIVE = Profile(5, 2, 4, 5, 10, 5, 5, 7, 4, 5)

TARGET_N = 262_144
TARGET_W = 131_071
TARGET_A = 180_413
TARGET_M = 148


def reserve(profile: Profile, curvature_degree: int) -> int:
    return (curvature_degree if curvature_degree < profile.n0
            else profile.k)


def support(profile: Profile) -> tuple[tuple[int, int, int, int, int], ...]:
    """Return monomials (X,Y,R,S,Z) in the exact relaxed source shape."""
    answer = []
    p = profile
    assert p.w >= 2 and p.agreements > p.w + 1 and p.k < p.m
    for sp in range(min(p.s, p.U, p.B // 2) + 1):
        cutoff = (p.m * p.agreements -
                  reserve(p, sp) * (p.agreements - (p.w - 2)))
        rmax = min(p.B - 2 * sp, p.U - sp)
        for rp in range(rmax + 1):
            for yp in range(p.U - sp - rp + 1):
                width = (cutoff - p.w * yp - (p.w - 1) * rp -
                         (p.w - 2) * sp)
                for zp in range(p.L - sp - rp - yp + 1):
                    for xp in range(max(0, width)):
                        answer.append((xp, yp, rp, sp, zp))
    return tuple(answer)


def poly_degree(coefficients: tuple[int, ...]) -> int:
    for i in range(len(coefficients) - 1, -1, -1):
        if coefficients[i] % PRIME:
            return i
    return -1


def make_receipt(profile: Profile, trial: int, tangent_kind: str) -> Receipt:
    """Build a candidate with exactly the prescribed agreement set.

    ``high`` chooses arbitrary agreement directions until their degree-<A
    interpolant has degree >w.  ``low_constant`` makes that interpolant 1.
    Structured variants choose a prescribed top-heavy interpolant and vary
    all off-agreement data deterministically.
    """
    p = profile
    rng = random.Random(1_000_003 * trial + 97 * sum(asdict(p).values()))
    nodes = tuple(range(p.n))
    agreement = tuple(sorted(rng.sample(nodes, p.agreements)))
    seed = rng.randrange(PRIME)
    polynomial = tuple(rng.randrange(PRIME) for _ in range(p.w)) + (
        rng.randrange(1, PRIME),)

    if tangent_kind == "low_constant":
        prescribed = (1,)
    elif tangent_kind == "low_quadratic":
        prescribed = tuple([3, 2] + [1] * max(0, p.w - 1))
    elif tangent_kind == "top_monomial":
        prescribed = (0,) * (p.agreements - 1) + (1,)
    elif tangent_kind == "top_dense":
        prescribed = tuple((7 * i + 3) % PRIME
                           for i in range(p.agreements))
        if prescribed[-1] == 0:
            prescribed = prescribed[:-1] + (1,)
    elif tangent_kind == "high":
        prescribed = None
    else:
        raise ValueError(tangent_kind)

    u1 = [rng.randrange(PRIME) for _ in nodes]
    if prescribed is not None:
        for x in agreement:
            u1[x] = evaluate(prescribed, x)
    else:
        while True:
            for x in agreement:
                u1[x] = rng.randrange(PRIME)
            tangent = interpolate(tuple(u1[x] for x in agreement), agreement)
            if poly_degree(tangent) > p.w:
                break

    tangent = interpolate(tuple(u1[x] for x in agreement), agreement)
    u0 = [rng.randrange(PRIME) for _ in nodes]
    for x in agreement:
        u0[x] = (evaluate(polynomial, x) - seed * u1[x]) % PRIME
    for x in nodes:
        if x not in agreement:
            forbidden = (evaluate(polynomial, x) - seed * u1[x]) % PRIME
            if u0[x] == forbidden:
                u0[x] = (u0[x] + 1) % PRIME
    actual = tuple(x for x in nodes if evaluate(polynomial, x) ==
                   (u0[x] + seed * u1[x]) % PRIME)
    assert actual == agreement
    if tangent_kind.startswith("low_"):
        assert poly_degree(tangent) <= p.w
    else:
        assert poly_degree(tangent) > p.w
    return Receipt(nodes, agreement, seed, polynomial, tuple(u0), tuple(u1),
                   tangent)


def contact_kernel(profile: Profile, receipt: Receipt,
                   monomials: tuple[tuple[int, int, int, int, int], ...]):
    columns = []
    for xp, yp, rp, sp, zp in monomials:
        column = {}
        for node in receipt.nodes:
            expansion = translated_column(
                xp, (yp, rp, sp), zp, node, receipt.u0[node],
                receipt.u1[node], profile.m, 2, PRIME)
            for term, value in expansion.items():
                if value:
                    column[(node, term)] = value
        columns.append(column)
    matrix = dense_matrix(columns)
    kernel, nullity = matrix.nullspace()
    rank = matrix.rank()
    assert rank + nullity == len(monomials)
    return matrix.nrows(), rank, kernel, nullity


def derivative_coefficients(coefficients: tuple[int, ...], order: int):
    out = list(coefficients)
    for _ in range(order):
        out = [(i + 1) * out[i + 1] % PRIME
               for i in range(len(out) - 1)]
    return tuple(out) if out else (0,)


def as_poly(coefficients: tuple[int, ...]) -> nmod_poly:
    return nmod_poly(list(coefficients), PRIME)


def x_power(exponent: int) -> nmod_poly:
    return nmod_poly([0] * exponent + [1], PRIME)


def falling(n: int, d: int) -> int:
    answer = 1
    for i in range(d):
        answer = answer * (n - i) % PRIME
    return answer


def bases(receipt: Receipt):
    f = receipt.polynomial
    return (
        as_poly(f),
        as_poly(derivative_coefficients(f, 1)),
        as_poly(derivative_coefficients(f, 2)),
        nmod_poly([receipt.seed], PRIME),
    )


def tangent_bases(receipt: Receipt):
    h = receipt.tangent
    return (
        as_poly(h),
        as_poly(derivative_coefficients(h, 1)),
        as_poly(derivative_coefficients(h, 2)),
        nmod_poly([1], PRIME),
    )


def monomial_gradient_polys(monomial, receipt: Receipt,
                            curvature_derivative: int = 0):
    xp, yp, rp, sp, zp = monomial
    if sp < curvature_derivative:
        return (nmod_poly([], PRIME),) * 4
    scale = falling(sp, curvature_derivative)
    exponents = (yp, rp, sp - curvature_derivative, zp)
    point = bases(receipt)
    answer = []
    for coordinate in range(4):
        if exponents[coordinate] == 0:
            answer.append(nmod_poly([], PRIME))
            continue
        value = x_power(xp) * (scale * exponents[coordinate] % PRIME)
        for j, (base, exponent) in enumerate(zip(point, exponents)):
            value *= base ** (exponent - (j == coordinate))
        answer.append(value)
    return tuple(answer)


def monomial_value_poly(monomial, receipt: Receipt,
                        curvature_derivative: int = 0):
    xp, yp, rp, sp, zp = monomial
    if sp < curvature_derivative:
        return nmod_poly([], PRIME)
    value = x_power(xp) * falling(sp, curvature_derivative)
    for base, exponent in zip(bases(receipt),
                              (yp, rp, sp - curvature_derivative, zp)):
        value *= base ** exponent
    return value


def compose(functionals, kernel, nullity):
    out = [nmod_poly([], PRIME) for _ in range(nullity)]
    for source_index, functional in enumerate(functionals):
        if not functional:
            continue
        for relation in range(nullity):
            coefficient = int(kernel[source_index, relation]) % PRIME
            if coefficient:
                out[relation] += coefficient * functional
    return tuple(out)


def gradient_rank_at(profile: Profile, receipt: Receipt, monomials, kernel,
                     nullity: int, x: int, curvature_derivative: int = 0):
    gradients = tuple(monomial_gradient_polys(
        monomial, receipt, curvature_derivative) for monomial in monomials)
    flat = []
    for coordinate in range(4):
        flat.extend(int(gradient[coordinate](x)) for gradient in gradients)
    raw = nmod_mat(4, len(monomials), flat, PRIME)
    image = raw * kernel
    return image.rank(), image


def tangent_relation(profile: Profile, receipt: Receipt, monomials, kernel,
                     nullity: int, curvature_derivative: int = 0):
    tangent = tangent_bases(receipt)
    functionals = []
    for monomial in monomials:
        gradient = monomial_gradient_polys(
            monomial, receipt, curvature_derivative)
        functionals.append(sum((a * b for a, b in zip(tangent, gradient)),
                               nmod_poly([], PRIME)))
    pairings = compose(functionals, kernel, nullity)
    return pairings, sum(bool(q) for q in pairings)


def one_k0_case(profile: Profile, trial: int, tangent_kind: str):
    monomials = support(profile)
    receipt = make_receipt(profile, trial, tangent_kind)
    rows, rank, kernel, nullity = contact_kernel(profile, receipt, monomials)

    # Independent exact check that every kernel row vanishes on the selected
    # candidate graph, rather than relying only on the intended theorem.
    specialized = compose(
        tuple(monomial_value_poly(q, receipt) for q in monomials),
        kernel, nullity)
    assert not any(specialized)

    witness = None
    witnessed_rank = -1
    image = None
    for x in range(profile.n, PRIME):
        witnessed_rank, image = gradient_rank_at(
            profile, receipt, monomials, kernel, nullity, x)
        if witnessed_rank == 4 or x >= profile.n + 2:
            witness = x
            break
    pairings, nonzero_pairings = tangent_relation(
        profile, receipt, monomials, kernel, nullity)

    tangent_degree = poly_degree(receipt.tangent)
    if tangent_degree <= profile.w:
        # The legal pencil f+t*h remains degree <=w and agrees on the same
        # A nodes.  Its coefficient of t gives this exact polynomial relation.
        assert not any(pairings)
        assert witnessed_rank <= 3
        function_field_rank = witnessed_rank
        upper_certificate = "nonzero tangent (h,h',h'',1) annihilates every row"
    else:
        assert witnessed_rank == 4
        assert nonzero_pairings > 0
        function_field_rank = 4
        upper_certificate = "four coordinate rows"
    return {
        "profile_n_w_A_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "trial_and_tangent_kind": (trial, tangent_kind),
        "agreement_set": receipt.agreement,
        "candidate_degree_and_tangent_degree": (
            poly_degree(receipt.polynomial), tangent_degree),
        "columns_contact_rows_rank_nullity": (
            len(monomials), rows, rank, nullity),
        "all_kernel_rows_specialize_to_zero_polynomial": True,
        "function_field_gradient_rank": function_field_rank,
        "rank_witness_X": witness,
        "specialized_rank_at_witness": witnessed_rank,
        "nonzero_canonical_tangent_pairings": nonzero_pairings,
        "rank_upper_certificate": upper_certificate,
    }


def k4_derivative_gate():
    profile = K4_DERIVATIVE
    monomials = support(profile)
    receipt = make_receipt(profile, 31, "high")
    rows, rank, kernel, nullity = contact_kernel(profile, receipt, monomials)
    top = tuple(i for i, q in enumerate(monomials) if q[3] >= 4)
    top_projection = nmod_mat(len(top), nullity, [
        int(kernel[i, j]) for i in top for j in range(nullity)
    ], PRIME)
    derivative_image_dimension = top_projection.rank()
    assert derivative_image_dimension == 0

    root_degree = (profile.m - 4) * profile.agreements
    tangent_cost = profile.agreements - profile.w - 1
    # X^(root_degree-1) S^4 is literally in this source.  After d/dS^4 its
    # degree is root_degree-1, so a single tangent replacement can reach or
    # exceed the root threshold.  There is no second 4A reserve.
    endpoint = (root_degree - 1, 0, 0, 4, 0)
    assert endpoint in monomials
    first_unforced = 1
    assert root_degree - 1 < root_degree
    assert root_degree - 1 + tangent_cost >= root_degree

    grad_rank, _ = gradient_rank_at(
        profile, receipt, monomials, kernel, nullity, profile.n, 4)
    pairings, nonzero = tangent_relation(
        profile, receipt, monomials, kernel, nullity, 4)
    assert grad_rank == 0 and not any(pairings) and nonzero == 0
    return {
        "profile_n_w_A_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "columns_contact_rows_rank_nullity": (
            len(monomials), rows, rank, nullity),
        "curvature_degree_at_least_four_columns": len(top),
        "exact_D4_kernel_image_dimension": derivative_image_dimension,
        "post_D4_contact_root_degree": root_degree,
        "literal_endpoint_monomial": endpoint,
        "agreement_tangent_degree_cost": tangent_cost,
        "first_root_count_unforced_directional_order": first_unforced,
        "D4_gradient_rank_over_FpX": grad_rank,
        "combined_three_transverse_plus_first_unforced_rank": 0,
    }


def target_k0_arithmetic():
    """Exact source and fixed-cutoff determinant gates at score 6900."""
    columns = coefficient_count(
        TARGET_A, TARGET_M, 5465, 64, 10, 200, 0, 1)
    one_node_rank = relaxed_rank_bound(TARGET_M, 5465, 64, 10, 200)
    margin = columns - TARGET_N * one_node_rank
    assert columns == 6_379_078_467_962_794
    assert one_node_rank == 24_333_499_291
    assert TARGET_N * one_node_rank == 6_378_880_838_139_904
    assert margin == 197_629_822_890

    # For a fixed cutoff D=m*A, the standard determinant-preserving contact
    # columns give valuation (4m-3)G for a full four-minor and (3m-3)G for a
    # vertical three-minor.  Their residual degrees at G=A+r are exactly:
    #   3(A-w)-1 -(4m-3)r, and 3(A-w) -(3m-3)r.
    full_base = 3 * (TARGET_A - TARGET_W) - 1
    full_slope = 4 * TARGET_M - 3
    vertical_base = 3 * (TARGET_A - TARGET_W)
    vertical_slope = 3 * TARGET_M - 3
    full_last_open = full_base // full_slope
    vertical_last_open = vertical_base // vertical_slope
    assert (full_base, full_slope, full_last_open) == (148_025, 589, 251)
    assert full_base - full_slope * 251 == 186
    assert full_base - full_slope * 252 == -403
    assert (vertical_base, vertical_slope, vertical_last_open) == (
        148_026, 441, 335)
    assert vertical_base - vertical_slope * 335 == 291
    assert vertical_base - vertical_slope * 336 == -150
    return {
        "profile_m_B_s_U_L_k_n0": (148, 64, 10, 200, 5465, 0, 1),
        "columns_one_node_rank_N_times_rank_margin": (
            columns, one_node_rank, TARGET_N * one_node_rank, margin),
        "full_minor_residual_at_A_plus_r": "148025-589*r",
        "full_minor_last_not_degree_killed_r_and_agreement": (
            full_last_open, TARGET_A + full_last_open),
        "full_minor_first_forced_zero_r_and_agreement": (
            full_last_open + 1, TARGET_A + full_last_open + 1),
        "vertical_minor_residual_at_A_plus_r": "148026-441*r",
        "vertical_minor_last_not_degree_killed_r_and_agreement": (
            vertical_last_open, TARGET_A + vertical_last_open),
        "vertical_minor_first_forced_zero_r_and_agreement": (
            vertical_last_open + 1, TARGET_A + vertical_last_open + 1),
    }


def main():
    # Counterexamples first, then deliberately diverse high-tangent trials.
    low_cases = (
        one_k0_case(K0_SMALL, 3, "low_constant"),
        one_k0_case(K0_SMALL, 5, "low_quadratic"),
        one_k0_case(K0_RICH, 7, "low_constant"),
    )
    high_specs = []
    for profile, base in ((K0_SMALL, 100), (K0_RICH, 200),
                          (K0_WIDER, 300)):
        high_specs.extend((
            (profile, base + 1, "top_monomial"),
            (profile, base + 2, "top_dense"),
            (profile, base + 3, "high"),
            (profile, base + 4, "high"),
        ))
    high_cases = tuple(one_k0_case(*spec) for spec in high_specs)
    assert all(q["function_field_gradient_rank"] == 3 for q in low_cases)
    assert all(q["function_field_gradient_rank"] == 4 for q in high_cases)

    result = {
        "prime": PRIME,
        "target_k0_arithmetic": target_k0_arithmetic(),
        "k0_low_degree_tangent_counterexamples": low_cases,
        "k0_high_degree_tangent_trials": high_cases,
        "high_degree_trials_rank_four": len(high_cases),
        "high_degree_trials_total": len(high_cases),
        "k4_derivative_gate": k4_derivative_gate(),
        "verdict": (
            "Universal k=0 pointwise rank four is false: whenever the "
            "agreement-direction interpolant has degree at most w, the legal "
            "pencil f+t*h forces an exact tangent relation and these chambers "
            "have rank exactly three.  All twelve tested high-degree-tangent "
            "receipts have exact F_p(X) rank four, supporting the sharper "
            "dichotomy rank<4 => a low-degree selected pencil.  This remains "
            "a target theorem, not a consequence of nullity.  The k=4 "
            "osculating ledger has first unforced order one, not fifteen; "
            "the tested complete derivative image is zero."
        ),
        "limitations": (
            "Finite small-field evidence cannot prove the target dichotomy. "
            "The low/high tangent rank mechanism was already isolated by "
            "f7_badrow_full_conormal_semantics_audit.py and the missing "
            "rank-defect-recovery theorem by the Global-O2 audits; these "
            "trials only confirm that the new relaxed k=0 source has the same "
            "semantics. "
            "The k=4 image-zero chamber is a faithful source/contact model "
            "but not a scaled copy of target dimensions, so it falsifies no "
            "target-specific noncollapse theorem.  The exact cutoff/contact "
            "calculation making directional order one unforced is dimension "
            "independent."
        ),
    }
    canonical = json.dumps(result, sort_keys=True, separators=(",", ":"))
    print(json.dumps(result, sort_keys=True, indent=2))
    print("canonical_sha256=" + hashlib.sha256(canonical.encode()).hexdigest())
    print("peak_rss_kib=" + str(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss))


if __name__ == "__main__":
    main()
