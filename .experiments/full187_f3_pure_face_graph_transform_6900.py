#!/usr/bin/env python3
"""Exact graph transform and scalar-dual gate for the Full187 F3 pure face.

This is an experiment, not a construction.  It specializes a hypothetical
F3 lift at R=S=Z=0, removes the agreement divisibilities by the change of
variables Y=G*V, and records the resulting one-graph fat-point module.  It
also proves that the tempting scalar Euler/Hasse projections of that module
are structurally too weak in their first sixteen E-adic orders (including
the 24-lane projection which kills correction degrees 2,...,59).

No large matrix is built.  The executable uses exact target-field locator
polynomials only to check the frozen partition, coprimality, and the closed
formula G^{-1}=N^{-1}*X*E' modulo E.
"""

from __future__ import annotations

from collections import Counter
from math import prod
import hashlib
import json
from pathlib import Path
import resource

from flint import nmod_poly

import full187_target_charge13_transposed_four_residue_gate_6900 as T


P = T.P
N = T.N
W = T.W
G_DEG = T.G
E_DEG = T.E
H_DEG = T.H
R_DEG = G_DEG - H_DEG
M = T.M
D = T.D
J = T.J_BOUND
A_WEIGHT = G_DEG - W


def raw_width(n: int) -> int:
    return D - n * W


def transformed_free_width(n: int) -> int:
    """Free dimension after the agreement condition is removed."""
    if n < M:
        return n * A_WEIGHT
    return raw_width(n)


def exact_dimension_receipt():
    raw_with_a1 = sum(raw_width(n) for n in range(1, J + 1))
    agreement_with_a1 = sum(
        (M - n) * G_DEG for n in range(1, M))
    residual_with_a1 = raw_with_a1 - agreement_with_a1
    residual_by_transform = sum(
        transformed_free_width(n) for n in range(1, J + 1))
    error_conditions = sum((M - j) * E_DEG for j in range(M))

    raw_corrections = sum(raw_width(n) for n in range(2, J + 1))
    agreement_corrections = sum(
        (M - n) * G_DEG for n in range(2, M))
    residual_corrections = raw_corrections - agreement_corrections

    assert raw_with_a1 == 441_597_347
    assert agreement_with_a1 == 319_331_010
    assert residual_with_a1 == residual_by_transform == 122_266_337
    assert error_conditions == 149_567_730
    assert error_conditions - residual_with_a1 == 27_301_393
    assert raw_corrections == 430_903_638
    assert agreement_corrections == 308_686_643
    assert residual_corrections == 122_216_995
    assert error_conditions - residual_corrections == 27_350_735

    return {
        "including_fixed_A1_as_a_formal_source_dimension": {
            "raw_dimensions_A1_through_A82": raw_with_a1,
            "agreement_divisibility_conditions": agreement_with_a1,
            "post_agreement_dimensions": residual_with_a1,
            "error_conditions": error_conditions,
            "error_minus_source_deficit": (
                error_conditions - residual_with_a1),
        },
        "actual_membership_unknowns_A2_through_A82": {
            "raw_correction_dimensions": raw_corrections,
            "agreement_divisibility_conditions": agreement_corrections,
            "post_agreement_correction_dimensions": residual_corrections,
            "error_conditions": error_conditions,
            "error_minus_correction_deficit": (
                error_conditions - residual_corrections),
        },
    }


def locator_and_inverse_receipt():
    instance = T.build_target_instance()
    h = nmod_poly(instance.xi_h_coefficients, P)
    r = nmod_poly(instance.xi_r_coefficients, P)
    e = nmod_poly(instance.xi_e_coefficients, P)
    g = h * r
    omega = nmod_poly([-1] + [0] * (N - 1) + [1], P)

    assert (h.degree(), r.degree(), g.degree(), e.degree()) == (
        H_DEG, R_DEG, G_DEG, E_DEG)
    assert g * e == omega
    assert g.gcd(e).degree() == 0

    # GE=X^N-1 gives G(alpha)E'(alpha)=N alpha^-1 at E-roots.
    # Therefore A=N^-1 X E' is the exact inverse of G modulo E.
    x = nmod_poly([0, 1], P)
    a = (pow(N, -1, P) * x * e.derivative()) % e
    assert a.degree() == E_DEG - 1
    assert (g * a) % e == nmod_poly([1], P)

    # The prescribed linear coefficient is exactly at the strict boundary:
    # B=H^59 R^60=G^59 R has degree (D-W)-1.
    boundary_degree = (M - 1) * G_DEG + R_DEG
    assert boundary_degree == raw_width(1) - 1 == 10_693_708
    assert R_DEG == A_WEIGHT - 1

    return {
        "locator_degrees_H_R_G_E": (
            h.degree(), r.degree(), g.degree(), e.degree()),
        "G_times_E_equals_X_to_N_minus_1": True,
        "gcd_G_E_degree": g.gcd(e).degree(),
        "inverse_A_formula": "A = N^-1 * X * E' mod E",
        "inverse_A_degree": a.degree(),
        "inverse_A_sha256_u32": T.sha256_u32(
            int(a[j]) for j in range(a.degree() + 1)),
        "G_times_A_mod_E_is_one": True,
        "boundary_B": "H^59*R^60 = G^59*R",
        "boundary_B_degree_and_strict_width": (
            boundary_degree, raw_width(1)),
        "a_equals_G_minus_W_equals_degR_plus_one": (
            A_WEIGHT, G_DEG - W, R_DEG + 1),
    }


def scalar_euler_projection_gate():
    """Prove the first E-adic scalar dual projections are surjective.

    If P(n) has degree d and k=60-d, the Euler/Hasse combination gives

      E^k | sum_n P(n) A_n.

    A correction lane n has a free polynomial of dimension s_n.  Whenever
    s_n >= k*deg(E), that lane alone maps onto Fp[X]/(E^k), because every
    agreement multiplier is a unit modulo E.  A degree-d scalar polynomial
    can kill at most d of the distinct integer lanes n=2,...,82.  Hence the
    projection is identically non-obstructing if there are more than d
    individually-surjective lanes.
    """
    rows = []
    forced_surjective_orders = []
    for k in range(1, M + 1):
        d = M - k
        modulus_dimension = k * E_DEG
        individually_surjective = tuple(
            n for n in range(2, J + 1)
            if transformed_free_width(n) >= modulus_dimension)
        surplus_over_root_budget = len(individually_surjective) - d
        forced = surplus_over_root_budget > 0
        if forced:
            forced_surjective_orders.append(k)
        rows.append((
            k, d, modulus_dimension, len(individually_surjective),
            surplus_over_root_budget, forced,
            individually_surjective[0] if individually_surjective else None,
            individually_surjective[-1] if individually_surjective else None,
        ))

    assert tuple(forced_surjective_orders) == tuple(range(1, 17))
    assert rows[16][:5] == (17, 43, 1_389_427, 43, 0)
    assert rows[17][:5] == (18, 42, 1_471_158, 42, 0)

    # The most tempting 24-component projection uses the degree-58
    # polynomial with roots 2,...,59.  It leaves the target n=1 plus the 23
    # high lanes 60,...,82 and gives only an E^2 congruence.  Root counting
    # already proves that at least 20 individually-surjective correction
    # lanes survive *any* degree-58 scalar projection, so this cannot yield a
    # target dual, independently of the actual coefficients of P.
    natural_degree = 58
    natural_k = M - natural_degree
    natural_large = tuple(
        n for n in range(2, J + 1)
        if transformed_free_width(n) >= natural_k * E_DEG)
    assert len(natural_large) == 78
    assert len(natural_large) - natural_degree == 20
    p_at_one = prod((1 - n) % P for n in range(2, 60)) % P
    assert p_at_one != 0

    return {
        "lemma": (
            "For deg P=d, F in (E,V-A)^60 implies "
            "sum_n P(n) C_n A^n is divisible by E^(60-d). "
            "Using a Hensel inverse of G and C_n=G^(n-60)A_n, this is "
            "equivalent to E^(60-d) dividing sum_n P(n)A_n."),
        "single_lane_surjectivity_criterion": (
            "P(n)!=0 and transformed_free_width(n) >= "
            "(60-d)*deg(E)"),
        "order_degree_modulus_largeLaneCount_minusRootBudget_forced_"
        "firstLastLane": tuple(rows),
        "all_scalar_projections_forced_surjective_E_adic_orders": (
            min(forced_surjective_orders), max(forced_surjective_orders)),
        "first_not_settled_by_single_lane_root_count": {
            "E_adic_order": 17,
            "polynomial_degree_and_root_budget": 43,
            "individually_surjective_lanes": 43,
        },
        "natural_24_lane_projection": {
            "P": "product_(n=2)^59 (t-n)",
            "degree": natural_degree,
            "P_at_1_mod_p": p_at_one,
            "remaining_named_lanes": "target n=1 and high n=60,...,82",
            "modulus": "E^2",
            "individually_surjective_correction_lanes_before_roots": (
                len(natural_large)),
            "minimum_individually_surjective_lanes_after_58_roots": (
                len(natural_large) - natural_degree),
            "decision": "VACUOUS_SCALAR_PROJECTION_SURJECTIVE",
        },
    }


def main():
    dimensions = exact_dimension_receipt()
    locators = locator_and_inverse_receipt()
    scalar_gate = scalar_euler_projection_gate()
    stable = {
        "scope": (
            "exact necessary R=S=Z=0 face of a hypothetical Full187 F3 "
            "lift; graph transform, dimensions, and scalar Euler-dual "
            "strength only; no pure-face membership decision or production "
            "claim"),
        "target_p_N_W_G_E_H_R_M_D_J_a": (
            P, N, W, G_DEG, E_DEG, H_DEG, R_DEG,
            M, D, J, A_WEIGHT),
        "pure_face": {
            "K": "B*Y + sum_(n=2)^82 A_n*Y^n",
            "strict_windows": "deg A_n < D-nW",
            "agreement": "G^(60-n) divides A_n for 1<=n<60",
            "error": (
                "E^(60-j) divides sum_(n=j)^82 binom(n,j)A_n "
                "for 0<=j<60"),
        },
        "graph_transform": {
            "definition": "F(V)=G^-60*K(GV)=sum C_n V^n",
            "uniform_caps": "deg C_n < n*a",
            "fixed_coefficients": "C_0=0, C_1=Rloc, deg Rloc=a-1",
            "high_tail": "G^(n-60) divides C_n for 60<=n<=82",
            "error_ideal": "F belongs to (E,V-A)^60",
            "A": "any Hensel lift of G^-1 modulo E^60",
            "polynomial_center": (
                "already (E,GV-1)=(E,V-(N^-1 X E' mod E))"),
        },
        "dimensions": dimensions,
        "exact_locator_checks": locators,
        "scalar_euler_projection_gate": scalar_gate,
        "decision": (
            "GREEN_EXACT_PURE_FACE_GRAPH_COMPRESSION__"
            "STOP_SCALAR_EULER_DUALS_TOO_WEAK__"
            "NEXT_GENUINE_MULTIROW_SHIFTED_POPOV_ON_HIGH_TAIL"),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    print(json.dumps({
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
