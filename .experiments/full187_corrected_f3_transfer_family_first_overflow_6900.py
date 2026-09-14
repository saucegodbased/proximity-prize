#!/usr/bin/env python3
"""Exact first-overflow audit for the corrected literal F3 transfer family.

Outer Z is passive in the benchmark contact filtration.  Consequently the
error-active form is W=Y-1-X^(E-1)Z, not V-1 for V=Y-q_H Z.  For

  H=Xi_H, R=Xi_(G\\H), E0=Xi_E,

every summand

  K_i = H^(59-i) R^60 E0^i V^(i+1) W^(60-i),  0<=i<=59,

has literal contact order 60 on H, R, and E separately.  Only K_0 contains
the raw degree-one packet B*V, B=H^59 R^60.

This script proves that neither scalar nor polynomial coefficients on this
60-summand separated family make it source-legal.  Its degree-two Y^2
coefficient already violates the Full187 taper.  More decisively, for
arbitrary polynomial coefficients c_i(X), c_0=1, the top Y^61 coefficient
has an unavoidable R^60 factor larger than its entire source window; the
required zero identity then contradicts coprimality of H and E0.
It does not rule out a larger simultaneous Padé cascade in which degree >=3
source layers change the error-side conditions on the degree-two layer.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import resource
import sys

from flint import nmod_poly

import full187_target_charge13_transposed_four_residue_gate_6900 as T


P = T.P
N = T.N
W = T.W
G = T.G
ECOUNT = T.E
HCOUNT = T.H
RCOUNT = G - HCOUNT
M = T.M
D = T.D


def main():
    instance = T.build_target_instance()
    H = nmod_poly(instance.xi_h_coefficients, P)
    R = nmod_poly(instance.xi_r_coefficients, P)
    E0 = nmod_poly(instance.xi_e_coefficients, P)
    qh = nmod_poly(instance.qh_coefficients, P)

    assert H.degree() == HCOUNT
    assert R.degree() == RCOUNT
    assert E0.degree() == ECOUNT
    assert qh.degree() == W
    assert HCOUNT == W + 1
    assert RCOUNT == G - HCOUNT == 49_341
    assert ECOUNT - 1 == 81_730

    # Correct literal contact-order ledger for each separated summand K_i.
    contact_orders = []
    for i in range(M):
        at_h = (M - 1 - i) + (i + 1)       # H power and active V power
        at_r = M                            # R^60 alone
        at_e = i + (M - i)                  # E0 power and active W power
        assert (at_h, at_r, at_e) == (M, M, M)
        contact_orders.append((i, at_h, at_r, at_e))

    # Homogeneous source degree two receives only i=0,1.  Its pure Y^2
    # coefficient, apart from a nonzero sign, is
    #
    #   H^58 R^60 (60 H + c_1 E0).
    #
    # Scalars cannot touch the leading H term.  Even allowing arbitrary
    # polynomial c_1, Euclidean division says the smallest possible degree of
    # 60H+c_1E0 is degree(H mod E0).  Check that literal remainder.
    h_remainder = H % E0
    assert h_remainder.degree() == ECOUNT - 1
    assert M % P != 0

    common_factor_degree = (M - 2) * HCOUNT + M * RCOUNT
    legal_width_y2 = D - 2 * W
    legal_max_degree_y2 = legal_width_y2 - 1
    scalar_family_degree = common_factor_degree + HCOUNT
    best_polynomial_family_degree = common_factor_degree + h_remainder.degree()
    assert scalar_family_degree > legal_max_degree_y2
    assert best_polynomial_family_degree > legal_max_degree_y2
    assert scalar_family_degree - legal_max_degree_y2 == W
    assert best_polynomial_family_degree - legal_max_degree_y2 == ECOUNT - 2

    # Close the whole separated family for arbitrary polynomial c_i(X).
    # The Y^(M+1) coefficient is
    #   R^M * sum_i c_i H^(M-1-i) E0^i.
    # R^M alone is wider than the legal coefficient window, so legality
    # forces the sum to vanish.  Mod E0 it is H^(M-1), since c_0=1, which
    # cannot vanish because H and E0 are coprime disjoint-set locators.
    r_power_degree = M * RCOUNT
    legal_width_top_y = D - W * (M + 1)
    legal_max_degree_top_y = legal_width_top_y - 1
    assert r_power_degree >= legal_width_top_y
    assert H.gcd(E0).degree() == 0
    assert (H ** (M - 1) % E0) != 0

    stable = {
        "scope": (
            "corrected passive-Z F3 transfer family: exact Y2 overflow and "
            "all-polynomial top-degree stop; no claim about the larger simultaneous "
            "Pade cascade, u0 tails, packet lift, or ProtocolClaim 6900"),
        "target_p_N_W_G_E_H_R_M_D": (
            P, N, W, G, ECOUNT, HCOUNT, RCOUNT, M, D),
        "active_forms": {
            "V": "Y-Z*q_H",
            "W_error": "Y-1-X^(E-1)*Z",
            "why_not_V_minus_1": (
                "Z is passive; on E, V-1 has zero-contact term "
                "Z*(U1-q_H)"),
        },
        "family": (
            "K_i=H^(59-i)R^60E0^iV^(i+1)W_error^(60-i), "
            "0<=i<=59"),
        "all_summands_contact_order_H_R_E": (M, M, M),
        "summand_contact_checks": len(contact_orders),
        "only_i0_has_raw_linear_boundary": True,
        "i0_raw_linear_boundary": "H^59*R^60*V = B*V",
        "first_overflow": {
            "source_monomial": "Y^2",
            "coefficient_up_to_sign": (
                "H^58*R^60*(60*H+c1*E0)"),
            "common_factor_degree": common_factor_degree,
            "legal_half_open_width": legal_width_y2,
            "legal_max_degree": legal_max_degree_y2,
            "scalar_c1_degree": scalar_family_degree,
            "scalar_overflow": scalar_family_degree - legal_max_degree_y2,
            "degree_H_mod_E0": h_remainder.degree(),
            "best_arbitrary_polynomial_c1_degree": (
                best_polynomial_family_degree),
            "best_arbitrary_polynomial_c1_overflow": (
                best_polynomial_family_degree - legal_max_degree_y2),
            "H_mod_E0_coefficients_sha256": T.sha256_u32(
                int(h_remainder[j]) for j in range(h_remainder.degree() + 1)),
        },
        "all_polynomial_coefficients_stop": {
            "top_source_monomial": "Y^61",
            "coefficient": (
                "R^60*sum_(i=0)^59 c_i(X)H^(59-i)E0^i, c_0=1"),
            "degree_R60": r_power_degree,
            "legal_half_open_width_Y61": legal_width_top_y,
            "legal_max_degree_Y61": legal_max_degree_top_y,
            "R60_alone_exceeds_legal_max_by": (
                r_power_degree - legal_max_degree_top_y),
            "forced_zero_identity_mod_E0": "H^59 = 0 mod E0",
            "gcd_H_E0_degree": H.gcd(E0).degree(),
            "H59_mod_E0_nonzero": True,
            "conclusion": (
                "no arbitrary polynomial c_i(X), c_0=1, makes the "
                "separated family source-legal"),
        },
        "decision": (
            "RED_ALL_POLYNOMIAL_MIXING_IN_SEPARATED_FAMILY__"
            "NEXT_GATE_FULL_MULTI_DEGREE_TARGET_PADE_CASCADE"),
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
