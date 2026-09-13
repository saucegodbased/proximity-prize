#!/usr/bin/env python3
"""Adversarial interface audit for the Full187 ratio relays and J2 actuators.

The target THREE-RHS obligation is not a scalar endpoint interpolation:

    C_G(h) = 0,  J_YRS(h) = 0,  C_E(h) = C_E(F_i).

This script checks the first two conditions structurally in the repository's
existing primary literal F_101 order-two contact model and then locates the
first forced error-contact failure.  Its multiplicity is four, so the target
pair (V^60,V^59) becomes (V^4,V^3), and a target A_b/A_(b+1) pair becomes
A_1/A_2.  The mechanisms being tested (normal contact order, global boundary
degree, and the passive R/S coefficient) are unchanged.  Source-window
legality is deliberately not transported from 60 to 4; it was checked
separately at the target in the two audited commits.

This is a theorem discriminator, not target transport and not a production
candidate.
"""

from __future__ import annotations

from collections import defaultdict
import hashlib
import json
from math import comb
from pathlib import Path
import sys

sys.path.insert(0, ".experiments")
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402
from higher_jet_literal_matrix import translated_column  # noqa: E402


PRIME = 101
N = 11
GOOD = tuple(range(8))
BAD = tuple(range(8, 11))
M = 4


def poly_scale(a, scalar):
    return F.poly_trim(tuple(scalar * value for value in a))


def interpolate(nodes, values):
    """The unique degree-<len(nodes) polynomial with the given values."""
    result = ()
    for i, (node, value) in enumerate(zip(nodes, values)):
        numerator = (1,)
        denominator = 1
        for j, other in enumerate(nodes):
            if i == j:
                continue
            numerator = F.poly_mul(numerator, ((-other) % PRIME, 1))
            denominator = denominator * (node - other) % PRIME
        term = poly_scale(numerator, value * pow(denominator, -1, PRIME))
        result = F.poly_add(result, term)
    assert len(result) <= len(nodes)
    assert tuple(F.poly_eval(result, node) for node in nodes) == tuple(
        value % PRIME for value in values)
    return result


def sparse_sum(*terms):
    result = {}
    for scale, source in terms:
        result = F.sparse_add(result, source, scale)
    return result


def scalar_times(poly, source):
    return F.sparse_mul(F.sparse_embed_x(poly), source)


def contact_image(source, u0, u1):
    image = {}
    for (xp, yp, rp, sp, zp), coefficient in source.items():
        for node in range(N):
            for local, value in translated_column(
                    xp, (yp, rp, sp), zp, node, u0[node], u1[node],
                    M, 2, PRIME).items():
                row = (node, local)
                replacement = (image.get(row, 0) + coefficient * value) % PRIME
                if replacement:
                    image[row] = replacement
                else:
                    image.pop(row, None)
    return image


def affine_coefficient(image, node, t=0, e=0, r=0, s=0):
    """Coefficient after the sound specialization Z=1."""
    return sum(
        coefficient for (row_node, (rt, re, rr, rs, _rz)), coefficient
        in image.items()
        if (row_node, rt, re, rr, rs) == (node, t, e, r, s)
    ) % PRIME


def vertical_yrs_zero(source):
    """The exact polynomial Y/R/S normal only sees total boundary degree one."""
    return not any(
        yp + rp + sp + zp == 1 and yp + rp + sp == 1
        for _xp, yp, rp, sp, zp in source
    )


def error_rows(image, target, node, rows):
    return {
        name: (
            affine_coefficient(image, node, **coordinate),
            affine_coefficient(target, node, **coordinate),
            (affine_coefficient(image, node, **coordinate)
             - affine_coefficient(target, node, **coordinate)) % PRIME,
        )
        for name, coordinate in rows.items()
    }


def main():
    F.PRIME = PRIME
    l = F.locator(GOOD)
    h = F.locator(BAD)
    l1 = F.poly_derivative(l)
    l2 = F.poly_derivative(l, 2)
    h1 = F.poly_derivative(h)
    q = F.poly_pow(h, 2)
    q1 = F.poly_derivative(q)

    ls = F.sparse_embed_x(l)
    l1s = F.sparse_embed_x(l1)
    hs = F.sparse_embed_x(h)
    qs = F.sparse_embed_x(q)
    q1s = F.sparse_embed_x(q1)
    v = sparse_sum((1, F.Y), (-1, F.sparse_mul(F.Z, qs)))
    w = sparse_sum((1, F.R), (-1, F.sparse_mul(F.Z, q1s)))
    j1 = sparse_sum(
        (1, F.sparse_mul(ls, w)),
        (-1, F.sparse_mul(l1s, v)),
    )
    u = F.poly_add(F.poly_mul(h, l1), F.poly_mul(l, h1), -2)

    target_source = scalar_times(F.poly_pow(l, M - 1), v)
    u0 = tuple(0 if node in GOOD else 1 for node in range(N))
    u1 = tuple(F.poly_eval(q, node) for node in range(N))
    target_contact = contact_image(target_source, u0, u1)
    assert not any(node in GOOD for node, _local in target_contact)

    def relay(n, multiplier):
        bracket = sparse_sum(
            (1, scalar_times(u, F.sparse_pow(v, n))),
            (-1, scalar_times(
                F.poly_pow(h, 3),
                F.sparse_mul(
                    F.Z,
                    F.sparse_mul(F.sparse_pow(v, n - 2), j1),
                ),
            )),
        )
        coefficient = F.poly_mul(multiplier, F.poly_pow(l, M - n))
        return scalar_times(coefficient, bracket)

    f_values = tuple(pow(F.poly_eval(l, x), M - 1, PRIME) for x in BAD)
    q_m_values = tuple(
        (-(M - 2) * f * pow(F.poly_eval(u, x), -1, PRIME)) % PRIME
        for x, f in zip(BAD, f_values)
    )
    q_prev_values = tuple(
        ((M - 1) * f * pow(
            F.poly_eval(l, x) * F.poly_eval(u, x) % PRIME,
            -1, PRIME)) % PRIME
        for x, f in zip(BAD, f_values)
    )
    q_m = interpolate(BAD, q_m_values)
    q_prev = interpolate(BAD, q_prev_values)
    relay_source = sparse_sum((1, relay(M, q_m)), (1, relay(M - 1, q_prev)))
    relay_contact = contact_image(relay_source, u0, u1)

    assert not any(node in GOOD for node, _local in relay_contact)
    assert vertical_yrs_zero(relay_source)
    relay_rows = {
        "value": {},
        "pure_T": {"t": 1},
        "T_R": {"t": 1, "r": 1},
        "T2_S": {"t": 2, "s": 1},
        "T2_R2": {"t": 2, "r": 2},
        "E": {"e": 1},
    }
    relay_receipts = []
    forced_second_moment = (
        -(M - 2) * comb(M, 2) + (M - 1) * comb(M - 1, 2)
    ) % PRIME
    assert forced_second_moment == (-3) % PRIME
    for node, f in zip(BAD, f_values):
        rows = error_rows(relay_contact, target_contact, node, relay_rows)
        assert rows["value"][2] == 0
        assert rows["T_R"][2] == 0
        assert rows["T2_S"][2] == 0
        assert rows["E"][2] == 0
        assert rows["T2_R2"][2] == forced_second_moment * f % PRIME
        assert rows["T2_R2"][2] != 0
        relay_receipts.append({
            "node": node,
            "F0_value": f,
            "image_target_residual_by_affine_contact_row": rows,
        })

    # The alleged J2-BZ actuator simplifies before any local expansion:
    #
    # J2 - BZ = (2(L')^2-LL'')Y - 2LL'R + L^2S.
    #
    # In particular its error contact-weight-zero slice contains R and S.
    c = F.poly_add(poly_scale(F.poly_pow(l1, 2), 2), F.poly_mul(l, l2), -1)
    d = sparse_sum(
        (1, scalar_times(c, F.Y)),
        (-2, scalar_times(F.poly_mul(l, l1), F.R)),
        (1, scalar_times(F.poly_pow(l, 2), F.S)),
    )

    def actuator(b, multiplier):
        coefficient = F.poly_mul(multiplier, F.poly_pow(l, M - b))
        return scalar_times(
            coefficient, F.sparse_mul(F.sparse_pow(v, b), d))

    # For b=1,2 the scalar value/E ratios are 2,3.  Choose amplitudes 2f,-f
    # so those two scalar rows really do match, then inspect the passive slice.
    b0, b1 = 1, 2
    alpha0 = tuple(2 * f % PRIME for f in f_values)
    alpha1 = tuple(-f % PRIME for f in f_values)
    c_values = tuple(F.poly_eval(c, x) for x in BAD)
    assert all(c_values)
    qa0_values = tuple(
        alpha * pow(
            pow(F.poly_eval(l, x), M - b0, PRIME) * cv % PRIME,
            -1, PRIME) % PRIME
        for x, alpha, cv in zip(BAD, alpha0, c_values)
    )
    qa1_values = tuple(
        alpha * pow(
            pow(F.poly_eval(l, x), M - b1, PRIME) * cv % PRIME,
            -1, PRIME) % PRIME
        for x, alpha, cv in zip(BAD, alpha1, c_values)
    )
    qa0 = interpolate(BAD, qa0_values)
    qa1 = interpolate(BAD, qa1_values)
    actuator_source = sparse_sum(
        (1, actuator(b0, qa0)), (1, actuator(b1, qa1)))
    actuator_contact = contact_image(actuator_source, u0, u1)
    assert not any(node in GOOD for node, _local in actuator_contact)
    assert vertical_yrs_zero(actuator_source)

    actuator_rows = {
        "value": {},
        "R_at_contact_weight_0": {"r": 1},
        "S_at_contact_weight_0": {"s": 1},
        "E": {"e": 1},
        "T_R": {"t": 1, "r": 1},
    }
    actuator_receipts = []
    for node, f, cv in zip(BAD, f_values, c_values):
        rows = error_rows(actuator_contact, target_contact, node, actuator_rows)
        lv = F.poly_eval(l, node)
        assert rows["value"][2] == 0
        assert rows["E"][2] == 0
        assert rows["S_at_contact_weight_0"][2] == f * lv * lv * pow(
            cv, -1, PRIME) % PRIME
        assert rows["S_at_contact_weight_0"][2] != 0
        q2_at_node = F.poly_eval(F.poly_derivative(q, 2), node)
        pure_b = (-lv * lv * q2_at_node) % PRIME
        actuator_receipts.append({
            "node": node,
            "Lambda": lv,
            "actual_d0_2LambdaPrimeSquared_minus_LambdaLambdaSecond": cv,
            "claimed_d0_minus_B": (-pure_b) % PRIME,
            "actual_d0_equals_claimed_d0": cv == (-pure_b) % PRIME,
            "image_target_residual_by_affine_contact_row": rows,
        })
    assert not any(item["actual_d0_equals_claimed_d0"]
                   for item in actuator_receipts)

    payload = {
        "scope": (
            "exact structural and F101 literal-contact audit of the Full187 "
            "ratio relay and J2-BZ actuator claims; not target transport"
        ),
        "field": PRIME,
        "control": {
            "nodes": N,
            "agreement_nodes": GOOD,
            "error_nodes": BAD,
            "multiplicity": M,
            "Q": "Xi_E^2",
        },
        "required_interface": (
            "C_G(h)=0; J_YRS(h)=0; C_E(h)=C_E(F_i)"
        ),
        "ratio_relay": {
            "scaled_pair": ("R_4", "R_3"),
            "inside_primary_F101_source_box": F.source_legal(relay_source),
            "all_literal_agreement_contacts_zero": True,
            "exact_polynomial_YRS_normal_zero": True,
            "matched_rows": ("value", "E", "T*R", "T^2*S"),
            "possibly_earlier_uncontrolled_row": "pure T (CRT derivative)",
            "first_forced_failure": "T^2*R^2",
            "forced_residual_multiple_of_F0_value": forced_second_moment,
            "target_60_59_integer_residual": -1711,
            "receipts": tuple(relay_receipts),
        },
        "j2_actuator": {
            "scaled_pair": ("A_1", "A_2"),
            "inside_primary_F101_source_box": F.source_legal(actuator_source),
            "identity_before_local_expansion": (
                "J2-BZ=(2(L')^2-L*L'')Y-2LL'R+L^2S"
            ),
            "all_literal_agreement_contacts_zero": True,
            "exact_polynomial_YRS_normal_zero": True,
            "scalar_rows_deliberately_matched": ("value", "E"),
            "first_forced_failure": "S at contact weight zero",
            "reason": (
                "after matching a nonzero scalar value, the common D factor "
                "has unavoidable S coefficient L^2; R and S are passive "
                "contact variables, not variables that may be set to zero"
            ),
            "receipts": tuple(actuator_receipts),
        },
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
