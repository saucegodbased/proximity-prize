#!/usr/bin/env python3
"""Exact centered-family gate for the missing k=0 high-head Y direction.

This uses the literal flattened second-jet contact substitution

    X -> x + eps,
    Y -> u0 + u1*Z + eps*R - eps^2*S + eps^3*T,

truncated modulo eps^m.  On the frozen F_101 m=8 profile it forms

    A  = Y - P(X) - (Z-gamma) Q(X),
    Ck = Lambda_G^(m-k) A^k.

The target is the complete eps>=3 trace of C1 at all nodes.  Every correction
carrier is an honest source polynomial, is checked coefficientwise against
the literal source support, has zero boundary gradient, and has zero complete
contact on the agreement set.  We compare the old pure family

    X^j (Z-gamma)^z Ck,  k>=2,
    X^j (Z-gamma)^z C1,  z>=1,

with graph-centered R/S companions obtained by multiplying by

    RG = R - P' - (Z-gamma)Q',
    SG = 2*S - P'' - (Z-gamma)Q''.

The calculation is a finite exact discriminator.  It does not promote a
small-field solve to a target-uniform CRT/source theorem.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import asdict, replace
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

sys.path.insert(0, ".experiments")
import k0_degree4_degree5_full_sr_attribution_6900 as Degree  # noqa: E402


P = Degree.P
Monomial = tuple[int, int, int, int, int]  # X,Y,R,S,Z
Raw = dict[Monomial, int]
LocalMonomial = tuple[int, int, int, int, int]  # eps,S,T,R,Z
Local = dict[LocalMonomial, int]


def raw_clean(poly: Raw) -> Raw:
    return {monomial: coefficient % P for monomial, coefficient in poly.items()
            if coefficient % P}


def raw_add(left: Raw, right: Raw, scale: int = 1) -> Raw:
    answer = dict(left)
    for monomial, coefficient in right.items():
        value = (answer.get(monomial, 0) + scale * coefficient) % P
        if value:
            answer[monomial] = value
        else:
            answer.pop(monomial, None)
    return answer


def raw_scale(poly: Raw, scalar: int) -> Raw:
    return raw_clean({monomial: scalar * coefficient
                      for monomial, coefficient in poly.items()})


def raw_mul(left: Raw, right: Raw) -> Raw:
    answer: Raw = {}
    for a, ca in left.items():
        for b, cb in right.items():
            monomial = tuple(x + y for x, y in zip(a, b))
            answer[monomial] = (answer.get(monomial, 0) + ca * cb) % P
    return raw_clean(answer)


def raw_pow(poly: Raw, exponent: int) -> Raw:
    answer: Raw = {(0, 0, 0, 0, 0): 1}
    base = poly
    while exponent:
        if exponent & 1:
            answer = raw_mul(answer, base)
        exponent //= 2
        if exponent:
            base = raw_mul(base, base)
    return answer


def raw_xpoly(coefficients: tuple[int, ...]) -> Raw:
    return raw_clean({(degree, 0, 0, 0, 0): coefficient
                      for degree, coefficient in enumerate(coefficients)})


RAW_ONE: Raw = {(0, 0, 0, 0, 0): 1}
RAW_X: Raw = {(1, 0, 0, 0, 0): 1}
RAW_Y: Raw = {(0, 1, 0, 0, 0): 1}
RAW_R: Raw = {(0, 0, 1, 0, 0): 1}
RAW_S: Raw = {(0, 0, 0, 1, 0): 1}
RAW_Z: Raw = {(0, 0, 0, 0, 1): 1}


def poly_trim(poly: tuple[int, ...]) -> tuple[int, ...]:
    out = list(poly)
    while len(out) > 1 and out[-1] % P == 0:
        out.pop()
    return tuple(coefficient % P for coefficient in out)


def poly_mul(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    answer = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            answer[i + j] = (answer[i + j] + a * b) % P
    return poly_trim(tuple(answer))


def poly_pow(poly: tuple[int, ...], exponent: int) -> tuple[int, ...]:
    answer = (1,)
    base = poly
    while exponent:
        if exponent & 1:
            answer = poly_mul(answer, base)
        exponent //= 2
        if exponent:
            base = poly_mul(base, base)
    return answer


def poly_derivative(poly: tuple[int, ...], order: int = 1) -> tuple[int, ...]:
    answer = tuple(poly)
    for _ in range(order):
        answer = tuple((i + 1) * answer[i + 1] % P
                       for i in range(len(answer) - 1))
        if not answer:
            answer = (0,)
    return poly_trim(answer)


def poly_eval(poly: tuple[int, ...], x: int) -> int:
    answer = 0
    for coefficient in reversed(poly):
        answer = (answer * x + coefficient) % P
    return answer


def locator(nodes: tuple[int, ...]) -> tuple[int, ...]:
    answer = (1,)
    for node in nodes:
        answer = poly_mul(answer, ((-node) % P, 1))
    return answer


def local_clean(poly: Local) -> Local:
    return {monomial: coefficient % P for monomial, coefficient in poly.items()
            if coefficient % P}


def local_mul(left: Local, right: Local, multiplicity: int) -> Local:
    answer: Local = {}
    for a, ca in left.items():
        for b, cb in right.items():
            monomial = tuple(x + y for x, y in zip(a, b))
            if monomial[0] >= multiplicity:
                continue
            answer[monomial] = (answer.get(monomial, 0) + ca * cb) % P
    return local_clean(answer)


def local_pow(poly: Local, exponent: int, multiplicity: int) -> Local:
    answer: Local = {(0, 0, 0, 0, 0): 1}
    base = poly
    while exponent:
        if exponent & 1:
            answer = local_mul(answer, base, multiplicity)
        exponent //= 2
        if exponent:
            base = local_mul(base, base, multiplicity)
    return answer


@lru_cache(maxsize=100_000)
def flattened_raw_column(monomial: Monomial, node: int, u0: int, u1: int,
                         multiplicity: int) -> Local:
    """Literal accepted flattened contact, with no compressed E coordinate."""
    xp, yp, rp, sp, zp = monomial
    one = (0, 0, 0, 0, 0)
    eps = (1, 0, 0, 0, 0)
    local_s = (0, 1, 0, 0, 0)
    local_t = (0, 0, 1, 0, 0)
    local_r = (0, 0, 0, 1, 0)
    local_z = (0, 0, 0, 0, 1)
    x_image: Local = {one: node % P, eps: 1}
    y_image: Local = {
        one: u0 % P,
        local_z: u1 % P,
        (1, 0, 0, 1, 0): 1,
        (2, 1, 0, 0, 0): -1 % P,
        (3, 0, 1, 0, 0): 1,
    }
    answer = local_pow(x_image, xp, multiplicity)
    for image, exponent in (
            (y_image, yp), ({local_r: 1}, rp),
            ({local_s: 1}, sp), ({local_z: 1}, zp)):
        answer = local_mul(answer, local_pow(image, exponent, multiplicity),
                           multiplicity)
    return answer


def raw_contact(poly: Raw, receipt, multiplicity: int,
                nodes: tuple[int, ...]) -> dict[tuple[int, LocalMonomial], int]:
    answer: dict[tuple[int, LocalMonomial], int] = {}
    for monomial, coefficient in poly.items():
        for node in nodes:
            for local, value in flattened_raw_column(
                    monomial, node, receipt.u0[node], receipt.u1[node],
                    multiplicity).items():
                row = (node, local)
                updated = (answer.get(row, 0) + coefficient * value) % P
                if updated:
                    answer[row] = updated
                else:
                    answer.pop(row, None)
    return answer


def raw_scale_coefficients(poly: tuple[int, ...], scalar: int) -> tuple[int, ...]:
    return tuple(scalar * coefficient % P for coefficient in poly)


def raw_monomial_boundary(monomial: Monomial, receipt,
                          boundary_x: int) -> tuple[int, ...]:
    """Formal boundary gradient in (Y,R,S,Z), with S=Hasse_2(P)."""
    xp, yp, rp, sp, zp = monomial
    candidate = tuple(receipt.polynomial)
    point = (
        poly_eval(candidate, boundary_x),
        poly_eval(poly_derivative(candidate), boundary_x),
        poly_eval(raw_scale_coefficients(
            poly_derivative(candidate, 2), pow(2, -1, P)), boundary_x),
        receipt.seed % P,
    )
    exponents = (yp, rp, sp, zp)
    answer = []
    for coordinate in range(4):
        if exponents[coordinate] == 0:
            answer.append(0)
            continue
        value = pow(boundary_x, xp, P) * exponents[coordinate] % P
        for j, (base, exponent) in enumerate(zip(point, exponents)):
            value = value * pow(base, exponent - (j == coordinate), P) % P
        answer.append(value)
    return tuple(answer)


def raw_boundary(poly: Raw, receipt, boundary_x: int) -> tuple[int, ...]:
    answer = [0, 0, 0, 0]
    for monomial, coefficient in poly.items():
        gradients = raw_monomial_boundary(monomial, receipt, boundary_x)
        for coordinate, gradient in enumerate(gradients):
            answer[coordinate] = (
                answer[coordinate] + coefficient * gradient) % P
    return tuple(answer)


def source_shift(poly: Raw, shift: int) -> Raw:
    return {(monomial[0] + shift,) + monomial[1:]: coefficient
            for monomial, coefficient in poly.items()}


class SparseEchelon:
    def __init__(self):
        self.pivots: dict[object, dict[object, int]] = {}

    @property
    def rank(self) -> int:
        return len(self.pivots)

    def reduce(self, source: dict[object, int]) -> dict[object, int]:
        vector = {row: coefficient % P for row, coefficient in source.items()
                  if coefficient % P}
        while vector:
            pivot = min(vector, key=repr)
            old = self.pivots.get(pivot)
            if old is None:
                break
            coefficient = vector[pivot]
            for row, value in old.items():
                updated = (vector.get(row, 0) - coefficient * value) % P
                if updated:
                    vector[row] = updated
                else:
                    vector.pop(row, None)
        return vector

    def add(self, source: dict[object, int]) -> bool:
        vector = self.reduce(source)
        if not vector:
            return False
        pivot = min(vector, key=repr)
        inverse = pow(vector[pivot], -1, P)
        self.pivots[pivot] = {
            row: coefficient * inverse % P
            for row, coefficient in vector.items()
            if coefficient * inverse % P
        }
        return True


def vector_for_nodes(contact, nodes, minimum_epsilon_order=3):
    selected = set(nodes)
    return {row: coefficient for row, coefficient in contact.items()
            if row[0] in selected and row[1][0] >= minimum_epsilon_order}


def with_boundary(vector, boundary):
    answer = dict(vector)
    for coordinate, coefficient in enumerate(boundary):
        if coefficient:
            answer[("boundary", coordinate)] = coefficient
    return answer


def t_channel(contact, nodes, epsilon_order=3):
    selected = set(nodes)
    return {row: coefficient for row, coefficient in contact.items()
            if row[0] in selected and row[1][0] == epsilon_order and
            row[1][1:4] == (0, 1, 0)}


def main():
    started = time.monotonic()
    profile = replace(Degree.PROFILE, L=10)
    receipt = Degree.Full.M8.monomial_tangent_receipt(
        profile, Degree.TRIAL, 0)
    source = set(Degree.K0.support(profile))
    agreement = tuple(receipt.agreement)
    agreement_set = set(agreement)
    errors = tuple(node for node in receipt.nodes if node not in agreement_set)
    boundary_x = profile.n

    # Primitive semantic guard.  This prevents accidentally substituting the
    # compressed `(q,E,R,S,Z)` oracle while calling q an ordinary epsilon
    # order.  Boundary gradients below use the script order `(Y,R,S,Z)`.
    sanity_node = receipt.nodes[0]
    zero_local = (0, 0, 0, 0, 0)
    primitive_y = raw_contact(
        RAW_Y, receipt, profile.m, (sanity_node,))
    expected_y = {
        (sanity_node, zero_local): receipt.u0[sanity_node] % P,
        (sanity_node, (0, 0, 0, 0, 1)): receipt.u1[sanity_node] % P,
        (sanity_node, (1, 0, 0, 1, 0)): 1,
        (sanity_node, (2, 1, 0, 0, 0)): -1 % P,
        (sanity_node, (3, 0, 1, 0, 0)): 1,
    }
    expected_y = {row: value for row, value in expected_y.items() if value}
    assert primitive_y == expected_y
    assert raw_contact(RAW_R, receipt, profile.m, (sanity_node,)) == {
        (sanity_node, (0, 0, 0, 1, 0)): 1}
    assert raw_contact(RAW_S, receipt, profile.m, (sanity_node,)) == {
        (sanity_node, (0, 1, 0, 0, 0)): 1}
    assert raw_contact(RAW_Z, receipt, profile.m, (sanity_node,)) == {
        (sanity_node, (0, 0, 0, 0, 1)): 1}
    assert all(local[0] < profile.m for _node, local in primitive_y)

    lam_coefficients = locator(agreement)
    lam = raw_xpoly(lam_coefficients)
    p_raw = raw_xpoly(tuple(receipt.polynomial))
    q_raw = raw_xpoly(tuple(receipt.tangent))
    w_raw = raw_add(RAW_Z, raw_scale(RAW_ONE, -receipt.seed))
    a_raw = raw_add(raw_add(RAW_Y, p_raw, -1), raw_mul(w_raw, q_raw), -1)
    rg_raw = raw_add(
        raw_add(RAW_R, raw_xpoly(poly_derivative(tuple(receipt.polynomial))), -1),
        raw_mul(w_raw, raw_xpoly(poly_derivative(tuple(receipt.tangent)))), -1)
    sg_raw = raw_add(
        raw_add(raw_scale(RAW_S, 2),
                raw_xpoly(poly_derivative(tuple(receipt.polynomial), 2)), -1),
        raw_mul(w_raw, raw_xpoly(poly_derivative(tuple(receipt.tangent), 2))), -1)

    carriers = {
        k: raw_mul(raw_pow(lam, profile.m - k), raw_pow(a_raw, k))
        for k in range(1, profile.m + 1)
    }
    print("built C1..C8", file=sys.stderr, flush=True)
    c1 = carriers[1]
    assert set(c1) <= source
    c1_contact = raw_contact(c1, receipt, profile.m, receipt.nodes)
    print("built C1 literal contact", file=sys.stderr, flush=True)
    c1_boundary = raw_boundary(c1, receipt, boundary_x)
    assert c1_boundary[0] != 0
    # A has boundary gradient (1,0,0,-Q(boundary)); the already-free Z axis
    # removes the harmless last coordinate.  The R/S coordinates are zero.
    assert c1_boundary[1:3] == (0, 0)
    assert not vector_for_nodes(c1_contact, agreement, 0)

    error_residuals = tuple(
        (node,
         (receipt.u0[node] + receipt.seed * receipt.u1[node] -
          poly_eval(tuple(receipt.polynomial), node)) % P,
         (receipt.u1[node] - poly_eval(tuple(receipt.tangent), node)) % P,
         poly_eval(lam_coefficients, node))
        for node in errors)
    assert all(delta and mismatch and lambda_value
               for _node, delta, mismatch, lambda_value in error_residuals)

    # Verify the motivating epsilon^3*T coefficient identities in centered
    # W coordinates by evaluating the coefficient polynomial at enough W's.
    c2_contact = raw_contact(carriers[2], receipt, profile.m, errors)
    wc1_contact = raw_contact(raw_mul(w_raw, c1), receipt, profile.m, errors)
    print("built C2/WC1 literal contacts", file=sys.stderr, flush=True)

    def t_polynomial_evaluation(contact, node, w_value):
        z_value = (receipt.seed + w_value) % P
        value = 0
        for (row_node, local), coefficient in contact.items():
            if row_node != node or local[0:4] != (3, 0, 1, 0):
                continue
            value = (value + coefficient * pow(z_value, local[4], P)) % P
        return value

    local_t_identities = []
    for node, delta, mismatch, lambda_value in error_residuals:
        sample_rows = []
        for w_value in range(3):
            c1_value = t_polynomial_evaluation(c1_contact, node, w_value)
            wc1_value = t_polynomial_evaluation(wc1_contact, node, w_value)
            c2_value = t_polynomial_evaluation(c2_contact, node, w_value)
            expected_c1 = pow(lambda_value, profile.m - 1, P)
            expected_wc1 = w_value * expected_c1 % P
            expected_c2 = (2 * pow(lambda_value, profile.m - 2, P) *
                           (delta + mismatch * w_value)) % P
            assert (c1_value, wc1_value, c2_value) == (
                expected_c1, expected_wc1, expected_c2)
            sample_rows.append((w_value, c1_value, wc1_value, c2_value))
        local_t_identities.append({
            "node_delta_mismatch_lambda": (node, delta, mismatch, lambda_value),
            "W_samples_C1_WC1_C2": tuple(sample_rows),
            "identity": (
                "[eps^3*T]C1=lambda^(m-1), "
                "[eps^3*T](W*C1)=W*lambda^(m-1), "
                "[eps^3*T]C2=2*lambda^(m-2)*(delta+mismatch*W)"
            ),
        })

    # Exhaust every literal legal X shift and external W shift in the stated
    # multiplier box.  Shapes are limited by the actual B=3,s=1 caps.
    shape_powers = ((0, 0), (1, 0), (2, 0), (3, 0), (0, 1), (1, 1))
    def legal_shift_limit(poly):
        limit = profile.m * profile.agreements
        for xp, yp, rp, sp, zp in poly:
            if (2 * sp + rp > profile.B or sp > profile.s or
                    sp + yp + rp > profile.U or
                    sp + yp + rp + zp > profile.L):
                return -1
            limit = min(limit, profile.m * profile.agreements - 1 -
                        (xp + profile.w * yp + (profile.w - 1) * rp +
                         (profile.w - 2) * sp))
        return limit

    # Cache the small factor powers once.  The first implementation rebuilt
    # them in the innermost loop and obscured what is a small exact test.
    r_powers = {power: raw_pow(rg_raw, power) for power in range(4)}
    s_powers = {power: raw_pow(sg_raw, power) for power in range(2)}
    w_powers = {power: raw_pow(w_raw, power)
                for power in range(profile.L + 1)}
    print("built centered multiplier powers", file=sys.stderr, flush=True)
    descriptors = {family: [] for family in ("pure", "R", "S", "RS")}
    for k in range(1, profile.m + 1):
        for r_power, s_power in shape_powers:
            family = ("pure" if r_power == s_power == 0 else
                      "R" if s_power == 0 else
                      "S" if r_power == 0 else "RS")
            companion = raw_mul(r_powers[r_power], s_powers[s_power])
            carrier_companion = raw_mul(carriers[k], companion)
            for z_power in range(profile.L + 1):
                if k == 1 and z_power + r_power + s_power == 0:
                    continue
                # Every summand is homogeneous for active-plus-seed degree.
                if k + r_power + s_power + z_power > profile.L:
                    continue
                base = raw_mul(carrier_companion, w_powers[z_power])
                limit = legal_shift_limit(base)
                if limit < 0:
                    continue
                descriptors[family].append(
                    (k, r_power, s_power, z_power, base, limit))
    print("built legal carrier descriptors " + repr({
        family: (len(rows), sum(limit + 1 for *_prefix, limit in rows))
        for family, rows in descriptors.items()}), file=sys.stderr, flush=True)

    assert any(descriptors.values())
    target_head_by_scope = {
        "all_errors": vector_for_nodes(c1_contact, errors),
        **{f"error_{node}": vector_for_nodes(c1_contact, (node,))
           for node in errors},
    }
    target_t_by_scope = {
        "all_errors": t_channel(c1_contact, errors),
        **{f"error_{node}": t_channel(c1_contact, (node,))
           for node in errors},
    }
    assert all(target_head_by_scope.values())
    assert all(target_t_by_scope.values())

    stage_results = []
    echelons = {
        scope: {"head": SparseEchelon(), "T": SparseEchelon()}
        for scope in target_head_by_scope
    }
    family_order = ("pure", "R", "S", "RS")
    admitted_families = set()
    counts = defaultdict(int)
    boundary_nonzero = []
    agreement_nonzero = []
    for family in family_order:
        for descriptor_index, descriptor in enumerate(
                descriptors[family], start=1):
            k, r_power, s_power, z_power, base, limit = descriptor
            # Multiplication by X^j preserves both properties below.  Audit
            # them once per unshifted carrier rather than nine nodes for
            # every shift.
            boundary = raw_boundary(base, receipt, boundary_x)
            if boundary != (0, 0, 0, 0):
                boundary_nonzero.append((
                    family, k, r_power, s_power, z_power, 0, boundary))
            agreement_contact = raw_contact(
                base, receipt, profile.m, agreement)
            if agreement_contact:
                agreement_nonzero.append((
                    family, k, r_power, s_power, z_power, 0))
            for x_shift in range(limit + 1):
                raw = source_shift(base, x_shift)
                # The arithmetic limit above is exact for k=0; retain a
                # coefficientwise membership assertion at both endpoints.
                if x_shift in (0, limit):
                    assert set(raw) <= source
                contact = raw_contact(raw, receipt, profile.m, errors)
                counts[family] += 1
                for scope, target in target_head_by_scope.items():
                    nodes = errors if scope == "all_errors" else (int(scope[6:]),)
                    echelons[scope]["head"].add(with_boundary(
                        vector_for_nodes(contact, nodes), (0, 0, 0, 0)))
                    echelons[scope]["T"].add(with_boundary(
                        t_channel(contact, nodes), (0, 0, 0, 0)))
                if counts[family] % 25 == 0:
                    print(f"{family} contact columns {counts[family]}",
                          file=sys.stderr, flush=True)
        admitted_families.add(family)
        scope_rows = []
        for scope in target_head_by_scope:
            head_echelon = echelons[scope]["head"]
            t_echelon = echelons[scope]["T"]
            head_residual = head_echelon.reduce(with_boundary(
                target_head_by_scope[scope], (0, 0, 0, 0)))
            t_residual = t_echelon.reduce(with_boundary(
                target_t_by_scope[scope], (0, 0, 0, 0)))
            scope_rows.append({
                "scope": scope,
                "head_family_rank": head_echelon.rank,
                "entire_eps_ge_3_C1_trace_in_span": not head_residual,
                "head_residual_support": len(head_residual),
                "eps3_T_family_rank": t_echelon.rank,
                "eps3_T_C1_trace_in_span": not t_residual,
                "eps3_T_residual_support": len(t_residual),
            })
        stage_results.append({
            "stage": "plus_".join(family_order[:family_order.index(family)+1]),
            "admitted_families": tuple(sorted(admitted_families)),
            "admitted_columns": sum(counts[family]
                                    for family in admitted_families),
            "scope_results": tuple(scope_rows),
        })
    assert not boundary_nonzero
    assert not agreement_nonzero

    final_global = next(row for row in stage_results[-1]["scope_results"]
                        if row["scope"] == "all_errors")
    verdict = (
        "GREEN_FINITE_GLOBAL_CENTERED_HEAD_CORRECTION"
        if final_global["entire_eps_ge_3_C1_trace_in_span"] else
        "RED_EVEN_FULL_TESTED_CENTERED_COMPANION_FAMILY"
    )
    stable = {
        "scope": (
            "exact flattened F101 m8 all-node eps>=3 C1 correction by legal "
            "zero-boundary full-centered carriers; finite discriminator only"
        ),
        "field": P,
        "profile_n_w_g_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "trial": Degree.TRIAL,
        "agreement_set": agreement,
        "error_set": errors,
        "boundary_X_and_gamma": (boundary_x, receipt.seed),
        "candidate_and_direction_degrees": (
            Degree.K0.poly_degree(receipt.polynomial),
            Degree.K0.poly_degree(receipt.tangent)),
        "error_node_delta_mismatch_lambda": error_residuals,
        "flattened_contact_semantics": (
            "Y=u0+u1*Z+eps*R-eps^2*S+eps^3*T modulo eps^8; "
            "head means literal eps exponent >=3"
        ),
        "primitive_contact_sanity_Y_R_S_Z": True,
        "local_row_order": "(eps,S,T,R,Z)",
        "boundary_gradient_order": "(Y,R,S,Z)",
        "C1_source_terms_boundary_Y_R_S_Z_head_rows": (
            len(c1), c1_boundary, len(target_head_by_scope["all_errors"])),
        "local_eps3_T_identities": tuple(local_t_identities),
        "companion_definitions": {
            "A": "Y-P-(Z-gamma)Q",
            "Ck": "Lambda_G^(m-k)*A^k",
            "RG": "R-P'-(Z-gamma)Q'",
            "SG": "S-P''-(Z-gamma)Q''",
            "family": "X^j*(Z-gamma)^z*RG^r*SG^s*Ck",
            "shape_powers_r_s": shape_powers,
            "zero_boundary_rule": "k>=2 or z+r+s>=1",
        },
        "generated_unique_legal_columns_by_family": tuple(sorted(counts.items())),
        "every_generated_column_source_legal": True,
        "every_generated_column_zero_boundary_gradient": True,
        "every_generated_column_complete_contact_zero_on_agreements": True,
        "nested_span_results": tuple(stage_results),
        "verdict": verdict,
        "scope_guard": (
            "GREEN proves only this frozen three-error F101 simultaneous "
            "solve. It does not supply the target 81731-error bounded-degree "
            "CRT/confluence theorem. SG is deliberately graph-centered so "
            "its multiplier vanishes at the boundary; no claim is made that "
            "it is the unique osculating covariant."
        ),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    payload = {
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "runtime": {
            "seconds": round(time.monotonic() - started, 3),
            "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            "external_memory_cap_bytes": 4_200_000_000,
        },
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
