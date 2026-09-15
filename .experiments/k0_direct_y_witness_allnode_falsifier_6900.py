#!/usr/bin/env python3
"""Exact all-node falsifier for the tempting direct Y head witness.

On the frozen F_101 m8 chamber form the literal target-scaled analogue

    F = Lambda_G^(m-1) * (Y - P(X) - Q(X)*(Z-gamma)),

where Lambda_G vanishes on the retained agreement set, P is the candidate,
and Q is the agreement-direction interpolant.  The source support is legal.
At every agreement the bracket has contact order at least one, so F has zero
truncated contact there.  At errors Lambda_G is a unit and the head contact
generically survives.  This directly tests the all-node composition issue;
agreement-only vanishing is not enough for the complete head kernel.
"""

from __future__ import annotations

from dataclasses import asdict, replace
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

sys.path.insert(0, ".experiments")
import k0_degree4_degree5_full_sr_attribution_6900 as Degree  # noqa: E402


P_FIELD = Degree.P


def trim(poly):
    value = list(poly)
    while len(value) > 1 and value[-1] % P_FIELD == 0:
        value.pop()
    return tuple(x % P_FIELD for x in value)


def add(left, right):
    size = max(len(left), len(right))
    return trim(tuple(
        ((left[i] if i < len(left) else 0) +
         (right[i] if i < len(right) else 0)) % P_FIELD
        for i in range(size)))


def scale(c, poly):
    return trim(tuple(c * x % P_FIELD for x in poly))


def mul(left, right):
    out = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i + j] = (out[i + j] + a * b) % P_FIELD
    return trim(tuple(out))


def power(poly, exponent):
    out = (1,)
    base = poly
    while exponent:
        if exponent & 1:
            out = mul(out, base)
        exponent //= 2
        if exponent:
            base = mul(base, base)
    return out


def locator(nodes):
    out = (1,)
    for x in nodes:
        out = mul(out, ((-x) % P_FIELD, 1))
    return out


def add_xpoly_shape(raw, poly, shape, scalar=1):
    yp, rp, sp, zp = shape
    for a, coefficient in enumerate(poly):
        value = scalar * coefficient % P_FIELD
        monomial = (a, yp, rp, sp, zp)
        raw[monomial] = (raw.get(monomial, 0) + value) % P_FIELD
        if not raw[monomial]:
            raw.pop(monomial)


def main():
    started = time.monotonic()
    profile = replace(Degree.PROFILE, L=10)
    receipt = Degree.Full.M8.monomial_tangent_receipt(
        profile, Degree.TRIAL, 0)
    lam = locator(receipt.agreement)
    lam_power = power(lam, profile.m - 1)
    lam_P = mul(lam_power, receipt.polynomial)
    lam_Q = mul(lam_power, receipt.tangent)
    raw = {}
    add_xpoly_shape(raw, lam_power, (1, 0, 0, 0), 1)
    add_xpoly_shape(raw, lam_P, (0, 0, 0, 0), -1)
    add_xpoly_shape(raw, lam_Q, (0, 0, 0, 1), -1)
    add_xpoly_shape(raw, lam_Q, (0, 0, 0, 0), receipt.seed)

    source = set(Degree.K0.support(profile))
    assert all(monomial in source for monomial in raw)
    contact = {}
    per_node = {x: {} for x in receipt.nodes}
    for monomial, coefficient in raw.items():
        for row, value in Degree.Full.expansions(profile, receipt, monomial):
            entry = coefficient * value % P_FIELD
            if entry:
                contact[row] = (contact.get(row, 0) + entry) % P_FIELD
                if not contact[row]:
                    contact.pop(row)
    for (node, term), value in contact.items():
        per_node[node][term] = value

    agreement_support = sum(len(per_node[x]) for x in receipt.agreement)
    errors = tuple(x for x in receipt.nodes if x not in set(receipt.agreement))
    error_support = sum(len(per_node[x]) for x in errors)
    head_support = sum(
        1 for x in errors for term in per_node[x] if term[0] >= 3)
    assert agreement_support == 0
    assert error_support > 0
    assert head_support > 0

    boundary = [0, 0, 0, 0]
    for monomial, coefficient in raw.items():
        gradients = Degree.K0.monomial_gradient_polys(monomial, receipt)
        for coordinate, polynomial in enumerate(gradients):
            boundary[coordinate] = (
                boundary[coordinate] +
                coefficient * int(polynomial(profile.n))) % P_FIELD
    boundary = tuple(boundary)
    lam_at_boundary = sum(
        coefficient * pow(profile.n, i, P_FIELD)
        for i, coefficient in enumerate(lam_power)) % P_FIELD
    assert boundary[0] == lam_at_boundary  # ordering (Y,R,S,Z) in script
    assert boundary[0] != 0

    payload = {
        "scope": "exact direct-Y witness all-node/head falsifier",
        "field": "F_101",
        "profile_n_w_g_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "agreement_set": receipt.agreement,
        "errors": errors,
        "candidate_and_direction_degrees": (
            len(receipt.polynomial) - 1, len(trim(receipt.tangent)) - 1),
        "lambda_degree_and_power": (len(lam) - 1, profile.m - 1),
        "raw_support_size_and_source_legal": (len(raw), True),
        "agreement_contact_support": agreement_support,
        "error_contact_support": error_support,
        "error_head_outer_ge_3_support": head_support,
        "boundary_gradient_script_order_Y_R_S_Z": boundary,
        "lambda_power_at_boundary": lam_at_boundary,
        "verdict": (
            "RED for complete head kernel: source-legal and contact-zero on "
            "agreements, but nonzero high-order contact survives at errors"
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    payload["runtime"] = {
        "seconds": round(time.monotonic() - started, 3),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
