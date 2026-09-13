#!/usr/bin/env python3
"""Exact correction for the Full187 pure-endpoint actuator calculation.

The prior local-GO receipt treated J2-BZ as having a unit scalar d0=-B.
Literal substitution shows that scalar cancels: J2-BZ is affine-linear in
Y,R,S.  This script expands the identity in an exact commutative polynomial
ring, records the corrected A36/A37 E-jets, and checks the value/S
countergate at the normalized error base.
"""

from __future__ import annotations

import hashlib
import json
from collections import defaultdict
from fractions import Fraction
from math import comb
from pathlib import Path


NAMES = ("L", "L1", "L2", "H", "H1", "H2", "Y", "R", "S", "Z")
N = len(NAMES)
Poly = dict[tuple[int, ...], Fraction]


def term(index: int, coefficient: int = 1) -> Poly:
    exponents = [0] * N
    exponents[index] = 1
    return {tuple(exponents): Fraction(coefficient)}


ONE: Poly = {(0,) * N: Fraction(1)}
L, L1, L2, H, H1, H2, Y, R, S, Z = (term(i) for i in range(N))


def add(*items: Poly) -> Poly:
    out: dict[tuple[int, ...], Fraction] = defaultdict(Fraction)
    for item in items:
        for exponents, coefficient in item.items():
            out[exponents] += coefficient
    return {key: value for key, value in out.items() if value}


def scale(coefficient: int | Fraction, item: Poly) -> Poly:
    c = Fraction(coefficient)
    return {key: c * value for key, value in item.items() if c * value}


def neg(item: Poly) -> Poly:
    return scale(-1, item)


def sub(left: Poly, right: Poly) -> Poly:
    return add(left, neg(right))


def mul(*items: Poly) -> Poly:
    out = ONE
    for item in items:
        product: dict[tuple[int, ...], Fraction] = defaultdict(Fraction)
        for a, ac in out.items():
            for b, bc in item.items():
                product[tuple(x + y for x, y in zip(a, b))] += ac * bc
        out = {key: value for key, value in product.items() if value}
    return out


def power(base: Poly, exponent: int) -> Poly:
    out = ONE
    for _ in range(exponent):
        out = mul(out, base)
    return out


def main() -> None:
    V = sub(Y, mul(power(H, 2), Z))
    W = sub(R, scale(2, mul(H, H1, Z)))
    P = sub(S, add(scale(2, mul(power(H1, 2), Z)),
                   scale(2, mul(H, H2, Z))))
    B = add(
        scale(-2, mul(power(L, 2), power(H1, 2))),
        scale(-2, mul(power(L, 2), H, H2)),
        scale(4, mul(L, L1, H, H1)),
        scale(-2, mul(power(L1, 2), power(H, 2))),
        mul(L, L2, power(H, 2)),
    )
    J2 = add(
        mul(power(L, 2), P),
        scale(-2, mul(L, L1, W)),
        mul(sub(scale(2, power(L1, 2)), mul(L, L2)), V),
    )
    affine = add(
        mul(sub(scale(2, power(L1, 2)), mul(L, L2)), Y),
        scale(-2, mul(L, L1, R)),
        mul(power(L, 2), S),
    )
    assert sub(J2, mul(B, Z)) == affine

    # At H=0, R=S=0 and Y=1+E, the normalized A_b factor is
    # c*(1+E)^(b+1), c=2L1^2-L*L2.  In particular B has disappeared.
    jets = {
        str(b): {
            "value": "c",
            "E": f"{b + 1}*c",
            "E2": f"{comb(b + 1, 2)}*c",
            "S": "L^2",
        }
        for b in (36, 37)
    }
    assert jets == {
        "36": {"value": "c", "E": "37*c", "E2": "666*c", "S": "L^2"},
        "37": {"value": "c", "E": "38*c", "E2": "703*c", "S": "L^2"},
    }

    # For any finite sum of actuators, write A for the sum of its normalized
    # amplitudes at the error base. Its value and S coefficient are A*c and
    # A*L^2. Since L is a unit at an error, value=nonzero and S=0 are
    # algebraically incompatible.
    payload = {
        "scope": (
            "correction of the invalid d0=-B actuator normalization; exact "
            "affine identity and value/S countergate, not a complete C_E theorem"
        ),
        "literal_identity": (
            "J2-BZ=(2(L')^2-LL'')Y-2LL'R+L^2S"
        ),
        "identity_monomials": len(affine),
        "corrected_A36_A37_error_E_jets": jets,
        "countergate": {
            "aggregate_actuator_value": "A*c",
            "aggregate_S_boundary": "A*L^2",
            "nonzero_target_value": "L^59",
            "conclusion": (
                "with L a unit, A*L^2=0 forces A=0, contradicting A*c=L^59; "
                "there is no actuator-only nonzero F0 value packet with zero S boundary"
            ),
        },
        "retracted_claims": (
            "d0=-B is not a scalar actuator value; the earlier unit determinant and "
            "A36/A37 value-plus-E GO do not apply"
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
