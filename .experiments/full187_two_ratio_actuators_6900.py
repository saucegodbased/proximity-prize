#!/usr/bin/env python3
"""Exact receipt for two Full187 pure-endpoint actuator classes.

This is deliberately a *local first-jet* construction.  It gives two
source-legal, pure-endpoint-zero classes whose H=0 value/E (and separately
value/TR) matrices are nonsingular.  It is not a complete C_E correction:
the same two CRT choices need not match both E and TR, let alone the higher
contact rows.

The pure seed is

    V=-H^2 Z, W=-2 H H' Z, P=-(2(H')^2+2H H'') Z,

and J2=L^2 P-2 L L' W+(2(L')^2-L L'')V=B Z.  Thus

    A_b(q)=q L^(60-b) V^b (J2-B Z)

has identically zero pure seed.  The literal source expansion is audited for
b=36 and b=37, including every V-binomial tail and every J2 summand.
"""

from __future__ import annotations

import hashlib
import json
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path


M = 60
G = 180_413
E = 81_731
W = 131_071
QDEG = E - 1
BDEG = 2 * (G + E - 1)


# A tiny exact commutative polynomial implementation.  It avoids making the
# receipt depend on a symbolic-algebra package while checking the displayed
# J2=BZ identity mechanically.
VARS = ("H", "Hp", "Hpp", "L", "Lp", "Lpp", "Y", "R", "S", "Z")
NVAR = len(VARS)
Poly = dict[tuple[int, ...], int]


def mono(index: int, exponent: int = 1, coefficient: int = 1) -> Poly:
    powers = [0] * NVAR
    powers[index] = exponent
    return {tuple(powers): coefficient}


def add(*items: Poly) -> Poly:
    out: dict[tuple[int, ...], int] = defaultdict(int)
    for item in items:
        for key, coefficient in item.items():
            out[key] += coefficient
    return {key: coefficient for key, coefficient in out.items() if coefficient}


def neg(item: Poly) -> Poly:
    return {key: -coefficient for key, coefficient in item.items()}


def scale(coefficient: int, item: Poly) -> Poly:
    return {key: coefficient * value for key, value in item.items() if coefficient * value}


def mul(*items: Poly) -> Poly:
    out: Poly = {(0,) * NVAR: 1}
    for item in items:
        nxt: dict[tuple[int, ...], int] = defaultdict(int)
        for left, left_coefficient in out.items():
            for right, right_coefficient in item.items():
                key = tuple(a + b for a, b in zip(left, right))
                nxt[key] += left_coefficient * right_coefficient
        out = {key: coefficient for key, coefficient in nxt.items() if coefficient}
    return out


def power(item: Poly, exponent: int) -> Poly:
    out: Poly = {(0,) * NVAR: 1}
    base = item
    n = exponent
    while n:
        if n & 1:
            out = mul(out, base)
        base = mul(base, base)
        n //= 2
    return out


H, HP, HPP, L, LP, LPP, Y, R, S, Z = (mono(i) for i in range(NVAR))


def pure_j2_receipt() -> dict[str, object]:
    v = neg(mul(H, H, Z))
    w = neg(scale(2, mul(H, HP, Z)))
    p = neg(add(scale(2, mul(HP, HP, Z)), scale(2, mul(H, HPP, Z))))
    j2 = add(
        mul(L, L, p),
        neg(scale(2, mul(L, LP, w))),
        mul(add(scale(2, mul(LP, LP)), neg(mul(L, LPP))), v),
    )
    b = add(
        neg(scale(2, mul(L, L, HP, HP))),
        neg(scale(2, mul(L, L, H, HPP))),
        scale(4, mul(L, LP, H, HP)),
        neg(scale(2, mul(LP, LP, H, H)),
        ),
        mul(L, LPP, H, H),
    )
    assert add(j2, neg(mul(b, Z))) == {}
    # The two displayed actuator numerators vanish identically after the
    # pure substitution, not merely at a sampled point.
    assert mul(power(v, 36), add(j2, neg(mul(b, Z)))) == {}
    assert mul(power(v, 37), add(j2, neg(mul(b, Z)))) == {}
    return {
        "pure_seed": {
            "V": "-H^2 Z",
            "W": "-2 H H' Z",
            "P": "-(2(H')^2+2 H H'') Z",
        },
        "B": (
            "-2 L^2(H')^2-2 L^2 H H''+4 L L' H H'"
            "-2(L')^2 H^2+L L'' H^2"
        ),
        "identity": "J2(pure seed)=B Z",
        "error_specialization": "B|_(H=0)=-2 L^2(H')^2",
        "monomial_count_J2_minus_BZ": len(add(j2, neg(mul(b, Z)))),
    }


@dataclass(frozen=True)
class SourceTerm:
    name: str
    outer_degree: int
    v_power: int
    extra_z: int
    r: int
    s: int


def source_terms(b: int) -> tuple[SourceTerm, ...]:
    # q L^(60-b)V^b(J2-BZ), after substituting V,W,P into literal Y/R/S/Z.
    # outer_degree excludes q and the V-binomial H^(2*(v_power-y)) factor.
    return (
        SourceTerm("-BZ*V^b", (M-b)*G + BDEG, b, 1, 0, 0),
        SourceTerm("L^2*S*V^b", (M-b+2)*G, b, 0, 0, 1),
        SourceTerm("L^2*P_seed*Z*V^b", (M-b+2)*G + 2*E-2, b, 1, 0, 0),
        SourceTerm("-2*L*L'*R*V^b", (M-b+2)*G-1, b, 0, 1, 0),
        SourceTerm("-2*L*L'*W_seed*Z*V^b", (M-b+2)*G + 2*E-2, b, 1, 0, 0),
        SourceTerm("(2(L')^2-L*L'')*V^(b+1)", (M-b+2)*G-2, b+1, 0, 0, 0),
    )


def expand_term(term: SourceTerm) -> tuple[dict[str, int], ...]:
    out = []
    for y in range(term.v_power + 1):
        z = term.extra_z + term.v_power-y
        coefficient_degree = term.outer_degree + QDEG + 2*E*(term.v_power-y)
        cutoff = M*G-W*y-(W-1)*term.r-(W-2)*term.s
        out.append({
            "y": y, "r": term.r, "s": term.s, "z": z,
            "coefficient_degree_upper_bound": coefficient_degree,
            "strict_X_cutoff": cutoff,
            "margin": cutoff-coefficient_degree,
            "caps_ok": (
                y+term.r+term.s <= 82
                and term.r+term.s <= 21
                and term.s <= 10
                and y+term.r+term.s+z <= 2703
            ),
        })
    return tuple(out)


def source_ledger(b: int) -> dict[str, object]:
    components = []
    all_rows = []
    for term in source_terms(b):
        rows = expand_term(term)
        all_rows.extend(rows)
        minimum = min(rows, key=lambda row: row["margin"])
        components.append({
            "term": term.name,
            "minimum_margin": minimum["margin"],
            "at_literal_shape": (minimum["y"], minimum["r"], minimum["s"], minimum["z"]),
            "coefficient_degree_upper_bound": minimum["coefficient_degree_upper_bound"],
            "strict_X_cutoff": minimum["strict_X_cutoff"],
            "all_expanded_shapes_pass_caps": all(row["caps_ok"] for row in rows),
        })
    margin = min(row["margin"] for row in all_rows)
    return {
        "b": b,
        "ell": M-b,
        "minimum_margin": margin,
        "minimum_formula": b*(G-2*E) - (BDEG+QDEG),
        "all_expanded_terms_strictly_legal": margin > 0 and all(
            row["caps_ok"] for row in all_rows),
        "components": components,
    }


def main() -> None:
    pure = pure_j2_receipt()
    ledgers = {str(b): source_ledger(b) for b in (35, 36, 37)}
    assert BDEG == 524_286
    assert ledgers["35"]["minimum_margin"] == -12_731
    assert ledgers["36"]["minimum_margin"] == 4_220
    assert ledgers["37"]["minimum_margin"] == 21_171
    assert not ledgers["35"]["all_expanded_terms_strictly_legal"]
    assert ledgers["36"]["all_expanded_terms_strictly_legal"]
    assert ledgers["37"]["all_expanded_terms_strictly_legal"]

    payload = {
        "scope": (
            "exact pure-endpoint and literal source-strip audit for the "
            "b=36,37 two-actuator first-jet pair; not a complete C_E lift"
        ),
        "target": {"m": M, "g": G, "e": E, "w": W,
                   "CRT_multiplier_degree_upper_bound": QDEG,
                   "B_degree_upper_bound": BDEG},
        "pure_seed_identity": pure,
        "general_centered_H0_jet_matrix": {
            "coordinates": "V=1+E+P, J1=a1 E+p1 P, J2=a2 E+p2 P; P=T*R",
            "row": "M_(b,c,d)=V^b J1^c J2^d",
            "value": "1 if c=d=0, otherwise 0",
            "E": (
                "b if c=d=0; a1 if (c,d)=(1,0); a2 if (c,d)=(0,1); "
                "0 if c+d>=2"
            ),
            "TR": (
                "b if c=d=0; p1 if (c,d)=(1,0); p2 if (c,d)=(0,1); "
                "0 if c+d>=2"
            ),
        },
        "actuators": {
            "definition": "A_b(q)=q L^(60-b) V^b (J2-B Z)",
            "pair": (36, 37),
            "H0_jet": (
                "write D=J2-B on Z=1 as d0+dE*E+dP*(T*R)+O(2); "
                "then jet(A_b/q)=L^(60-b)(d0, b*d0+dE, b*d0+dP)"
            ),
            "E_value_matrix": (
                "[[L^24*d0, L^23*d0], "
                "[L^24*(36*d0+dE), L^23*(37*d0+dE)]]"
            ),
            "TR_value_matrix": (
                "[[L^24*d0, L^23*d0], "
                "[L^24*(36*d0+dP), L^23*(37*d0+dP)]]"
            ),
            "both_determinants": "L^47*d0^2",
            "explicit_E_CRT_values": (
                "q36=(36*d0+dE)*L^35/d0^2; "
                "q37=-(35*d0+dE)*L^36/d0^2"
            ),
            "explicit_TR_CRT_values": (
                "replace dE by dP in the preceding two values"
            ),
            "matched_target_jet": "L^59*(1+E) (or separately L^59*(1+T*R))",
        },
        "source_ledgers": ledgers,
        "conclusion": (
            "GO for the requested two-ratio local actuator test: b=36 and "
            "b=37 are pure-endpoint-zero and source-legal with margins 4220 "
            "and 21171, and an e-degree CRT pair matches value plus E (or, "
            "with a separately chosen pair, value plus TR). Higher simultaneous "
            "jets remain open."
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
