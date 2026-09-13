#!/usr/bin/env python3
"""Exact symbolic receipt for the Full187 degree-59 relay.

The high binomial has reduction V^60 and first value-normalized E/TR ratio
60.  This script searches the requested explicit 2--6 row packets.  Its
new two-row low block is

    L * (U V^59 - H^3 Z V^57 J1).

It cancels under V=-H^2 Z, J1=H U Z; modulo H it is L U V^59.  Combining
the high and low blocks with effective amplitudes -58*f and 59*f gives
value=f and both first E and first T*R coefficients=f.

This is an exact first-jet GO, not a full C_E correction: all higher jets,
the other two prescribed RHS, and the Z direction remain open.
"""

from __future__ import annotations

import hashlib
import json
from collections import Counter
from pathlib import Path


M = 60
G = 180_413
E = 81_731
Q_DEGREE_MAX = E - 1
U_DEGREE = G + E - 1


def add(target, coefficient, h, u, b, z):
    target[(h, u, b, z)] += coefficient


def pure_term(coefficient, multiplier, normal):
    """Pure-seed monomial for H^h U^u B^b Z^z times V^a J1^c J2^d."""
    h, u, b, z = multiplier
    a, c, d = normal
    return coefficient * (-1 if a & 1 else 1), h + 2 * a + c, u + c, b + d, z + a + c + d


def expands_to_zero(terms):
    output = Counter()
    for coefficient, multiplier, normal in terms:
        coeff, h, u, b, z = pure_term(coefficient, multiplier, normal)
        add(output, coeff, h, u, b, z)
    return {str(key): value for key, value in output.items() if value}


def window(normal_degree, r):
    return normal_degree * (G - 2 * E) - (G - 2 * E - 1) * r


HIGH_TWO = (
    (1, (0, 1, 0, 0), (60, 0, 0)),
    (-1, (3, 0, 0, 1), (58, 1, 0)),
)
LOW_TWO = (
    (1, (0, 1, 0, 0), (59, 0, 0)),
    (-1, (3, 0, 0, 1), (57, 1, 0)),
)
J2_THREE = (
    (1, (0, 0, 1, 0), (52, 4, 0)),
    (-1, (0, 0, 1, 0), (53, 2, 1)),
    (1, (0, 2, 0, 0), (53, 2, 1)),
    (-1, (0, 2, 0, 0), (54, 0, 2)),
)
HIGH_SQUARE = (
    (1, (0, 2, 0, 0), (60, 0, 0)),
    (-2, (3, 1, 0, 1), (58, 1, 0)),
    (1, (6, 0, 0, 2), (56, 2, 0)),
)
HIGH_CUBIC = (
    (1, (0, 3, 0, 0), (60, 0, 0)),
    (-3, (3, 2, 0, 1), (58, 1, 0)),
    (3, (6, 1, 0, 2), (56, 2, 0)),
    (-1, (9, 0, 0, 3), (54, 3, 0)),
)


def check_block(name, terms):
    remainder = expands_to_zero(terms)
    assert not remainder, (name, remainder)


def main():
    # Literal normal forms and pure-seed cancellations.
    check_block("high_binomial_two", HIGH_TWO)
    check_block("low_relay_two", LOW_TWO)
    check_block("J2_same_stratum_three", J2_THREE)
    check_block("high_square_three", HIGH_SQUARE)
    check_block("high_cubic_four", HIGH_CUBIC)

    # In the normalized error chart V=1+E+T*R+O(T^2), while the J2 test
    # has total J-degree at least two.  It therefore has zero value and
    # zero first E/TR jets at J1=J2=0.
    assert min(c + d for _coef, _mul, (_a, c, d) in J2_THREE) == 2

    high_two_degrees = (Q_DEGREE_MAX + U_DEGREE, Q_DEGREE_MAX + 3 * E)
    low_two_degrees = (
        Q_DEGREE_MAX + G + U_DEGREE,
        Q_DEGREE_MAX + G + 3 * E,
    )
    high_square_degrees = (
        Q_DEGREE_MAX + 2 * U_DEGREE,
        Q_DEGREE_MAX + U_DEGREE + 3 * E,
        Q_DEGREE_MAX + 6 * E,
    )
    high_cubic_degrees = (
        Q_DEGREE_MAX + 3 * U_DEGREE,
        Q_DEGREE_MAX + 2 * U_DEGREE + 3 * E,
        Q_DEGREE_MAX + U_DEGREE + 6 * E,
        Q_DEGREE_MAX + 9 * E,
    )
    assert high_two_degrees == (343_873, 326_923)
    assert low_two_degrees == (524_286, 507_336)
    assert high_square_degrees == (606_016, 589_066, 572_116)
    assert high_cubic_degrees == (868_159, 851_209, 834_259, 817_309)

    high_two_windows = (window(60, 0), window(60, 1))
    low_two_windows = (window(59, 0), window(59, 1))
    high_square_windows = tuple(window(60, r) for r in range(3))
    high_cubic_windows = tuple(window(60, r) for r in range(4))
    assert high_two_windows == (1_017_060, 1_000_110)
    assert low_two_windows == (1_000_109, 983_159)
    assert all(degree < bound for degree, bound in zip(high_two_degrees, high_two_windows))
    assert all(degree < bound for degree, bound in zip(low_two_degrees, low_two_windows))
    assert all(degree < bound for degree, bound in zip(high_square_degrees, high_square_windows))
    assert all(degree < bound for degree, bound in zip(high_cubic_degrees, high_cubic_windows))

    # For arbitrary desired value f, effective amplitudes A=-58f and B=59f
    # solve A+B=f and 60A+59B=f.  The same equality is the T*R coefficient.
    A, B = -58, 59
    assert A + B == 1
    assert 60 * A + 59 * B == 1

    candidates = (
        {
            "rows": 2,
            "name": "high_binomial",
            "pure_seed": "zero",
            "H0_reduction": "U*V^60",
            "value_normalized_E_ratio": 60,
            "value_normalized_TR_ratio": 60,
            "verdict": "STOP: locked high ratio",
        },
        {
            "rows": 2,
            "name": "low_degree_59_relay",
            "pure_seed": "zero",
            "H0_reduction": "L*U*V^59",
            "value_normalized_E_ratio": 59,
            "value_normalized_TR_ratio": 59,
            "verdict": "relay GO: nonzero, changes the ratio",
        },
        {
            "rows": 3,
            "name": "same_stratum_J2_S_checkerboard",
            "pure_seed": "zero",
            "H0_reduction": "terms of J-degree at least two",
            "value_normalized_E_ratio": None,
            "value_normalized_TR_ratio": None,
            "verdict": "STOP for first-jet relay: zero value and zero first jet",
        },
        {
            "rows": 4,
            "name": "high_two_plus_low_two",
            "pure_seed": "zero blockwise",
            "H0_reduction": "A*V^60 + B*V^59",
            "amplitudes_for_target_value_f": {"A": "-58*f", "B": "59*f"},
            "value": "f",
            "E_jet": "f",
            "TR_jet": "f",
            "verdict": "GO: smallest packet matching value plus E/TR",
        },
        {
            "rows": 5,
            "name": "high_square_plus_low_two",
            "pure_seed": "zero blockwise",
            "H0_reduction": "A*U^2*V^60 + B*L*U*V^59",
            "value": "f after independent CRT normalization of unit U,L",
            "E_jet": "f",
            "TR_jet": "f",
            "verdict": "GO at first jet; dominated by 4-row packet",
        },
        {
            "rows": 6,
            "name": "high_cubic_plus_low_two",
            "pure_seed": "zero blockwise",
            "H0_reduction": "A*U^3*V^60 + B*L*U*V^59",
            "value": "f after independent CRT normalization of unit U,L",
            "E_jet": "f",
            "TR_jet": "f",
            "verdict": "GO at first jet; dominated by 4-row packet",
        },
    )

    payload = {
        "scope": "lower-6900 exact symbolic first-jet relay test",
        "target": {"m": M, "g": G, "e": E, "crt_degree_max": Q_DEGREE_MAX},
        "pure_seed": {"V": "-H^2*Z", "J1": "H*U*Z", "J2": "B*Z"},
        "error_chart_mod_H": "V=1+E+T*R+O(T^2); high/low J terms carry H^3",
        "strict_windows": {
            "high_two": high_two_windows,
            "low_two": low_two_windows,
            "high_square": high_square_windows,
            "high_cubic": high_cubic_windows,
        },
        "coefficient_degree_bounds": {
            "high_two": high_two_degrees,
            "low_two": low_two_degrees,
            "high_square": high_square_degrees,
            "high_cubic": high_cubic_degrees,
        },
        "strict_margins": {
            "high_two": tuple(bound - degree for degree, bound in zip(high_two_degrees, high_two_windows)),
            "low_two": tuple(bound - degree for degree, bound in zip(low_two_degrees, low_two_windows)),
            "high_square": tuple(bound - degree for degree, bound in zip(high_square_degrees, high_square_windows)),
            "high_cubic": tuple(bound - degree for degree, bound in zip(high_cubic_degrees, high_cubic_windows)),
        },
        "candidates": candidates,
        "conclusion": (
            "GO only for the exact first-jet subproblem: the 2-row degree-59 "
            "relay is literal and source-legal, and the 4-row high+low packet "
            "matches value, E, and T*R.  This does not close higher jets or 6900."
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
