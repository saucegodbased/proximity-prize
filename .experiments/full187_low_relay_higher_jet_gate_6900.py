#!/usr/bin/env python3
"""Exact higher-jet gate for the Full187 staggered low relay ladder.

The literal local value coordinate is

    V = 1 + E + T*R - T^2*S/2.

For n=60,59,58,57 the two-row pure-seed-cancelling blocks have nonzero
reduction A_n V^n.  This script expands their V-sector through contact
weight three (weight(T)=1, weight(E)=3), checks the source strips, and
separates the intrinsic binomial moments from the still-open CRT-Hermite
coefficient jets and the H^3*J1 tail.
"""

from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from math import comb
from pathlib import Path


M = 60
G = 180_413
ELOC = 81_731
QMAX = ELOC - 1
UDEG = G + ELOC - 1


def add(left, right):
    out = dict(left)
    for key, coefficient in right.items():
        out[key] = out.get(key, Fraction(0)) + coefficient
    return {key: value for key, value in out.items() if value}


def multiply(left, right, contact_limit=3):
    """Polynomials in (T,E,R,S), truncated by deg(T)+3 deg(E)."""
    out = {}
    for exponent_l, coefficient_l in left.items():
        for exponent_r, coefficient_r in right.items():
            exponent = tuple(a + b for a, b in zip(exponent_l, exponent_r))
            if exponent[0] + 3 * exponent[1] <= contact_limit:
                out[exponent] = out.get(exponent, Fraction(0)) + coefficient_l * coefficient_r
    return {key: value for key, value in out.items() if value}


def power(base, exponent):
    result = {(0, 0, 0, 0): Fraction(1)}
    for _ in range(exponent):
        result = multiply(result, base)
    return result


def v_sector(amplitudes):
    local_v = {
        (0, 0, 0, 0): Fraction(1),
        (0, 1, 0, 0): Fraction(1),       # E
        (1, 0, 1, 0): Fraction(1),       # T R
        (2, 0, 0, 1): Fraction(-1, 2),   # -T^2 S / 2
    }
    result = {}
    for n, amplitude in amplitudes.items():
        for exponent, coefficient in power(local_v, n).items():
            result[exponent] = result.get(exponent, Fraction(0)) + amplitude * coefficient
    return {str(exponent): str(value) for exponent, value in sorted(result.items()) if value}


def moment_vector(amplitudes):
    return tuple(sum(amplitude * comb(n, k) for n, amplitude in amplitudes.items())
                 for k in range(5))


def window(n, r):
    return n * (G - 2 * ELOC) - (G - 2 * ELOC - 1) * r


def coefficient_degrees(n):
    locator_head = 60 - n
    return (
        QMAX + locator_head * G + UDEG,
        QMAX + locator_head * G + 3 * ELOC,
    )


def pure_signature(coefficient, h_shift, u_shift, z_shift, n, c):
    """Signature after V=-H^2 Z and J1=H U Z (B degree unused here)."""
    return (
        coefficient * (-1 if n & 1 else 1),
        h_shift + 2 * n + c,
        u_shift + c,
        z_shift + n + c,
    )


def assert_relay_seed_identity(n):
    # U V^n - H^3 Z V^(n-2) J1
    first = pure_signature(1, 0, 1, 0, n, 0)
    second = pure_signature(-1, 3, 0, 1, n - 2, 1)
    assert first[1:] == second[1:]
    assert first[0] + second[0] == 0


def main():
    two = {60: -58, 59: 59}
    three = {60: 1653, 59: -3363, 58: 1711}
    four = {60: -30856, 59: 94164, 58: -95816, 57: 32509}
    for n in range(57, 61):
        assert_relay_seed_identity(n)

    assert moment_vector(two) == (1, 1, -1711, -66729, -1430396)
    assert moment_vector(three) == (1, 1, 0, 32509, 1397887)
    assert moment_vector(four) == (1, 1, 0, 0, -455126)

    target_sector = {
        "(0, 0, 0, 0)": "1",
        "(0, 1, 0, 0)": "1",
        "(1, 0, 1, 0)": "1",
        "(2, 0, 0, 1)": "-1/2",
    }
    two_sector = v_sector(two)
    three_sector = v_sector(three)
    four_sector = v_sector(four)
    assert two_sector["(2, 0, 2, 0)"] == "-1711"
    assert three_sector["(3, 0, 3, 0)"] == "32509"
    assert four_sector == target_sector

    strips = {}
    for n in range(56, 61):
        degrees = coefficient_degrees(n)
        windows = (window(n, 0), window(n, 1))
        strips[str(n)] = {
            "coefficient_degrees": degrees,
            "strict_windows": windows,
            "margins": tuple(bound - degree for degree, bound in zip(degrees, windows)),
            "legal": all(degree < bound for degree, bound in zip(degrees, windows)),
        }
    assert strips["60"]["margins"] == (673187, 673187)
    assert strips["59"]["margins"] == (475823, 475823)
    assert strips["58"]["margins"] == (278459, 278459)
    assert strips["57"]["margins"] == (81095, 81095)
    assert strips["56"]["margins"] == (-116269, -116269)

    payload = {
        "scope": "lower-6900 exact local V-sector gate for the R60/R59 relay",
        "local_coordinate": "V=1+E+T*R-T^2*S/2",
        "contact_weight": {"T": 1, "E": 3, "R": 0, "S": 0},
        "target_F0_normalized_V_sector": target_sector,
        "two_relay": {
            "degrees": (60, 59),
            "amplitudes": two,
            "binomial_moments_choose_n_0_through_4": moment_vector(two),
            "V_sector": two_sector,
            "verdict": "STOP at order 2: T^2*R^2 coefficient is -1711",
        },
        "three_relay": {
            "degrees": (60, 59, 58),
            "amplitudes": three,
            "binomial_moments_choose_n_0_through_4": moment_vector(three),
            "V_sector": three_sector,
            "verdict": "GO through order 2; STOP at order 3: T^3*R^3 coefficient is 32509",
        },
        "four_relay": {
            "degrees": (60, 59, 58, 57),
            "amplitudes": four,
            "binomial_moments_choose_n_0_through_4": moment_vector(four),
            "V_sector": four_sector,
            "verdict": "GO for the entire intrinsic V sector through contact weight 3",
        },
        "literal_strips": strips,
        "pure_seed_block": "L^(60-n)*(U*V^n-H^3*Z*V^(n-2)*J1), n=57..60",
        "literal_J1_tail_at_weight_three": (
            "with h=H'(x), Z=1, and J1=-L'+L*R+O(T,E), "
            "-a_n*(h*T)^3*J1 = a_n*h^3*L'*T^3-a_n*h^3*L*T^3*R; "
            "it has no R^2, R*S, or R^3 component"
        ),
        "first_unproved_condition": (
            "The degree-<e CRT representatives are fixed after their node values are set. "
            "Their T,Hasse derivatives must satisfy the longitudinal Hermite equations, and "
            "the H^3*Z*J1 tail begins in horizontal order three.  The V-sector moments do "
            "not prove those derivative equations or the full C_E contact claim."
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
