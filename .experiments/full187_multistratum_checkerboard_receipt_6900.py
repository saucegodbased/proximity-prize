#!/usr/bin/env python3
"""Exact symbolic receipt for Full187 three-term pure-seed checkerboards.

This does *not* claim a target contact correction.  It records a real
mixed-degree / mixed-H-stratum cancellation which is invisible to the
one-packet endpoint STOPs, then records the remaining error-jet work.

For the normal pure-seed specialisation

    V  = -H^2 Z,       J1 = H U Z,       J2 = B Z,

the three legal Full187 shapes

    (52,4,0), (53,2,1), (54,0,2)

obey

 B V^52 J1^4 - (B-U^2) V^53 J1^2 J2 - U^2 V^54 J2^2 = 0.

The principal identity is

 U^2 V^60 - 2 U H^3 Z V^58 J1 + H^6 Z^2 V^56 J1^2 = 0.

Its strata are r=0,1,2 and its seed shifts are 0,1,2.  A CRT multiplier q
of degree <e preserves all strict windows and makes its error value q U^2,
but it does not by itself match the higher error jets.
"""

from __future__ import annotations

import hashlib
import json
from collections import Counter
from pathlib import Path


M = 60
G = 180_413
E = 81_731
SLOPE = 21
CURVATURE = 10

# In the actual NTT-domain correction, the inverse is N^{-1} X H', whose
# degree is E.  The checkerboard below does not use that inverse.  U and B
# are the pure-seed coefficients of J1 and J2, respectively.
N = 262_144
U_DEGREE_BOUND = G + E - 1
B_DEGREE_BOUND = 2 * U_DEGREE_BOUND


def triples() -> tuple[tuple[int, int, int], ...]:
    return tuple(
        (M - 2 * c - 3 * d, c, d)
        for c in range(SLOPE + 1)
        for d in range(CURVATURE + 1)
        if M - 2 * c - 3 * d >= 0 and c + d <= SLOPE
    )


def pure_seed_width(r: int) -> int:
    """Strict X-degree allowance for the normal shell r=c+2d."""
    return M * (G - 2 * E) - (G - 2 * E - 1) * r


def monomial(a: int, c: int, d: int) -> tuple[int, int, int, int, int]:
    """Signed H,U,B,Z monomial for V^a J1^c J2^d."""
    return (a & 1, 2 * a + c, c, d, a + c + d)


def add_term(
    accumulator: Counter[tuple[int, int, int, int]], coefficient: int,
    sign: int, h: int, u: int, b: int, z: int,
) -> None:
    accumulator[(h, u, b, z)] += coefficient * sign


def expand_checkerboard(a: int, c: int, d: int) -> dict[tuple[int, int, int, int], int]:
    """Expand B*M0 - (B-U^2)*M1 - U^2*M2 in the pure-seed ring."""
    assert c >= 4
    terms: Counter[tuple[int, int, int, int]] = Counter()
    for coeff, extra_u, extra_b, triple in (
        (1, 0, 1, (a, c, d)),
        (-1, 0, 1, (a + 1, c - 2, d + 1)),
        (1, 2, 0, (a + 1, c - 2, d + 1)),
        (-1, 2, 0, (a + 2, c - 4, d + 2)),
    ):
        sign_bit, h, u, b, z = monomial(*triple)
        add_term(terms, coeff, -1 if sign_bit else 1,
                 h, u + extra_u, b + extra_b, z)
    return {key: value for key, value in terms.items() if value}


def expand_mixed_h_checkerboard() -> dict[tuple[int, int, int, int], int]:
    """Expand U^2*M(60,0,0)-2UH^3Z*M(58,1,0)+H^6Z^2*M(56,2,0)."""
    terms: Counter[tuple[int, int, int, int]] = Counter()
    for coefficient, extra_h, extra_u, extra_z, triple in (
        (1, 0, 2, 0, (60, 0, 0)),
        (-2, 3, 1, 1, (58, 1, 0)),
        (1, 6, 0, 2, (56, 2, 0)),
    ):
        sign_bit, h, u, b, z = monomial(*triple)
        add_term(terms, coefficient, -1 if sign_bit else 1,
                 h + extra_h, u + extra_u, b, z + extra_z)
    return {key: value for key, value in terms.items() if value}


def checkerboards(shell: set[tuple[int, int, int]]) -> tuple[dict[str, int], ...]:
    out = []
    for a, c, d in sorted(shell):
        r = c + 2 * d
        shifted = ((a + 1, c - 2, d + 1), (a + 2, c - 4, d + 2))
        if (
            c >= 4 and d <= CURVATURE - 2 and all(item in shell for item in shifted)
            and B_DEGREE_BOUND < pure_seed_width(r)
        ):
            assert expand_checkerboard(a, c, d) == {}
            out.append({"a": a, "c": c, "d": d, "r": r,
                        "pure_seed_width": pure_seed_width(r),
                        "margin": pure_seed_width(r) - B_DEGREE_BOUND})
    return tuple(out)


def main() -> None:
    shell_tuple = triples()
    shell = set(shell_tuple)
    assert len(shell_tuple) == len(shell) == 187
    blocks = checkerboards(shell)
    assert len(blocks) == 126
    assert blocks[0] == {
        "a": 10, "c": 13, "d": 8, "r": 29,
        "pure_seed_width": 525_510, "margin": 1_224,
    }

    displayed = (52, 4, 0)
    assert displayed in shell
    assert expand_checkerboard(*displayed) == {}
    displayed_terms = (displayed, (53, 2, 1), (54, 0, 2))
    assert all(item in shell for item in displayed_terms)
    assert all(
        a + c + d <= M and c + d <= SLOPE and d <= CURVATURE
        for a, c, d in displayed_terms
    )
    assert pure_seed_width(4) == 949_260
    assert B_DEGREE_BOUND == 524_286
    assert B_DEGREE_BOUND < pure_seed_width(4)

    mixed_h_terms = ((60, 0, 0), (58, 1, 0), (56, 2, 0))
    assert all(item in shell for item in mixed_h_terms)
    assert expand_mixed_h_checkerboard() == {}
    assert tuple(c + 2 * d for _a, c, d in mixed_h_terms) == (0, 1, 2)
    assert tuple(a + c + d + z for (a, c, d), z in
                 zip(mixed_h_terms, (0, 1, 2))) == (60, 60, 60)
    crt_degree = E - 1
    mixed_multiplier_bounds = (
        crt_degree + 2 * U_DEGREE_BOUND,
        crt_degree + U_DEGREE_BOUND + 3 * E,
        crt_degree + 6 * E,
    )
    assert mixed_multiplier_bounds == (606_016, 589_066, 572_116)
    mixed_windows = tuple(pure_seed_width(r) for r in (0, 1, 2))
    assert mixed_windows == (1_017_060, 1_000_110, 983_160)
    assert all(left < right for left, right in zip(mixed_multiplier_bounds,
                                                     mixed_windows))

    payload = {
        "scope": (
            "exact normal pure-seed identities and strict-window ledger; "
            "the mixed-H block is not yet a Full187 C_E correction"
        ),
        "target": {"m": M, "g": G, "e": E, "slope": SLOPE,
                   "curvature": CURVATURE, "N": N},
        "actual_domain_inverse_note": (
            "the natural inverse is N^{-1}*X*H' (degree e); this receipt "
            "does not use the obsolete constant-derivative inverse"
        ),
        "normal_pure_seed_specialisation": {
            "V": "-H^2 Z", "J1": "H U Z", "J2": "B Z",
        },
        "pure_factor_degree_bounds": {
            "deg_U_le": U_DEGREE_BOUND,
            "deg_B_and_U_squared_le": B_DEGREE_BOUND,
        },
        "shell_cardinality": len(shell),
        "mixed_H_three_term_checkerboard": {
            "triples": mixed_h_terms,
            "r_strata": (0, 1, 2),
            "seed_shifts": (0, 1, 2),
            "identity": (
                "U^2*V^60 - 2*U*H^3*Z*V^58*J1 + H^6*Z^2*V^56*J1^2 = 0 "
                "after the pure-seed specialisation"
            ),
            "CRT_q_degree_upper_bound": crt_degree,
            "multiplier_degree_upper_bounds": mixed_multiplier_bounds,
            "strict_pure_seed_windows": mixed_windows,
            "strict_margins": tuple(right - left for left, right in
                                    zip(mixed_multiplier_bounds, mixed_windows)),
            "error_value": (
                "at H=0, V=1, J1=0, this equals q*U^2; q can prescribe "
                "the node values because U is a unit at simple errors"
            ),
            "remaining_gap": (
                "the V^60 term still has higher E jets, so this is not a "
                "complete C_E correction without further mixed-stratum rows"
            ),
        },
        "legal_three_term_checkerboards": len(blocks),
        "r_histogram": dict(sorted(Counter(item["r"] for item in blocks).items())),
        "minimum_strict_window_margin": min(item["margin"] for item in blocks),
        "displayed_checkerboard": {
            "triples": displayed_terms,
            "identity": (
                "B*V^52*J1^4 - (B-U^2)*V^53*J1^2*J2 - U^2*V^54*J2^2 = 0 "
                "after the pure-seed specialisation"
            ),
            "r": 4,
            "strict_pure_seed_width": pure_seed_width(4),
            "multiplier_degree_upper_bound": B_DEGREE_BOUND,
            "margin": pure_seed_width(4) - B_DEGREE_BOUND,
            "error_line_warning": (
                "on E=R=0, the third summand has the exposed quadratic "
                "initial form -U^2*(L^2*S)^2"
            ),
        },
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
