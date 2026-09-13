#!/usr/bin/env python3
"""Exact target-strip arithmetic for the centered Full187 Wronskian shell.

For m=60, b=23, Q=Xi^2, and

 V^(m-2) Z^b (c V^2 + B V Z + A Xi Lambda V1 Z),

with B + A Xi Lambda' = C Lambda, this checks every collected literal
X-strip after the exact boundary-head collection

 B0 = B - c Q + 2 A Lambda Xi'.

It proves only degree feasibility.  It does not construct A,C,c for any of
the three RHS, nor prove a target HRS recurrence.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


M = 60
BSEED = 23
G = 180_413
E = 81_731
W = 131_071
J = 82
PASSIVE = 21
CURVATURE = 10
SEED_CAP = 2703

MG = M * G
QDEG = 2 * E


def cutoff(y: int, r: int = 0, s: int = 0) -> int:
    return MG - W * y - (W - 1) * r - (W - 2) * s


def shape_ok(y: int, r: int, s: int, z: int) -> bool:
    return (y + r + s <= J and r + s <= PASSIVE and s <= CURVATURE
            and y + r + s + z <= SEED_CAP)


def degree_caps() -> dict[str, int]:
    """Strict degree bounds d < cap derived from all raw collected strips."""
    # c first appears independently at y=1 in the pure sector.
    cap_c = min(cutoff(y) - 2 * E * (M - y) for y in range(1, M + 1))
    # B0 has the special y=0 coefficient B0*(-Q)^(m-1).
    cap_b0 = min(
        [cutoff(0) - 2 * E * (M - 1)]
        + [cutoff(y) - 2 * E * (M - 1 - y) for y in range(1, M)])
    # The A*Lambda*Xi' pure contribution begins at y=1 after B0 collection.
    cap_a_pure = min(
        cutoff(y) - G - (2 * M - 1 - 2 * y) * E + 1
        for y in range(1, M - 1))
    # The A*Xi*Lambda*R contribution begins at y=0.
    cap_a_r = min(
        cutoff(y, 1) - G - (2 * M - 3 - 2 * y) * E
        for y in range(M - 1))
    assert cap_a_pure == cap_a_r
    # C Lambda enters B0 without an assumed extra cancellation.
    cap_c_big = cap_b0 - G
    # Componentwise caps which make deg(B0)<cap_b0 without relying on a
    # cancellation between cQ and A(2 Lambda Xi'-Xi Lambda').
    cap_c_unconditional = cap_b0 - 2 * E
    cap_a_unconditional = cap_b0 - (G + E - 1)
    return {
        "A": cap_a_r,
        "c": cap_c,
        "C": cap_c_big,
        "B0": cap_b0,
        "A_without_B0_cancellation": cap_a_unconditional,
        "c_without_B0_cancellation": cap_c_unconditional,
    }


def raw_rows(caps: dict[str, int]) -> list[dict[str, object]]:
    """Collected source rows; degree is affine in dA/dB0/dc."""
    rows: list[dict[str, object]] = []
    # y=0 is the exact B0 boundary-zero head, not three separately charged
    # c/B/A terms.
    rows.append({
        "family": "B0_head", "shape": (0, 0, 0, BSEED + M),
        "degree": "dB0+2e*(m-1)",
        "strict_cap_on_coefficient": cutoff(0) - 2 * E * (M - 1),
    })
    # For 1<=y<=m-2, use
    # (-Q)^(m-2-y)[ C(m-1,y-1)cQ^2 - C(m-1,y)B0Q
    #                 +2C(m-2,y-1)A Lambda Xi' Q ].
    for y in range(1, M - 1):
        z = BSEED + M - y
        assert shape_ok(y, 0, 0, z)
        rows.extend((
            {"family": "c_pure", "shape": (y, 0, 0, z),
             "degree": "dc+2e*(m-y)",
             "strict_cap_on_coefficient": cutoff(y) - 2 * E * (M - y)},
            {"family": "B0_pure", "shape": (y, 0, 0, z),
             "degree": "dB0+2e*(m-1-y)",
             "strict_cap_on_coefficient": cutoff(y) - 2 * E * (M - 1 - y)},
            {"family": "A_Xi_prime_pure", "shape": (y, 0, 0, z),
             "degree": "dA+g+(2m-1-2y)e-1",
             "strict_cap_on_coefficient": cutoff(y) - G - (2 * M - 1 - 2 * y) * E + 1},
        ))
    # The two terminal pure shapes have fewer summands and are never binding;
    # include them for a complete raw ledger.
    rows.extend((
        {"family": "terminal_y_m_minus_1_B0", "shape": (M - 1, 0, 0, BSEED + 1),
         "degree": "dB0", "strict_cap_on_coefficient": cutoff(M - 1)},
        {"family": "terminal_y_m_minus_1_cQ", "shape": (M - 1, 0, 0, BSEED + 1),
         "degree": "dc+2e", "strict_cap_on_coefficient": cutoff(M - 1) - 2 * E},
        {"family": "terminal_y_m_minus_1_A", "shape": (M - 1, 0, 0, BSEED + 1),
         "degree": "dA+g+e-1", "strict_cap_on_coefficient": cutoff(M - 1) - G - E + 1},
        {"family": "terminal_y_m_c", "shape": (M, 0, 0, BSEED),
         "degree": "dc", "strict_cap_on_coefficient": cutoff(M)},
    ))
    # A Xi Lambda R V^(m-2) Z^(b+1).
    for y in range(M - 1):
        z = BSEED + M - 1 - y
        assert shape_ok(y, 1, 0, z)
        rows.append({
            "family": "A_R", "shape": (y, 1, 0, z),
            "degree": "dA+g+(2m-3-2y)e",
            "strict_cap_on_coefficient": cutoff(y, 1) - G - (2 * M - 3 - 2 * y) * E,
        })
    return rows


def main() -> None:
    caps = degree_caps()
    assert caps == {
        "A": 950_770,
        "c": 1_049_451,
        "C": 1_000_109,
        "B0": 1_180_522,
        "A_without_B0_cancellation": 918_379,
        "c_without_B0_cancellation": 1_017_060,
    }
    rows = raw_rows(caps)
    assert len(rows) == 1 + 3 * 58 + 4 + 59
    assert all(shape_ok(*row["shape"]) for row in rows)

    # Strict endpoint equalities: cap-1 is legal by one X degree.
    assert (caps["B0"] - 1) + 2 * E * 59 == MG - 1
    assert (caps["c"] - 1) + 2 * E * 59 == cutoff(1) - 1
    assert (caps["A"] - 1) + G + 117 * E - 1 == cutoff(1) - 1
    assert (caps["A"] - 1) + G + 117 * E == cutoff(0, 1) - 1

    # The leading B0 expression after B+A*Xi*Lambda'=C*Lambda is
    # B0=C*Lambda-c*Q+A*(2*Lambda*Xi'-Xi*Lambda').
    # Its three uncancelled degree charges are as follows.
    b0_charges = {
        "C_Lambda": (caps["C"] - 1) + G,
        "c_Q_at_sharp_c_cap": (caps["c"] - 1) + 2 * E,
        "A_wronskian_at_sharp_A_cap": (caps["A"] - 1) + G + E - 1,
        "B0_cap_minus_1": caps["B0"] - 1,
    }
    assert b0_charges == {
        "C_Lambda": 1_180_521,
        "c_Q_at_sharp_c_cap": 1_212_912,
        "A_wronskian_at_sharp_A_cap": 1_212_912,
        "B0_cap_minus_1": 1_180_521,
    }
    assert b0_charges["c_Q_at_sharp_c_cap"] - b0_charges["B0_cap_minus_1"] == 32_391
    wronskian_cofactor_degree = G + E - 1
    assert wronskian_cofactor_degree == 262_143
    assert 2 * E - G == -16_951

    # Conservative simultaneous depth-three Hermite CRT: each of A,C,c may
    # have an independently chosen representative of degree <3e.  It fits
    # even the componentwise (no B0-cancellation) caps.
    hermite_three_degree = 3 * E - 1
    assert hermite_three_degree == 245_192
    assert hermite_three_degree < caps["A_without_B0_cancellation"]
    assert hermite_three_degree < caps["c_without_B0_cancellation"]
    assert hermite_three_degree < caps["C"]
    b0_depth_three_charges = {
        "C_Lambda": hermite_three_degree + G,
        "c_Q": hermite_three_degree + 2 * E,
        "A_wronskian": hermite_three_degree + G + E - 1,
    }
    assert b0_depth_three_charges == {
        "C_Lambda": 425_605,
        "c_Q": 408_654,
        "A_wronskian": 507_335,
    }
    b0_depth_three_degree = max(b0_depth_three_charges.values())
    b0_head_margin = MG - (b0_depth_three_degree + 2 * E * 59)
    assert b0_head_margin == 673_187

    payload = {
        "scope": (
            "raw source-strip feasibility for the target centered Wronskian shell; "
            "no construction of coefficient polynomials or THREE-RHS theorem"),
        "target": {"m": M, "b": BSEED, "g": G, "e": E, "w": W,
                   "J": J, "passive": PASSIVE, "curvature": CURVATURE,
                   "seed_cap": SEED_CAP},
        "shell": (
            "V^(m-2) Z^b (c V^2+B V Z+A Xi Lambda V1 Z), "
            "B+A Xi Lambda'=C Lambda"),
        "B0_identity": "B0=B-cQ+2A Lambda Xi'=C Lambda-cQ+A(2 Lambda Xi'-Xi Lambda')",
        "raw_strict_degree_caps": caps,
        "raw_row_count": len(rows),
        "all_shape_caps_pass": all(shape_ok(*row["shape"]) for row in rows),
        "B0_sharp_charge_ledger": b0_charges,
        "wronskian_cofactor": {
            "polynomial": "2 Lambda Xi'-Xi Lambda'",
            "degree": wronskian_cofactor_degree,
            "leading_degree_coefficient_2e_minus_g": 2 * E - G,
            "sharp_B0_head_cancellation_degrees_required": 32_391,
        },
        "depth_three_Hermite_CRT": {
            "degree_upper_bound": hermite_three_degree,
            "componentwise_caps_pass_without_B0_cancellation": True,
            "B0_component_degrees": b0_depth_three_charges,
            "B0_y0_strict_margin": b0_head_margin,
        },
        "three_RHS_degree_verdict": (
            "YES for degree budget only: three independently interpolated coefficient triples, "
            "or a conservative depth-three Hermite representative per coefficient, fit these "
            "source caps. NO coefficient-existence claim is made: the required nodewise values, "
            "the B+A Xi Lambda' divisibility, and the three actual contact syndromes remain open."
        ),
        "binding_rows": {
            "B0_y0": {"shape": (0, 0, 0, 83), "cap": caps["B0"]},
            "c_y1": {"shape": (1, 0, 0, 82), "cap": caps["c"]},
            "A_pure_y1": {"shape": (1, 0, 0, 82), "cap": caps["A"]},
            "A_R_y0": {"shape": (0, 1, 0, 82), "cap": caps["A"]},
        },
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
