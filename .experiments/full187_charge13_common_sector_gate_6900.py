#!/usr/bin/env python3
"""Exact Full187 charge-13 common-sector and fringe ledger.

This is deliberately only an arithmetic/basis gate.  It proves that the
eleven terminal origins form a rectangular degree-ten binary sector for the
first 76,979 X coefficients and that the remaining 55 coefficients split
into ten smaller complete binary stair steps.  It does *not* identify the
benchmark variables R,S with the conics C0,C1 in discussion #530.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
from math import factorial
import hashlib
import json
from pathlib import Path
import resource


PRIME = 2_130_706_433
W = 131_071
G = 180_413
MULTIPLICITY = 60
DEGREE = MULTIPLICITY * G
ACTIVE_CAP = 82
SLOPE_CAP = 21
CURVATURE_CAP = 10
SEED_CAP = 2_703
PASSIVE_EXPONENT = SEED_CAP - ACTIVE_CAP
COMMON_WIDTH = 76_979


@dataclass(frozen=True)
class Origin:
    s: int
    binary_i: int
    y: int
    r: int
    z: int
    width: int
    source_Y_R_S_Z: tuple[int, int, int, int]
    factored_binary_R_S: tuple[int, int]
    common_window: tuple[int, int]
    fringe_window: tuple[int, int]


@dataclass(frozen=True)
class FringeLayer:
    x_degree: int
    offset: int
    present_s: tuple[int, ...]
    residual_degree: int
    residual_binary_R_S: tuple[tuple[int, int], ...]
    common_S_factor: int


@dataclass(frozen=True)
class TopType:
    name: str
    f: int
    aE: int
    cS: int


def source_width(y: int, r: int, s: int) -> int:
    return DEGREE - W * y - (W - 1) * r - (W - 2) * s


def multinomial_scalar(y: int, f: int, h: int,
                       a_e: int, c_s: int) -> int:
    """Coefficient of u1^h E^aE (-T^2 S/2)^cS (T R)^rawR."""
    raw_r = f - a_e - c_s
    u0 = y - f - h
    assert min(raw_r, u0, h, a_e, c_s) >= 0
    integer = factorial(y) // (
        factorial(u0) * factorial(h) * factorial(a_e)
        * factorial(c_s) * factorial(raw_r)
    )
    return integer * pow(-pow(2, -1, PRIME), c_s, PRIME) % PRIME


def origin(s: int) -> Origin:
    assert 0 <= s <= CURVATURE_CAP
    r = SLOPE_CAP - s
    y = ACTIVE_CAP - r - s
    z = PASSIVE_EXPONENT
    width = source_width(y, r, s)
    binary_i = CURVATURE_CAP - s
    assert (y, r, z) == (61, 21 - s, 2_621)
    assert width == COMMON_WIDTH + s
    assert r == 11 + binary_i
    return Origin(
        s=s,
        binary_i=binary_i,
        y=y,
        r=r,
        z=z,
        width=width,
        source_Y_R_S_Z=(y, r, s, z),
        factored_binary_R_S=(binary_i, CURVATURE_CAP - binary_i),
        common_window=(0, COMMON_WIDTH),
        fringe_window=(COMMON_WIDTH, width),
    )


def fringe_layer(offset: int) -> FringeLayer:
    """One X coefficient beyond the common rectangle.

    At X^(COMMON_WIDTH+offset), only s >= offset+1 occurs.  Factoring
    S^(offset+1) leaves every degree-(9-offset) binary R/S monomial once.
    """
    assert 0 <= offset < CURVATURE_CAP
    present_s = tuple(range(offset + 1, CURVATURE_CAP + 1))
    residual_degree = CURVATURE_CAP - offset - 1
    residual = tuple(
        (CURVATURE_CAP - s, s - offset - 1) for s in present_s
    )
    assert residual == tuple(
        (i, residual_degree - i)
        for i in range(residual_degree, -1, -1)
    )
    return FringeLayer(
        x_degree=COMMON_WIDTH + offset,
        offset=offset,
        present_s=present_s,
        residual_degree=residual_degree,
        residual_binary_R_S=residual,
        common_S_factor=offset + 1,
    )


def top_contact_row(o: Origin, kind: TopType) -> dict[str, object]:
    raw_r = kind.f - kind.aE - kind.cS
    h = o.y - kind.f
    charge = 2 * kind.aE + kind.cS
    target = (
        kind.f - kind.aE + kind.cS,  # T
        kind.aE,                     # E
        o.r + raw_r,                 # R
        o.s + kind.cS,               # S
        o.z + h,                     # Z
    )
    assert charge == 13
    assert sum(target[1:]) == SEED_CAP
    return {
        "name": kind.name,
        "f_aE_cS_rawR_h_charge": (
            kind.f, kind.aE, kind.cS, raw_r, h, charge,
        ),
        "target_T_E_R_S_Z": target,
        "scalar_mod_prime": multinomial_scalar(
            o.y, kind.f, h, kind.aE, kind.cS
        ),
        "u1_power": h,
    }


def main() -> None:
    origins = tuple(origin(s) for s in range(CURVATURE_CAP + 1))
    assert len(origins) == 11
    assert tuple(o.width for o in origins) == tuple(
        range(COMMON_WIDTH, COMMON_WIDTH + 11)
    )

    # The exact ragged coefficient space.
    rectangle_dimension = len(origins) * COMMON_WIDTH
    fringe_dimension = sum(o.width - COMMON_WIDTH for o in origins)
    total_dimension = sum(o.width for o in origins)
    assert rectangle_dimension == 846_769
    assert fringe_dimension == 55
    assert total_dimension == 846_824
    assert rectangle_dimension + fringe_dimension == total_dimension

    # For every common X coefficient, after the fixed factor
    # Y^61 R^11 Z^2621, these are all degree-ten binary monomials once.
    binary_basis = tuple(o.factored_binary_R_S for o in origins)
    assert set(binary_basis) == {
        (i, CURVATURE_CAP - i) for i in range(CURVATURE_CAP + 1)
    }

    # The 55-cell ragged fringe is not arbitrary: it is ten complete binary
    # sectors of residual degrees 9,8,...,0 after fixed S powers 1,...,10.
    fringe = tuple(fringe_layer(j) for j in range(CURVATURE_CAP))
    assert tuple(len(layer.present_s) for layer in fringe) == tuple(
        range(10, 0, -1)
    )
    assert sum(len(layer.present_s) for layer in fringe) == 55

    kinds = (
        TopType("A", 7, 6, 1),
        TopType("B", 8, 5, 3),
        TopType("C", 8, 6, 1),
    )
    top_rows = {
        f"s={o.s}": tuple(top_contact_row(o, kind) for kind in kinds)
        for o in origins
    }
    scalars = {
        kind.name: top_contact_row(origins[0], kind)["scalar_mod_prime"]
        for kind in kinds
    }
    assert scalars == {
        "A": 603_758_703,
        "B": 693_269_975,
        "C": 642_373_467,
    }
    assert scalars["C"] == 54 * scalars["A"] % PRIME
    assert scalars["B"] == scalars["C"] * pow(4, -1, PRIME) % PRIME

    stable = {
        "scope": (
            "exact Full187 charge13 source-window and binary-basis gate; "
            "no C0/C1 identification and no contact-surjectivity claim"
        ),
        "parameters_p_w_g_m_D_J_q_t_L": (
            PRIME, W, G, MULTIPLICITY, DEGREE, ACTIVE_CAP,
            SLOPE_CAP, CURVATURE_CAP, SEED_CAP,
        ),
        "origins": tuple(asdict(o) for o in origins),
        "common_rectangle": {
            "fixed_source_factor": "Y^61 * R^11 * Z^2621",
            "binary_degree": 10,
            "binary_basis_R_S": binary_basis,
            "x_window_half_open": (0, COMMON_WIDTH),
            "x_layers": COMMON_WIDTH,
            "dimension": rectangle_dimension,
        },
        "fringe": {
            "dimension": fringe_dimension,
            "layer_sizes": tuple(len(layer.present_s) for layer in fringe),
            "decomposition": tuple(asdict(layer) for layer in fringe),
            "interpretation": (
                "at X^(76979+j), factor S^(j+1); what remains is the "
                "complete binary degree-(9-j) R/S basis"
            ),
        },
        "total_physical_source_dimension": total_dimension,
        "three_correlated_top_contact_rows_per_origin": top_rows,
        "top_scalar_correlations": {
            "A_B_C": (scalars["A"], scalars["B"], scalars["C"]),
            "identities": "C=54*A and B=C/4 modulo p",
        },
        "discussion_530_transfer_gate": {
            "combinatorial_match": (
                "after the fixed factor, R^i*S^(10-i) has the same index "
                "simplex as C0^i*C1^(10-i); every fringe layer similarly "
                "has a complete smaller simplex after a fixed S power"
            ),
            "literal_match": False,
            "exact_mismatch": (
                "benchmark R,S are source derivative variables, whereas "
                "discussion C0,C1 are unique conics on three derivative "
                "jets with initial forms in(C0)=a0*U+t^2*Q(Z) and "
                "in(C1)=t*(Z-s1)*(Z-s2). No local-ring initial-form "
                "isomorphism or unit-triangular bridge is supplied."
            ),
            "status": "STOP_UNTIL_INITIAL_FORM_BRIDGE",
        },
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    payload = {
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
