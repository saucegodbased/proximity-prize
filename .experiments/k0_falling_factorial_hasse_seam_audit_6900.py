#!/usr/bin/env python3
"""Exact discriminator for the locator-adic/Hasse basis proposed for k0.

This does two deliberately small things.

1.  Over F_101 it verifies the exact diagonal formula for the basis

        Lambda(X)^q X^a,

    where Lambda is the locator of five distinct agreement nodes.  At each
    node its Hasse coefficients below q vanish and the q-th coefficient is
    Lambda'(x_i)^q x_i^a.  Hence every *full* residual-degree block is an
    invertible scaled Vandermonde block.

2.  It audits the target (m,g,w)=(47,180413,131071) strict X windows.  An
    arbitrary degree-(g-1) node interpolant does not preserve an adjacent-Y
    taper: at an extremal multiplier it misses by exactly g-w-1=49341.
    A degree-w anchor interpolant fits exactly.  Thus the basis isolates the
    known seam, but cannot by itself prove a right inverse; a connector/carry
    identity from the higher R/S layers is load-bearing.

The script uses only integer arithmetic and exact prime-field elimination.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


P = 101
NODES = (1, 2, 4, 7, 11)

TARGET_CHAR = 2_130_706_433
M = 47
G = 180_413
W = 131_071
D = M * G


def trim(a: list[int]) -> list[int]:
    while len(a) > 1 and a[-1] % P == 0:
        a.pop()
    return [x % P for x in a]


def mul(a: list[int], b: list[int]) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % P
    return trim(out)


def power(a: list[int], n: int) -> list[int]:
    out = [1]
    base = a
    while n:
        if n & 1:
            out = mul(out, base)
        base = mul(base, base)
        n >>= 1
    return out


def translate(a: list[int], x: int, cutoff: int) -> list[int]:
    """Coefficients of a(x+eps) modulo eps^cutoff (Hasse coefficients)."""
    out = [0] * cutoff
    for degree, coeff in enumerate(a):
        choose = 1
        for j in range(min(degree, cutoff - 1) + 1):
            out[j] = (out[j] + coeff * choose * pow(x, degree - j, P)) % P
            if j < degree:
                choose = choose * (degree - j) // (j + 1)
    return out


def locator(nodes: tuple[int, ...]) -> list[int]:
    out = [1]
    for x in nodes:
        out = mul(out, [(-x) % P, 1])
    return out


def derivative_eval(a: list[int], x: int) -> int:
    return sum(i * c * pow(x, i - 1, P) for i, c in enumerate(a) if i) % P


def rank_mod(matrix: list[list[int]]) -> int:
    a = [[x % P for x in row] for row in matrix]
    rows = len(a)
    cols = len(a[0]) if rows else 0
    rank = 0
    for col in range(cols):
        pivot = next((r for r in range(rank, rows) if a[r][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        inv = pow(a[rank][col], P - 2, P)
        a[rank] = [(x * inv) % P for x in a[rank]]
        for r in range(rows):
            if r != rank and a[r][col]:
                factor = a[r][col]
                a[r] = [(u - factor * v) % P for u, v in zip(a[r], a[rank])]
        rank += 1
        if rank == rows:
            break
    return rank


def target_cost(y: int, r: int, s: int) -> int:
    return W * y + (W - 1) * r + (W - 2) * s


def target_window(y: int, r: int, s: int) -> int:
    return D - target_cost(y, r, s)


def locator_block(width: int) -> tuple[int, int]:
    """Number of full degree-<g blocks and width of the final partial block."""
    return divmod(width, G)


def main() -> None:
    lam = locator(NODES)
    g0 = len(NODES)
    diagonal_checks = []
    for q in range(4):
        block = []
        below_zero = True
        formula_ok = True
        for x in NODES:
            row = []
            dl = derivative_eval(lam, x)
            for a in range(g0):
                basis = mul(power(lam, q), [0] * a + [1])
                jets = translate(basis, x, q + 1)
                below_zero &= all(v == 0 for v in jets[:q])
                expected = pow(dl, q, P) * pow(x, a, P) % P
                formula_ok &= jets[q] == expected
                row.append(jets[q])
            block.append(row)
        diagonal_checks.append({
            "q": q,
            "below_q_zero": below_zero,
            "diagonal_formula": formula_ok,
            "diagonal_rank": rank_mod(block),
            "expected_rank": g0,
        })

    assert all(c["below_q_zero"] and c["diagonal_formula"] and
               c["diagonal_rank"] == g0 for c in diagonal_checks)

    critical = {
        "S_Y47": target_window(47, 0, 1),
        "S_Y48": target_window(48, 0, 1),
        "S_Y46_R": target_window(46, 1, 1),
        "Y64": target_window(64, 0, 0),
    }
    blocks = {name: locator_block(width) for name, width in critical.items()}

    # Let p have the largest legal degree in a Y^y strip.  Multiplication by
    # a degree-(g-1) interpolant, followed by lowering y once, overflows the
    # enlarged strip by exactly g-w-1.  A degree-w anchor multiplier lands on
    # its last legal degree.
    sample_width = critical["S_Y48"]
    extremal_degree = sample_width - 1
    next_window = sample_width + W
    generic_product_degree = extremal_degree + (G - 1)
    anchor_product_degree = extremal_degree + W
    seam = generic_product_degree - (next_window - 1)
    assert seam == G - W - 1 == 49_341
    assert anchor_product_degree == next_window - 1
    assert generic_product_degree >= next_window

    # In locator-adic coordinates the same exact fit is more informative.
    # S*Y^48 has 11 full Lambda blocks and a residual polynomial of width
    # 72391.  Multiplying that residual by q (degree <=w) produces one carry
    # of width exactly 23049, the partial 12th block of S*Y^47.  Replacing q
    # by the degree-(w+1) anchor locator E produces a carry of width exactly
    # 23050, the partial block of the S*Y^46*R connector.  No cap slack or
    # factorial division is hidden in either statement.
    sy48_full, sy48_partial = blocks["S_Y48"]
    sy47_full, sy47_partial = blocks["S_Y47"]
    connector_full, connector_partial = blocks["S_Y46_R"]
    q_carry_width = sy48_partial + W - G
    locator_carry_width = sy48_partial + (W + 1) - G
    assert (sy48_full, sy47_full, connector_full) == (11, 12, 12)
    assert q_carry_width == sy47_partial == 23_049
    assert locator_carry_width == connector_partial == 23_050

    # Complete target cap and characteristic audit.  Hasse coordinates need
    # no factorial division; even an ordinary derivative/falling-factorial
    # conversion up to the largest source X exponent stays below the prime.
    assert D == 8_479_411
    assert D < TARGET_CHAR
    assert G < TARGET_CHAR and W < TARGET_CHAR and M < TARGET_CHAR

    payload = {
        "scope": "k0 locator-adic Hasse diagonal and strict-taper seam",
        "small_exact_field_and_nodes": (P, NODES),
        "locator_coefficients_low_to_high": lam,
        "diagonal_checks": diagonal_checks,
        "target_char_m_g_w_D": (TARGET_CHAR, M, G, W, D),
        "target_factorial_index_upper_bound_below_char": D - 1,
        "critical_windows": critical,
        "critical_locator_blocks_full_and_partial": blocks,
        "adjacent_y_extremal": {
            "source_width": sample_width,
            "lower_y_width": next_window,
            "generic_degree_g_minus_1_product_degree": generic_product_degree,
            "generic_overflow_past_last_legal_degree": seam,
            "anchor_degree_w_product_degree": anchor_product_degree,
            "anchor_lands_on_last_legal_degree": True,
        },
        "locator_adic_exact_carries": {
            "SY48_partial_width": sy48_partial,
            "times_degree_w_carry_width": q_carry_width,
            "SY47_receiving_partial_width": sy47_partial,
            "times_degree_w_plus_1_carry_width": locator_carry_width,
            "SY46R_receiving_partial_width": connector_partial,
            "anchor_q_and_locator_E_carries_fit_exactly": True,
        },
        "verdict": (
            "GO for the full-block Hasse diagonal and the exact q/E carry; "
            "RED as a standalone global right inverse because a generic "
            "degree-(g-1) interpolant still leaves a 49341-degree T seam"
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
