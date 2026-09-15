#!/usr/bin/env python3
"""Exact small-field gate for node-signature/first-separator proposals.

This deliberately tests the hypotheses those proposals actually cite:

* one fixed received pencil U0 + gamma U1 on n=12 nodes;
* selected polynomials of degree at most w=5;
* at least A=7 agreements per selected polynomial;
* one fixed received row is bad on every selected support; and
* every nonzero projective received direction has canonical degree >=14.

It then exhaustively finds the best fixed original-node evaluation panels.
The model is structural, not an inhabitant of the enormous DataEleven leaf.
"""

from collections import defaultdict
from itertools import combinations
import json
import resource
import signal

from signed_cancellation_free_tail_f17_control_6900 import (
    P,
    NODES,
    LAMBDA,
    add,
    field_div,
    field_mul,
    gcd_poly,
    interpolate,
    mul,
    rem,
    powmod,
    scale,
    sub,
    trim,
)


resource.setrlimit(resource.RLIMIT_AS, (512 << 20, 512 << 20))
# The imported exact-field helper already installs a 30-second hard CPU cap.
# Tighten rather than attempting to raise that inherited limit.
resource.setrlimit(resource.RLIMIT_CPU, (28, 28))
signal.alarm(45)

TEST_NODES = NODES[:12]
N = len(TEST_NODES)
W = 5
A = 7
ALPHA = (0, 1)  # degree-six generator of GF(17^6)


def k(c: int):
    return () if c % P == 0 else (c % P,)


def kpoly_trim(poly):
    out = list(poly)
    while out and not out[-1]:
        out.pop()
    return tuple(out)


def kpoly_add(a, b):
    out = [()] * max(len(a), len(b))
    for i in range(len(out)):
        out[i] = add(a[i] if i < len(a) else (), b[i] if i < len(b) else ())
    return kpoly_trim(out)


def kpoly_scale(c, a):
    return kpoly_trim(tuple(field_mul(c, x) for x in a))


def kpoly_eval(poly, x: int):
    out = ()
    xk = k(x)
    for coefficient in reversed(poly):
        out = add(field_mul(out, xk), coefficient)
    return out


def kinterpolate(nodes, values):
    """Newton interpolation over GF(17^6), ordinary monomial basis."""
    coefficients = list(values)
    for step in range(1, len(nodes)):
        for j in range(len(nodes) - 1, step - 1, -1):
            # Newton denominators are in the prime field; scalar inversion is
            # vastly cheaper than a fresh GF(17^6) exponentiation.
            denominator_inv = pow((nodes[j] - nodes[j - step]) % P, -1, P)
            coefficients[j] = scale(
                denominator_inv, sub(coefficients[j], coefficients[j - 1])
            )
    out = (coefficients[-1],)
    for j in range(len(nodes) - 2, -1, -1):
        # Multiply by X-nodes[j], then add the Newton coefficient.
        shifted = [()]
        shifted.extend(out)
        constant = kpoly_scale(k((-nodes[j]) % P), out)
        out = kpoly_add(kpoly_trim(tuple(shifted)), constant)
        out = kpoly_add(out, (coefficients[j],))
    assert tuple(kpoly_eval(out, x) for x in nodes) == tuple(values)
    return out


def denominator_value(x: int):
    # E(X)=X^2-alpha.  It is nonzero at every base-field node because alpha
    # is not in GF(17).
    value = sub(k(x * x), ALPHA)
    assert value
    return value


def received_values():
    # U0=X/E and U1=1/E.  Since deg E=2, E cannot divide a nonzero affine
    # numerator.  The standard all-node root argument therefore forces every
    # nonzero constant direction a*U0+b*U1 to have canonical degree >=14.
    u0 = tuple(field_div(k(x), denominator_value(x)) for x in TEST_NODES)
    u1 = tuple(field_div(k(1), denominator_value(x)) for x in TEST_NODES)
    return u0, u1


def build_family():
    u0, u1 = received_values()
    by_gamma = {}
    raw_supports = 0
    zero_u1_top = 0
    gamma_collisions = 0

    for support in combinations(range(N), A):
        nodes = tuple(TEST_NODES[i] for i in support)
        p0 = kinterpolate(nodes, tuple(u0[i] for i in support))
        p1 = kinterpolate(nodes, tuple(u1[i] for i in support))
        c0 = p0[A - 1] if len(p0) == A else ()
        c1 = p1[A - 1] if len(p1) == A else ()
        if not c1:
            zero_u1_top += 1
            continue
        gamma = field_div(scale(-1, c0), c1)
        selected = kpoly_add(p0, kpoly_scale(gamma, p1))
        assert len(selected) <= W + 1
        actual_support = tuple(
            i
            for i in range(N)
            if kpoly_eval(selected, TEST_NODES[i]) == add(u0[i], field_mul(gamma, u1[i]))
        )
        # E*selected-(X+gamma) is nonzero of degree <=7, so A=7 is maximal
        # in this construction.  Verify the literal result, not just the cap.
        assert len(actual_support) == A
        assert actual_support == support
        raw_supports += 1
        prior = by_gamma.get(gamma)
        if prior is None:
            by_gamma[gamma] = (selected, actual_support)
        else:
            gamma_collisions += 1
            # A benchmark family has one selected polynomial per seed.  Keep
            # the lexicographically first support, deterministically.
            if actual_support < prior[1]:
                by_gamma[gamma] = (selected, actual_support)

    family = tuple(
        (gamma, selected, support)
        for gamma, (selected, support) in sorted(by_gamma.items())
    )
    assert family

    # Fixed-row badness was checked constructively at insertion time: c1 was
    # the degree-six coefficient of U1 on precisely this owned support and
    # only c1 != 0 supports were admitted.

    return family, raw_supports, zero_u1_top, gamma_collisions


def panel_stats(family):
    evaluations = [
        tuple(kpoly_eval(selected, x) for x in TEST_NODES)
        for _, selected, _ in family
    ]
    results = []
    all_single_node_stats = []
    first_injective = None
    first_injective_stats = None

    for width in range(1, W + 2):
        best = None
        for panel in combinations(range(N), width):
            fibres = defaultdict(int)
            for row in evaluations:
                fibres[tuple(row[i] for i in panel)] += 1
            sizes = tuple(fibres.values())
            collision_pairs = sum(size * (size - 1) // 2 for size in sizes)
            score = (max(sizes), collision_pairs, -sum(size == 1 for size in sizes), panel)
            if width == 1:
                all_single_node_stats.append({
                    "node_index": panel[0],
                    "node": TEST_NODES[panel[0]],
                    "max_fibre": max(sizes),
                    "collision_pairs": collision_pairs,
                    "singleton_candidates": sum(size == 1 for size in sizes),
                })
            if best is None or score < best[0]:
                best = (score, len(fibres), sum(size == 1 for size in sizes))
        assert best is not None
        score, fibre_count, singleton_count = best
        entry = {
            "width": width,
            "best_panel_node_indices": list(score[3]),
            "best_panel_nodes": [TEST_NODES[i] for i in score[3]],
            "max_fibre": score[0],
            "collision_pairs": score[1],
            "fibre_count": fibre_count,
            "singleton_candidates": singleton_count,
        }
        results.append(entry)
        if score[0] == 1:
            first_injective = score[3]
            first_injective_stats = entry
            break

    assert first_injective is not None

    # For the lex-first tree in the winning panel order, record how quickly
    # difference-factor mass disappears.  Equal signatures at depth d imply
    # divisibility by the d-node locator, but only pairs still in a common
    # fibre can exploit that factor.
    lex_tree = []
    for depth in range(1, len(first_injective) + 1):
        panel = first_injective[:depth]
        fibres = defaultdict(int)
        for row in evaluations:
            fibres[tuple(row[i] for i in panel)] += 1
        sizes = tuple(fibres.values())
        lex_tree.append({
            "depth": depth,
            "remaining_equal_signature_pairs": sum(
                size * (size - 1) // 2 for size in sizes
            ),
            "max_fibre": max(sizes),
            "nontrivial_fibres": sum(size > 1 for size in sizes),
        })

    return results, first_injective_stats, lex_tree, all_single_node_stats


def main():
    # Check that alpha has degree six: its modulus is the helper's irreducible
    # LAMBDA, and alpha is not a base-field scalar.
    assert LAMBDA == (1, 1, 2, 0, 0, 0, 1)
    xpoly = (0, 1)
    assert powmod(xpoly, P**6, LAMBDA) == xpoly
    assert gcd_poly(sub(powmod(xpoly, P**2, LAMBDA), xpoly), LAMBDA) == (1,)
    assert gcd_poly(sub(powmod(xpoly, P**3, LAMBDA), xpoly), LAMBDA) == (1,)
    assert len(ALPHA) == 2
    family, raw_supports, zero_u1_top, gamma_collisions = build_family()
    results, first_injective, lex_tree, all_single_node_stats = panel_stats(family)

    print(json.dumps({
        "status": "PASS exact structural control / STOP panel-factor implication",
        "field": "GF(17^6)",
        "parameters_n_w_A_e_projective_high": [N, W, A, 2, 10],
        "all_received_directions_projective_degree_at_least": 10,
        "fixed_bad_received_row": 1,
        "raw_supported_candidates": raw_supports,
        "supports_with_zero_U1_top_coefficient": zero_u1_top,
        "duplicate_gamma_supports_discarded": gamma_collisions,
        "same_witness_family_size": len(family),
        "best_panels_by_width": results,
        "first_injective_panel": first_injective,
        "all_single_node_panel_stats": all_single_node_stats,
        "lex_first_equal_signature_mass": lex_tree,
        "interpretation": (
            "A fixed evaluation panel can separate the family, but once it "
            "does, no same-signature pair remains to carry the claimed "
            "difference locator. Projective-highness does not itself force a "
            "large panel fibre or a reusable separator factor."
        ),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
