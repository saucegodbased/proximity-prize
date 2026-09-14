#!/usr/bin/env python3
"""Inspect the first nonvacuous target-closing shell at m=5 and m=6.

The grade<=J source misses each of F0,F1,F2 by one dimension in the fixed
n=10 arbitrary-direction chamber, while the complete grade J+1 source does
close them.  This script extracts canonical contact-kernel lifts, isolates
their grade J+1 pieces, and rewrites those pieces in centered coordinates

  V0 = Y-QZ, V1 = R-Q'Z, V2 = S-Q''Z.

The output is a structural discovery receipt, not a target theorem.
"""

from __future__ import annotations

from collections import defaultdict
from math import comb
import hashlib
import json
from pathlib import Path
import sys

from flint import nmod_poly

sys.path.insert(0, ".experiments")
import f101_n10_grade7_centered_wronskian_universality_6900 as U  # noqa: E402
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402


P = 101
OFFSETS = (3, 5, 7)


def poly_from_terms(terms):
    if not terms:
        return nmod_poly([], P)
    coefficients = [0] * (max(terms) + 1)
    for exponent, coefficient in terms.items():
        coefficients[exponent] = coefficient % P
    return nmod_poly(coefficients, P)


def raw_top_grouped(literal, indices, vector, grade):
    grouped = defaultdict(dict)
    for row, source_index in enumerate(indices):
        coefficient = int(vector[row, 0]) % P
        if not coefficient:
            continue
        x, y, r, s, z = literal.monomials[source_index]
        if y + r + s + z == grade:
            grouped[(y, r, s, z)][x] = coefficient
    return {shape: poly_from_terms(terms) for shape, terms in grouped.items()}


def centered_expansion(literal, raw):
    q = nmod_poly(list(literal.q), P)
    q1 = q.derivative()
    q2 = q1.derivative()
    centered = defaultdict(lambda: nmod_poly([], P))
    for (y, r, s, z), coefficient in raw.items():
        for vy in range(y + 1):
            for vr in range(r + 1):
                for vs in range(s + 1):
                    extra_z = (y - vy) + (r - vr) + (s - vs)
                    scale = (coefficient * comb(y, vy) * comb(r, vr)
                             * comb(s, vs) * q ** (y - vy)
                             * q1 ** (r - vr) * q2 ** (s - vs))
                    centered[(vy, vr, vs, z + extra_z)] += scale
    return {shape: poly for shape, poly in centered.items() if poly != 0}


def polynomial_receipt(poly, xi, locator):
    xi_order = 0
    remainder = poly
    while remainder and divmod(remainder, xi)[1] == 0:
        remainder = divmod(remainder, xi)[0]
        xi_order += 1
    locator_order = 0
    remainder_locator = poly
    while remainder_locator and divmod(remainder_locator, locator)[1] == 0:
        remainder_locator = divmod(remainder_locator, locator)[0]
        locator_order += 1
    return {
        "degree": poly.degree(),
        "support": sum(1 for index in range(poly.degree() + 1)
                       if int(poly[index]) % P),
        "xi_divisibility": xi_order,
        "locator_divisibility": locator_order,
        "sha256": hashlib.sha256(str(poly).encode()).hexdigest(),
    }


def one_multiplicity(m):
    case = (10, 4, 7, m, 7 * m, 1, 1, m + 2, m + 6)
    literal = M.build_case(
        f"next_shell_m{m}", case, 7, 7, 3,
        error_direction_offsets=OFFSETS)
    indices, contact, nullity, image, lifts = U.solve_restricted(literal)
    grade = case[7] + 1
    xi = nmod_poly(list(literal.xi), P)
    locator = nmod_poly(list(literal.locator), P)
    rows = []
    centered_forms = []
    for name, vector in lifts:
        raw = raw_top_grouped(literal, indices, vector, grade)
        centered = centered_expansion(literal, raw)
        centered_forms.append(centered)
        rows.append({
            "normal": name,
            "raw_shape_count": len(raw),
            "raw_term_count": sum(
                sum(1 for index in range(poly.degree() + 1)
                    if int(poly[index]) % P)
                for poly in raw.values()),
            "centered_shape_count": len(centered),
            "centered_shapes": tuple(
                (shape, polynomial_receipt(poly, xi, locator))
                for shape, poly in sorted(centered.items())),
            "centered_source_sha256": hashlib.sha256(repr(tuple(
                (shape, str(poly)) for shape, poly in sorted(centered.items())
            )).encode()).hexdigest(),
        })

    # Record whether all three canonical top pieces are proportional.  This
    # was true at m=4 and is a useful discriminator at the next shell.
    pivot_shape = next(iter(centered_forms[0]))
    pivot_poly = centered_forms[0][pivot_shape]
    proportional = []
    for centered in centered_forms:
        if set(centered) != set(centered_forms[0]):
            proportional.append(None)
            continue
        candidate = centered[pivot_shape]
        scale = None
        for index in range(max(pivot_poly.degree(), candidate.degree()) + 1):
            left = int(pivot_poly[index]) % P
            right = int(candidate[index]) % P
            if left:
                scale = right * pow(left, -1, P) % P
                break
            if right:
                scale = -1
                break
        if scale is None:
            scale = 0
        if scale >= 0 and all(centered[shape] == scale * poly
                              for shape, poly in centered_forms[0].items()):
            proportional.append(scale)
        else:
            proportional.append(None)

    return {
        "parameters_n_w_g_m_D_s_t_J_L": case,
        "restricted_columns": len(indices),
        "contact_rank_nullity": (contact.rank(), nullity),
        "target_image_rank": image.rank(),
        "top_grade": grade,
        "canonical_top_pieces_proportional_scales": tuple(proportional),
        "rhs": tuple(rows),
    }


def main():
    M.PRIME = M.T.PRIME = M.F.PRIME = F.PRIME = U.PRIME = P
    multiplicities = tuple(int(value) for value in sys.argv[1:]) or (5, 6)
    payload = {
        "scope": (
            "canonical first-closing-shell structure in the fixed n10 "
            "offset chamber; finite F101 discovery evidence only"
        ),
        "field": P,
        "offsets": OFFSETS,
        "results": tuple(one_multiplicity(m) for m in multiplicities),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(
        canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
