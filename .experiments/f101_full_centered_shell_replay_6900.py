#!/usr/bin/env python3
"""Exact all-grade centered replay of the canonical F101 Full187 corrections.

This reproduces the *same* canonical source-vector selection as
f101_grade7_correction_factor_probe_6900.py, then changes variables exactly:

  V=Y-QZ,  V1=R-Q'Z,  V2=S-Q''Z.

It is a factor/recurrence probe, not a new rank search.  The only matrix
operations replay the already-used contact-kernel and target-relation solve
needed to obtain the fixed source vectors.  Every centered shell is expanded
back to (Y,R,S,Z) and asserted equal to the source vector.
"""

from __future__ import annotations

import hashlib
import json
from collections import defaultdict
from math import comb
from pathlib import Path

from flint import nmod_mat, nmod_poly

import f101_o2_seedcap_pc_filtration_discriminator_6900 as P
import f101_o2_xi2_full_kernel_certificate_6900 as C
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F
import prime_o2_conormal_threshold_falsifier as T


PRIME = 101
MAX_GRADE = 7
Orig = tuple[int, int, int, int]  # Y,R,S,Z exponents
Centered = tuple[int, int, int, int]  # V,V1,V2,Z exponents


def poly_from_terms(terms: dict[int, int]) -> nmod_poly:
    if not terms:
        return nmod_poly([], PRIME)
    out = [0] * (max(terms) + 1)
    for degree, coefficient in terms.items():
        out[degree] = coefficient % PRIME
    return nmod_poly(out, PRIME)


def poly_is_zero(poly: nmod_poly) -> bool:
    return poly.degree() < 0


def poly_add_to(target: dict[tuple, nmod_poly], key: tuple, value: nmod_poly) -> None:
    if poly_is_zero(value):
        return
    prior = target.get(key)
    value = value if prior is None else prior + value
    if poly_is_zero(value):
        target.pop(key, None)
    else:
        target[key] = value


def factor_receipt(poly: nmod_poly) -> dict[str, object]:
    if poly_is_zero(poly):
        return {"degree": -1, "polynomial": "0", "unit": 0, "factors": ()}
    unit, factors = poly.factor()
    return {
        "degree": poly.degree(),
        "polynomial": str(poly),
        "unit": int(unit),
        "factors": tuple((str(factor), multiplicity) for factor, multiplicity in factors),
    }


def polynomial_gcd(polys: list[nmod_poly]) -> nmod_poly:
    assert polys
    out = polys[0]
    for poly in polys[1:]:
        out = out.gcd(poly)
    return out


def power(poly: nmod_poly, exponent: int) -> nmod_poly:
    out = nmod_poly([1], PRIME)
    base = poly
    while exponent:
        if exponent & 1:
            out *= base
        base *= base
        exponent //= 2
    return out


def centered_expand(
    original: dict[Orig, nmod_poly], q: nmod_poly, q1: nmod_poly, q2: nmod_poly,
) -> dict[Centered, nmod_poly]:
    """Y=V+QZ, R=V1+Q'Z, S=V2+Q''Z exactly."""
    out: dict[Centered, nmod_poly] = {}
    q_powers = [power(q, i) for i in range(MAX_GRADE + 1)]
    q1_powers = [power(q1, i) for i in range(MAX_GRADE + 1)]
    q2_powers = [power(q2, i) for i in range(MAX_GRADE + 1)]
    for (y, r, s, z), coefficient in original.items():
        for vy in range(y + 1):
            for vr in range(r + 1):
                for vs in range(s + 1):
                    moved = (y - vy) + (r - vr) + (s - vs)
                    key: Centered = (vy, vr, vs, z + moved)
                    scalar = comb(y, vy) * comb(r, vr) * comb(s, vs)
                    term = coefficient * scalar * q_powers[y - vy] * q1_powers[r - vr] * q2_powers[s - vs]
                    poly_add_to(out, key, term)
    return out


def original_expand(
    centered: dict[Centered, nmod_poly], q: nmod_poly, q1: nmod_poly, q2: nmod_poly,
) -> dict[Orig, nmod_poly]:
    """Inverse substitution V=Y-QZ, V1=R-Q'Z, V2=S-Q''Z exactly."""
    out: dict[Orig, nmod_poly] = {}
    q_powers = [power(q, i) for i in range(MAX_GRADE + 1)]
    q1_powers = [power(q1, i) for i in range(MAX_GRADE + 1)]
    q2_powers = [power(q2, i) for i in range(MAX_GRADE + 1)]
    for (v, v1, v2, z), coefficient in centered.items():
        for y in range(v + 1):
            for r in range(v1 + 1):
                for s in range(v2 + 1):
                    moved = (v - y) + (v1 - r) + (v2 - s)
                    key: Orig = (y, r, s, z + moved)
                    scalar = ((-1) ** moved) * comb(v, y) * comb(v1, r) * comb(v2, s)
                    term = coefficient * scalar * q_powers[v - y] * q1_powers[v1 - r] * q2_powers[v2 - s]
                    poly_add_to(out, key, term)
    return out


def grouped_source_vector(ordered, source_vector) -> dict[Orig, nmod_poly]:
    grouped: dict[Orig, dict[int, int]] = defaultdict(dict)
    for index, (xp, y, r, s, z) in enumerate(ordered):
        coefficient = int(source_vector[index, 0]) % PRIME
        if coefficient:
            grouped[(y, r, s, z)][xp] = coefficient
    return {shape: poly_from_terms(terms) for shape, terms in grouped.items()}


def canonical_source_vectors():
    """Verbatim canonical selection from the root grade-seven factor probe."""
    T.PRIME = F.PRIME = PRIME
    F.GAMMA = 0
    F.MULTIPLICITY = C.M
    xi, q, monomials, contact_columns = P.build_full_columns()
    locator = F.locator(C.AGREEMENT)
    xi_poly, q_poly, locator_poly = (nmod_poly(list(xi), PRIME),
                                      nmod_poly(list(q), PRIME),
                                      nmod_poly(list(locator), PRIME))
    normals = F.centered_locator_normals(locator, (0,), q)
    targets = tuple(P.normal_target(normal, 3) for normal in normals)
    indices = tuple(sorted(
        (index for index, monomial in enumerate(monomials)
         if sum(monomial[1:]) <= MAX_GRADE),
        key=lambda index: (
            sum(monomials[index][1:]), sum(monomials[index][1:4]),
            monomials[index][0], monomials[index][3], monomials[index][2],
            monomials[index][1], monomials[index][4])))
    ordered = tuple(monomials[index] for index in indices)
    contact_matrix = T.dense_matrix([contact_columns[index] for index in indices])
    kernel, nullity = contact_matrix.nullspace()
    assert (contact_matrix.rank(), nullity) == (1735, 39)
    j_rows = sorted(
        {row for monomial in ordered for row in P.exact_polynomial_normal_rows(monomial, 3)}
        | {row for target in targets for row in target}, key=repr)
    j_index = {row: index for index, row in enumerate(j_rows)}
    flat = [0] * (len(j_rows) * len(indices))
    for column, monomial in enumerate(ordered):
        for row, coefficient in P.exact_polynomial_normal_rows(monomial, 3).items():
            flat[j_index[row] * len(indices) + column] = coefficient
    image = nmod_mat(len(j_rows), len(indices), flat, PRIME) * kernel
    assert image.rank() == 12
    kernel_basis = nmod_mat(kernel.nrows(), nullity, [
        int(kernel[row, column]) for row in range(kernel.nrows())
        for column in range(nullity)], PRIME)
    vectors = {}
    for name, target in zip(("F0", "F1", "F2"), targets):
        target_column = [0] * len(j_rows)
        for row, coefficient in target.items():
            target_column[j_index[row]] = (-coefficient) % PRIME
        augmented_flat = []
        for row in range(len(j_rows)):
            augmented_flat.extend(int(image[row, column]) for column in range(nullity))
            augmented_flat.append(target_column[row])
        relations, relation_count = nmod_mat(
            len(j_rows), nullity + 1, augmented_flat, PRIME).nullspace()
        relation = next(column for column in range(relation_count)
                        if int(relations[nullity, column]) % PRIME)
        scale = pow(int(relations[nullity, relation]) % PRIME, -1, PRIME)
        coordinates = nmod_mat(nullity, 1, [
            int(relations[row, relation]) * scale % PRIME for row in range(nullity)], PRIME)
        vectors[name] = kernel_basis * coordinates
    return ordered, vectors, xi_poly, q_poly, locator_poly


def shell_summary(centered: dict[Centered, nmod_poly]) -> dict[str, object]:
    by_grade: dict[int, dict[Centered, nmod_poly]] = defaultdict(dict)
    for exponent, coefficient in centered.items():
        by_grade[sum(exponent)][exponent] = coefficient
    assert set(by_grade).issubset(set(range(MAX_GRADE + 1)))
    result = {}
    for grade in range(MAX_GRADE + 1):
        shell = by_grade.get(grade, {})
        if not shell:
            result[str(grade)] = {"terms": 0, "shapes": (), "gcd": factor_receipt(nmod_poly([], PRIME))}
            continue
        gcd = polynomial_gcd(list(shell.values()))
        mins = tuple(min(exponent[i] for exponent in shell) for i in range(4))
        result[str(grade)] = {
            "terms": len(shell),
            "shapes": tuple(sorted(shell)),
            "componentwise_monomial_gcd": mins,
            "gcd": factor_receipt(gcd),
            "coefficients": {repr(exponent): factor_receipt(coefficient)
                             for exponent, coefficient in sorted(shell.items())},
        }
    return result


def scalar_multiple(left: dict[Centered, nmod_poly], right: dict[Centered, nmod_poly]):
    """Return scalar if right=scalar*left; otherwise None.  Scalar is in F101."""
    if set(left) != set(right) or not left:
        return None
    anchor = next(iter(left))
    if left[anchor].degree() != 0 or right[anchor].degree() != 0:
        return None
    scalar = int(right[anchor][0]) * pow(int(left[anchor][0]), -1, PRIME) % PRIME
    if all(right[key] == scalar * value for key, value in left.items()):
        return scalar
    return None


def grade_piece(centered: dict[Centered, nmod_poly], grade: int) -> dict[Centered, nmod_poly]:
    return {key: value for key, value in centered.items() if sum(key) == grade}


def exact_quotient(numerator: nmod_poly, denominator: nmod_poly) -> nmod_poly:
    quotient, remainder = divmod(numerator, denominator)
    assert poly_is_zero(remainder)
    return quotient


def normal_frame_and_recurrence_receipt(
    all_centered: dict[str, dict[Centered, nmod_poly]], locator: nmod_poly, xi: nmod_poly,
) -> dict[str, object]:
    """Assert the exact grade-one normal frame and the first recurrence break.

    The frame is the literal centered form of the three prescribed locator
    normals.  Any homogeneous degree-one carrier times a frame element has
    zero pure (V,V1,V2)-tail.  The explicit nonzero Z^2 entries at grade two
    therefore rule out a one-carrier homogeneous shell recurrence already at
    its first possible step; this is a support-and-coefficient obstruction,
    not a rank claim.
    """
    l1, l2 = locator.derivative(), locator.derivative().derivative()
    expected = {
        "F0": {(1, 0, 0, 0): locator**3},
        "F1": {
            (1, 0, 0, 0): -locator**2 * l1,
            (0, 1, 0, 0): locator**3,
        },
        "F2": {
            (1, 0, 0, 0): 2 * locator * l1**2 - locator**2 * l2,
            (0, 1, 0, 0): -2 * locator**2 * l1,
            (0, 0, 1, 0): locator**3,
        },
    }
    receipt = {}
    for name, frame in expected.items():
        grade_one = grade_piece(all_centered[name], 1)
        assert grade_one == frame, name
        assert all(key[3] == 0 for key in grade_one), name
        pure_z2 = grade_piece(all_centered[name], 2).get((0, 0, 0, 2))
        assert pure_z2 is not None and not poly_is_zero(pure_z2), name
        receipt[name] = {
            "grade_one_exact": {
                repr(key): factor_receipt(value) for key, value in sorted(frame.items())
            },
            "grade_two_pure_Z2": factor_receipt(pure_z2),
            "homogeneous_linear_carrier_failure": (
                "A homogeneous linear centered carrier times this grade-one "
                "frame has zero pure Z^2 coefficient, but the displayed "
                "coefficient is nonzero."
            ),
        }
    return receipt


def grade_seven_covariant_receipt(
    all_centered: dict[str, dict[Centered, nmod_poly]], locator: nmod_poly, xi: nmod_poly,
) -> dict[str, object]:
    """Recover the terminal Wronskian packet directly from centered shells."""
    l1 = locator.derivative()
    expected_shapes = {(4, 0, 0, 3), (3, 0, 0, 4), (2, 1, 0, 4)}
    receipt = {}
    for name, centered in all_centered.items():
        shell = grade_piece(centered, 7)
        assert set(shell) == expected_shapes, name
        c = shell[(4, 0, 0, 3)]
        a = exact_quotient(shell[(2, 1, 0, 4)], xi * locator)
        cc = exact_quotient(shell[(3, 0, 0, 4)] + a * xi * l1, locator)
        assert shell[(3, 0, 0, 4)] == cc * locator - a * xi * l1
        assert shell[(2, 1, 0, 4)] == a * xi * locator
        receipt[name] = {
            "c": factor_receipt(c),
            "A": factor_receipt(a),
            "C": factor_receipt(cc),
            "identity": (
                "V^2 Z^3 (c V^2 + C Lambda V Z + A Xi "
                "(Lambda V1 - Lambda' V) Z)"
            ),
        }
    return receipt


def main() -> None:
    ordered, vectors, xi, q, locator = canonical_source_vectors()
    q1, q2 = q.derivative(), q.derivative().derivative()
    all_centered = {}
    records = {}
    for name, vector in vectors.items():
        original = grouped_source_vector(ordered, vector)
        centered = centered_expand(original, q, q1, q2)
        reconstructed = original_expand(centered, q, q1, q2)
        assert reconstructed == original, name
        assert all(sum(exponent) <= MAX_GRADE for exponent in centered)
        all_centered[name] = centered
        records[name] = {
            "original_terms": len(original),
            "centered_terms": len(centered),
            "original_sha256": hashlib.sha256(
                repr(tuple((key, str(value)) for key, value in sorted(original.items()))).encode()).hexdigest(),
            "centered_sha256": hashlib.sha256(
                repr(tuple((key, str(value)) for key, value in sorted(centered.items()))).encode()).hexdigest(),
            "reconstruction": "exact",
            "shells": shell_summary(centered),
        }

    # Exact gradewise common support and scalar-multiple checks.  This is the
    # recurrence discriminator: a nontrivial equality is reported only when
    # every centered coefficient polynomial agrees.
    comparisons = {}
    for grade in range(MAX_GRADE + 1):
        pieces = {
            name: {key: value for key, value in centered.items() if sum(key) == grade}
            for name, centered in all_centered.items()
        }
        common = set.intersection(*(set(piece) for piece in pieces.values()))
        comparisons[str(grade)] = {
            "common_shapes": tuple(sorted(common)),
            "F1_is_scalar_F0": scalar_multiple(pieces["F0"], pieces["F1"]),
            "F2_is_scalar_F0": scalar_multiple(pieces["F0"], pieces["F2"]),
        }

    # The first and last nonzero shells are both exact covariant packets.
    # The grade-two pure-tail term is an exact obstruction to joining those
    # packets by a homogeneous one-carrier grade recurrence.
    frame_and_break = normal_frame_and_recurrence_receipt(all_centered, locator, xi)
    grade7_covariant = grade_seven_covariant_receipt(all_centered, locator, xi)

    payload = {
        "scope": "exact canonical F101 all-grade centered-shell replay; no target-scale claim",
        "field": PRIME,
        "parameters_n_w_A_m_D_s_t_J_L": C.CASE,
        "centered_change": {
            "V": "Y-QZ", "V1": "R-Q'Z", "V2": "S-Q''Z",
            "Q": str(q), "Q1": str(q1), "Q2": str(q2),
            "Lambda": str(locator), "Xi": str(xi),
        },
        "canonical_source_ordered_columns": len(ordered),
        "grade_one_normal_frame_and_first_recurrence_break": frame_and_break,
        "grade_seven_covariant_packet": grade7_covariant,
        "corrections": records,
        "gradewise_comparisons": comparisons,
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
