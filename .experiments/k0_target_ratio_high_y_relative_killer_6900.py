#!/usr/bin/env python3
"""Focused high-Y relative-killer test in the target-ratio controls.

For the exact and ceiling profiles exported by
``k0_target_ratio_constant_t_gate_6900.py``, construct every legal size-six
constant-T partial-locator packet, reduce their raw polynomial span exactly,
and adjoin consecutive raw bands

    X^j Y^(U-B) Z^z,  0 <= z <= q.

The exponent ``U-B`` (not ``m+1``) is the feature shared with the target
pair ``Y^48`` because target ``U-B=64-16=48``.  This is one deterministic
mechanism test, not a parameter search.
"""

from __future__ import annotations

from collections import defaultdict
import hashlib
from itertools import combinations
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat

sys.path.insert(0, ".experiments")
from higher_jet_literal_matrix import translated_column  # noqa: E402
import k0_target_ratio_constant_t_gate_6900 as Gate  # noqa: E402


P = Gate.P
K0 = Gate.K0
Mon = tuple[int, int, int, int, int]
Poly = dict[Mon, int]
ZERO: Mon = (0, 0, 0, 0, 0)


def normalize(poly: Poly) -> Poly:
    return {mon: coefficient % P for mon, coefficient in poly.items()
            if coefficient % P}


def add(left: Poly, right: Poly) -> Poly:
    answer = dict(left)
    for monomial, coefficient in right.items():
        answer[monomial] = (answer.get(monomial, 0) + coefficient) % P
    return normalize(answer)


def scale(coefficient: int, poly: Poly) -> Poly:
    return normalize({monomial: coefficient * value
                      for monomial, value in poly.items()})


def mul(left: Poly, right: Poly) -> Poly:
    answer: Poly = {}
    for lm, lc in left.items():
        for rm, rc in right.items():
            monomial = tuple(a + b for a, b in zip(lm, rm))
            answer[monomial] = (answer.get(monomial, 0) + lc * rc) % P
    return normalize(answer)


def power(poly: Poly, exponent: int) -> Poly:
    answer = {ZERO: 1}
    base = poly
    while exponent:
        if exponent & 1:
            answer = mul(answer, base)
        exponent //= 2
        if exponent:
            base = mul(base, base)
    return answer


def derivative(poly: Poly) -> Poly:
    return normalize({(xp - 1, yp, rp, sp, zp): xp * coefficient
                      for (xp, yp, rp, sp, zp), coefficient in poly.items()
                      if xp})


def xpoly(coefficients: tuple[int, ...]) -> Poly:
    return normalize({(degree, 0, 0, 0, 0): coefficient
                      for degree, coefficient in enumerate(coefficients)})


def locator(nodes: tuple[int, ...]) -> Poly:
    answer = {ZERO: 1}
    for node in nodes:
        answer = mul(answer, {ZERO: -node, (1, 0, 0, 0, 0): 1})
    return answer


Y = {(0, 1, 0, 0, 0): 1}
R = {(0, 0, 1, 0, 0): 1}
S = {(0, 0, 0, 1, 0): 1}
Z = {(0, 0, 0, 0, 1): 1}


def anchor_packet(profile: K0.Profile, anchor: tuple[int, ...]) -> tuple[Poly, ...]:
    agreement = tuple(range(profile.agreements))
    complement = tuple(node for node in agreement if node not in anchor)
    h = locator(anchor)
    outside = locator(complement)
    q = xpoly(Gate.constant_t_polynomial())
    c = Gate.constant_t_polynomial()[-1]
    qh = add(q, scale(-c, h))
    assert add(q, scale(-1, qh)) == scale(c, h)

    a0 = add(Y, scale(-1, mul(Z, qh)))
    rh = add(R, scale(-1, mul(Z, derivative(qh))))
    sh = add(S, scale(-1, mul(Z, derivative(derivative(qh)))))
    hp = derivative(h)
    hpp = derivative(hp)
    a1 = add(mul(h, rh), scale(-1, mul(hp, a0)))
    a2 = add(
        add(mul(power(h, 2), sh), scale(-2, mul(mul(h, hp), rh))),
        mul(add(scale(2, power(hp, 2)), scale(-1, mul(h, hpp))), a0),
    )
    answer = []
    for sp in range(profile.s + 1):
        for rp in range(profile.B - 2 * sp + 1):
            for ip in range(profile.m - 2 * rp - 3 * sp + 1):
                depth = ip + 2 * rp + 3 * sp
                if depth == 0 or ip + rp + sp > profile.U:
                    continue
                core = mul(
                    mul(power(h, profile.m - depth), power(outside, profile.m)),
                    mul(power(a0, ip), mul(power(a1, rp), power(a2, sp))),
                )
                for zp in range(profile.L - (ip + rp + sp) + 1):
                    seeded = mul(core, power(Z, zp))
                    for xp in range(depth):
                        answer.append(mul({(xp, 0, 0, 0, 0): 1}, seeded))
    return tuple(answer)


def polynomial_span_basis(polynomials, monomial_index: dict[Mon, int]) -> tuple[Poly, ...]:
    """Sparse exact echelon basis of the packet's raw polynomial span."""
    pivots: dict[int, dict[int, int]] = {}
    answer = []
    for poly in polynomials:
        vector = {monomial_index[mon]: coefficient % P
                  for mon, coefficient in poly.items() if coefficient % P}
        while vector:
            pivot = min(vector)
            if pivot not in pivots:
                inverse = pow(vector[pivot], -1, P)
                vector = {i: coefficient * inverse % P
                          for i, coefficient in vector.items()
                          if coefficient * inverse % P}
                pivots[pivot] = vector
                answer.append({mon: vector[i]
                               for mon, i in monomial_index.items() if i in vector})
                break
            coefficient = vector[pivot]
            for i, value in pivots[pivot].items():
                new_value = (vector.get(i, 0) - coefficient * value) % P
                if new_value:
                    vector[i] = new_value
                else:
                    vector.pop(i, None)
    return tuple(answer)


def expand_contact(poly: Poly, profile: K0.Profile, receipt: K0.Receipt,
                   cache: dict[Mon, dict[object, int]]) -> dict[object, int]:
    answer: dict[object, int] = {}
    for monomial, coefficient in poly.items():
        if monomial not in cache:
            xp, yp, rp, sp, zp = monomial
            raw = {}
            for node in receipt.nodes:
                expansion = translated_column(
                    xp, (yp, rp, sp), zp, node,
                    receipt.u0[node], receipt.u1[node], profile.m, 2, P)
                for term, value in expansion.items():
                    if value:
                        raw[(node, term)] = value
            cache[monomial] = raw
        for row, value in cache[monomial].items():
            answer[row] = (answer.get(row, 0) + coefficient * value) % P
    return {row: value for row, value in answer.items() if value}


def expand_boundary(poly: Poly, x: int) -> tuple[int, int, int, int]:
    answer = [0, 0, 0, 0]
    for (xp, yp, rp, sp, zp), coefficient in poly.items():
        active = (yp, rp, sp, zp)
        if sum(active) == 1:
            coordinate = active.index(1)
            answer[coordinate] = (answer[coordinate]
                                  + coefficient * pow(x, xp, P)) % P
    return tuple(answer)


def dense(sparse_columns, rows) -> nmod_mat:
    return nmod_mat(
        len(rows), len(sparse_columns),
        [sparse_columns[j].get(row, 0)
         for row in rows for j in range(len(sparse_columns))], P)


def boundary_matrix(columns, x: int) -> nmod_mat:
    values = tuple(expand_boundary(poly, x) for poly in columns)
    return nmod_mat(4, len(columns),
                    [values[j][i] for i in range(4)
                     for j in range(len(columns))], P)


def stack(top: nmod_mat, bottom: nmod_mat) -> nmod_mat:
    return nmod_mat(
        top.nrows() + bottom.nrows(), top.ncols(),
        [int(top[i, j]) for i in range(top.nrows()) for j in range(top.ncols())]
        + [int(bottom[i, j])
           for i in range(bottom.nrows()) for j in range(bottom.ncols())], P)


def run(profile: K0.Profile) -> dict[str, object]:
    receipt = Gate.constant_t_receipt(profile)
    monomials = K0.support(profile)
    monomial_index = {monomial: i for i, monomial in enumerate(monomials)}
    packet_polynomials = tuple(
        poly
        for anchor in combinations(tuple(range(profile.agreements)), profile.w + 1)
        for poly in anchor_packet(profile, anchor)
    )
    for poly in packet_polynomials:
        assert all(mon in monomial_index for mon in poly)
    packet = polynomial_span_basis(packet_polynomials, monomial_index)

    active = profile.U - profile.B
    zmax = profile.L - active
    assert (active, zmax) == (6, 2)
    bands = tuple(tuple(
        {monomial: 1} for monomial in monomials
        if monomial[1:] == (active, 0, 0, z))
        for z in range(zmax + 1))

    cache: dict[Mon, dict[object, int]] = {}
    all_columns = packet + tuple(poly for band in bands for poly in band)
    sparse = tuple(expand_contact(poly, profile, receipt, cache)
                   for poly in all_columns)
    rows = tuple(sorted(set().union(*(set(column) for column in sparse)), key=repr))
    contact = dense(sparse, rows)
    boundary_x = profile.n
    boundary = boundary_matrix(all_columns, boundary_x)

    packet_count = len(packet)
    c0 = nmod_mat(contact.nrows(), packet_count,
                  [int(contact[i, j]) for i in range(contact.nrows())
                   for j in range(packet_count)], P)
    b0 = nmod_mat(4, packet_count,
                  [int(boundary[i, j]) for i in range(4)
                   for j in range(packet_count)], P)
    base_contact_rank = c0.rank()
    base_augmented_rank = stack(c0, b0).rank()

    cases = []
    offset = packet_count
    for q in range(zmax + 1):
        count = sum(len(bands[z]) for z in range(q + 1))
        total = offset + count
        cm = nmod_mat(contact.nrows(), total,
                      [int(contact[i, j]) for i in range(contact.nrows())
                       for j in range(total)], P)
        bm = nmod_mat(4, total,
                      [int(boundary[i, j]) for i in range(4)
                       for j in range(total)], P)
        contact_rank = cm.rank()
        augmented_rank = stack(cm, bm).rank()
        family_sparse = sparse[offset:total]
        error_rows = tuple(row for row in rows if row[0] >= profile.agreements)
        agreement_rows = tuple(row for row in rows if row[0] < profile.agreements)
        family_all = dense(family_sparse, rows)
        family_error = dense(family_sparse, error_rows)
        family_agreement = dense(family_sparse, agreement_rows)
        cases.append({
            "z_range": (0, q),
            "raw_band_columns": count,
            "packet_plus_family_contact_augmented_gain": (
                contact_rank, augmented_rank, augmented_rank - contact_rank),
            "increment_mod_packet_contact_augmented": (
                contact_rank - base_contact_rank,
                augmented_rank - base_augmented_rank),
            "family_rank_all_agreement_error": (
                family_all.rank(), family_agreement.rank(), family_error.rank()),
            "family_nullity_all": count - family_all.rank(),
            "family_boundary_is_zero": not any(int(boundary[i, j])
                for i in range(4) for j in range(offset, total)),
        })

    return {
        "profile_n_w_g_m_B_s_U_L_k_n0": tuple(profile.__dict__.values()),
        "raw_packet_columns_before_span_reduction": len(packet_polynomials),
        "packet_polynomial_span_dimension": packet_count,
        "packet_contact_augmented_gain": (
            base_contact_rank, base_augmented_rank,
            base_augmented_rank - base_contact_rank),
        "high_Y_exponent_U_minus_B": active,
        "band_widths_by_Z": tuple(len(band) for band in bands),
        "cases": tuple(cases),
    }


def main() -> None:
    started = time.monotonic()
    results = (run(Gate.EXACT), run(Gate.CEILING))
    assert tuple(case["packet_contact_augmented_gain"] for case in results) == (
        (713, 714, 1), (979, 980, 1))
    assert tuple(tuple(
        row["increment_mod_packet_contact_augmented"] for row in case["cases"])
        for case in results) == (
            ((10, 10), (20, 20), (30, 30)),
            ((12, 12), (24, 24), (36, 36)),
        )
    assert all(row["family_boundary_is_zero"]
               for case in results for row in case["cases"])
    assert all(row["family_nullity_all"] == 0
               for case in results for row in case["cases"])
    payload = {
        "scope": (
            "two deterministic target-ratio constant-T controls; exact all-"
            "anchor packet plus U-B high-Y consecutive-Z family"
        ),
        "field": "F_101",
        "verdict": (
            "RED: the U-B high-Y family is globally injective and kills no "
            "packet conormal in either target-ratio control; moreover the "
            "all-anchor packet has gain one, not a residual line"
        ),
        "cases": results,
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    payload["runtime"] = {
        "seconds": round(time.monotonic() - started, 3),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
