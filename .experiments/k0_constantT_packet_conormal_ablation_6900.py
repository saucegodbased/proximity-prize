#!/usr/bin/env python3
"""Exact constant-T ablation for the legal k=0 partial-carrier packet.

This is a single adversarial experiment, not a parameter scan.  It uses the
smallest target-gated two-Newton/two-error chamber

    (n,w,g,m,B,s,U,L,k,n0) = (7,2,5,4,2,1,7,7,0,1)

over F_11 and the constant-T family Q=C(X,3), epsilon=delta=1 at both
errors.  Thus every size-three anchor has Q-q_H=c*Lambda_H and all scalar
passive traces of the partial-carrier packet collapse to an m-dimensional
X-frame.

Unlike the scalar quotient, this script expands the actual legal carriers in
the raw (X,Y,R,S,Z) source and imposes every literal order-two contact row.
It compares a0-only, slope-companion, full second-osculating, adjacent-anchor,
and complete-source conormal ranks.  The purpose is to identify which
information discarded by the scalar quotient can actually rescue four
boundary directions.
"""

from __future__ import annotations

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
import secondjet_candidate_major_function_field_rank_gate_6900 as K0  # noqa: E402


PRIME = 11
PROFILE = K0.Profile(7, 2, 5, 4, 2, 1, 7, 7, 0, 1)
NODES = tuple(range(7))
AGREEMENT = tuple(range(5))
ERRORS = (5, 6)
BOUNDARY_X = 7
MONOMIALS = K0.support(PROFILE)
MONOMIAL_INDEX = {monomial: i for i, monomial in enumerate(MONOMIALS)}

# Sparse polynomials in (X,Y,R,S,Z).
Mon = tuple[int, int, int, int, int]
Poly = dict[Mon, int]
ZERO_MON: Mon = (0, 0, 0, 0, 0)


def normalize(poly: Poly) -> Poly:
    return {mon: coefficient % PRIME for mon, coefficient in poly.items()
            if coefficient % PRIME}


def add(left: Poly, right: Poly) -> Poly:
    answer = dict(left)
    for monomial, coefficient in right.items():
        answer[monomial] = (answer.get(monomial, 0) + coefficient) % PRIME
    return normalize(answer)


def scale(coefficient: int, poly: Poly) -> Poly:
    return normalize({monomial: coefficient * value
                      for monomial, value in poly.items()})


def mul(left: Poly, right: Poly) -> Poly:
    answer: Poly = {}
    for lm, lc in left.items():
        for rm, rc in right.items():
            monomial = tuple(a + b for a, b in zip(lm, rm))
            answer[monomial] = (answer.get(monomial, 0) + lc * rc) % PRIME
    return normalize(answer)


def power(poly: Poly, exponent: int) -> Poly:
    answer = {ZERO_MON: 1}
    base = poly
    while exponent:
        if exponent & 1:
            answer = mul(answer, base)
        exponent //= 2
        if exponent:
            base = mul(base, base)
    return answer


def xpoly(coefficients: tuple[int, ...]) -> Poly:
    return normalize({(degree, 0, 0, 0, 0): coefficient
                      for degree, coefficient in enumerate(coefficients)})


def derivative(poly: Poly) -> Poly:
    answer: Poly = {}
    for (xp, yp, rp, sp, zp), coefficient in poly.items():
        if xp:
            answer[(xp - 1, yp, rp, sp, zp)] = xp * coefficient % PRIME
    return normalize(answer)


def linear_factor(root: int) -> Poly:
    return xpoly((-root, 1))


def locator(nodes: tuple[int, ...]) -> Poly:
    answer = {ZERO_MON: 1}
    for node in nodes:
        answer = mul(answer, linear_factor(node))
    return answer


X = {(1, 0, 0, 0, 0): 1}
Y = {(0, 1, 0, 0, 0): 1}
RVAR = {(0, 0, 1, 0, 0): 1}
SVAR = {(0, 0, 0, 1, 0): 1}
Z = {(0, 0, 0, 0, 1): 1}


# Q=C(X,3)=X(X-1)(X-2)/6 over F_11; its leading coefficient is 2.
Q = scale(pow(6, -1, PRIME), locator((0, 1, 2)))
QPRIME = derivative(Q)
QSECOND = derivative(QPRIME)


def anchor_packet(anchor: tuple[int, ...], companion_level: int):
    """Return expanded legal carriers for one anchor.

    ``companion_level`` is 0 for a0 only, 1 to admit a1, and 2 to admit a2.
    Every returned polynomial is asserted to lie termwise in the exact source.
    """
    assert len(anchor) == PROFILE.w + 1
    complement = tuple(node for node in AGREEMENT if node not in anchor)
    h = locator(anchor)
    outside = locator(complement)
    # For degree-(w+1) Q, q_H=Q-cH and T_H=c for every anchor.
    qh = add(Q, scale(-2, h))
    assert derivative(add(Q, scale(-1, qh))) == derivative(scale(2, h))

    a0 = add(Y, scale(-1, mul(Z, qh)))
    rh = add(RVAR, scale(-1, mul(Z, derivative(qh))))
    sh = add(SVAR, scale(-1, mul(Z, derivative(derivative(qh)))))
    hp = derivative(h)
    hpp = derivative(hp)
    a1 = add(mul(h, rh), scale(-1, mul(hp, a0)))
    a2 = add(
        add(mul(power(h, 2), sh), scale(-2, mul(mul(h, hp), rh))),
        mul(add(scale(2, power(hp, 2)), scale(-1, mul(h, hpp))), a0),
    )

    answer = []
    for sp in range(PROFILE.s + 1):
        if sp and companion_level < 2:
            continue
        for rp in range(PROFILE.B - 2 * sp + 1):
            if rp and companion_level < 1:
                continue
            for ip in range(PROFILE.m - 2 * rp - 3 * sp + 1):
                depth = ip + 2 * rp + 3 * sp
                if depth == 0 or ip + rp + sp > PROFILE.U:
                    continue
                core = mul(
                    mul(power(h, PROFILE.m - depth), power(outside, PROFILE.m)),
                    mul(power(a0, ip), mul(power(a1, rp), power(a2, sp))),
                )
                for zp in range(PROFILE.L - (ip + rp + sp) + 1):
                    seeded = mul(core, power(Z, zp))
                    for xp in range(depth):
                        carrier = mul(power(X, xp), seeded)
                        missing = tuple(mon for mon in carrier
                                        if mon not in MONOMIAL_INDEX)
                        assert not missing, (anchor, ip, rp, sp, xp, zp, missing[:3])
                        answer.append(carrier)
    return tuple(answer)


def raw_contact_columns():
    # Candidate P=0,gamma=0.  Agreements have (u0,u1)=(0,Q); errors have
    # delta=epsilon=1, hence common passive ratio rho=-1.
    qvalues = (0, 0, 0, 1, 4, 10, 20)
    u0 = (0, 0, 0, 0, 0, 1, 1)
    u1 = tuple((value + (node in ERRORS)) % PRIME
               for node, value in enumerate(qvalues))
    answer = []
    for xp, yp, rp, sp, zp in MONOMIALS:
        column = {}
        for node in NODES:
            expansion = translated_column(
                xp, (yp, rp, sp), zp, node, u0[node], u1[node],
                PROFILE.m, 2, PRIME,
            )
            for term, value in expansion.items():
                if value:
                    column[(node, term)] = value
        answer.append(column)
    return tuple(answer)


RAW_CONTACT = raw_contact_columns()


def raw_boundary_column(monomial: Mon):
    xp, yp, rp, sp, zp = monomial
    active = (yp, rp, sp, zp)
    if sum(active) != 1:
        return (0, 0, 0, 0)
    return tuple(pow(BOUNDARY_X, xp, PRIME) if active[i] else 0
                 for i in range(4))


RAW_BOUNDARY = tuple(raw_boundary_column(monomial) for monomial in MONOMIALS)


def expand_contact(poly: Poly):
    answer = {}
    for monomial, coefficient in poly.items():
        raw = RAW_CONTACT[MONOMIAL_INDEX[monomial]]
        for row, value in raw.items():
            answer[row] = (answer.get(row, 0) + coefficient * value) % PRIME
    return {row: value for row, value in answer.items() if value}


def expand_boundary(poly: Poly):
    answer = [0, 0, 0, 0]
    for monomial, coefficient in poly.items():
        raw = RAW_BOUNDARY[MONOMIAL_INDEX[monomial]]
        for coordinate, value in enumerate(raw):
            answer[coordinate] = (answer[coordinate] + coefficient * value) % PRIME
    return tuple(answer)


def dense_contact(columns, rows):
    return nmod_mat(
        len(rows), len(columns),
        [columns[column].get(row, 0)
         for row in rows for column in range(len(columns))],
        PRIME,
    )


def dense_boundary(columns):
    return nmod_mat(
        4, len(columns),
        [columns[column][coordinate]
         for coordinate in range(4) for column in range(len(columns))],
        PRIME,
    )


def stack(top, bottom):
    return nmod_mat(
        top.nrows() + bottom.nrows(), top.ncols(),
        [int(top[i, j])
         for i in range(top.nrows()) for j in range(top.ncols())]
        + [int(bottom[i, j])
           for i in range(bottom.nrows()) for j in range(bottom.ncols())],
        PRIME,
    )


def conormal_receipt(label: str, polynomials, extract_compatible: bool = False):
    contact_columns = tuple(expand_contact(poly) for poly in polynomials)
    boundary_columns = tuple(expand_boundary(poly) for poly in polynomials)
    rows = tuple(sorted(set().union(*(set(column) for column in contact_columns)),
                        key=repr))
    contact = dense_contact(contact_columns, rows)
    boundary = dense_boundary(boundary_columns)
    contact_rank = contact.rank()
    gains = []
    for coordinate in range(4):
        row = nmod_mat(1, len(polynomials),
                       [boundary_columns[j][coordinate]
                        for j in range(len(polynomials))], PRIME)
        gains.append(stack(contact, row).rank() - contact_rank)
    augmented = stack(contact, boundary)
    augmented_rank = augmented.rank()
    compatible = None
    if extract_compatible:
        relations, nullity = augmented.transpose().nullspace()
        projected = nmod_mat(
            4, nullity,
            [int(relations[contact.nrows() + coordinate, relation])
             for coordinate in range(4) for relation in range(nullity)],
            PRIME,
        )
        basis = []
        for relation in range(nullity):
            vector = tuple(int(projected[coordinate, relation])
                           for coordinate in range(4))
            if any(vector):
                basis.append(vector)
        compatible = {
            "dimension": projected.rank(),
            "raw_nonzero_nullspace_projections": tuple(basis),
        }
    receipt = {
        "source": label,
        "columns": len(polynomials),
        "contact_rows": len(rows),
        "contact_rank": contact_rank,
        "kernel_dimension": len(polynomials) - contact_rank,
        "individual_boundary_gains_Y_R_S_Z": tuple(gains),
        "four_boundary_gain": augmented_rank - contact_rank,
    }
    if compatible is not None:
        receipt["compatible_boundary_covectors"] = compatible
    return receipt


def main():
    started = time.monotonic()
    a012 = anchor_packet((0, 1, 2), 0)
    r012 = anchor_packet((0, 1, 2), 1)
    s012 = anchor_packet((0, 1, 2), 2)
    s013 = anchor_packet((0, 1, 3), 2)
    s014 = anchor_packet((0, 1, 4), 2)
    all_anchor_packets = tuple(
        polynomial
        for anchor in combinations(AGREEMENT, PROFILE.w + 1)
        for polynomial in anchor_packet(anchor, 2)
    )
    # The full source is represented by its raw monomial basis.
    raw_source = tuple({monomial: 1} for monomial in MONOMIALS)
    cases = (
        conormal_receipt("anchor012_a0_only", a012),
        conormal_receipt("anchor012_a0_a1", r012),
        conormal_receipt("anchor012_a0_a1_a2", s012),
        conormal_receipt("anchors012_013_full_packet", s012 + s013),
        conormal_receipt("anchors012_013_014_full_packet", s012 + s013 + s014),
        conormal_receipt("all_ten_anchors_full_packet", all_anchor_packets, True),
        conormal_receipt("complete_relaxed_source", raw_source),
    )
    assert tuple((case["columns"], case["contact_rank"],
                  case["four_boundary_gain"]) for case in cases) == (
        (50, 50, 0),
        (126, 126, 0),
        (171, 171, 0),
        (342, 272, 1),
        (513, 297, 3),
        (1710, 297, 3),
        (1728, 1280, 4),
    )
    assert cases[-2]["compatible_boundary_covectors"] == {
        "dimension": 1,
        "raw_nonzero_nullspace_projections": ((1, 8, 2, 1),),
    }
    payload = {
        "scope": "one exact constant-T/equal-ratio adversary; no grid",
        "field": "F_11",
        "profile_n_w_g_m_B_s_U_L_k_n0": (
            PROFILE.n, PROFILE.w, PROFILE.agreements, PROFILE.m,
            PROFILE.B, PROFILE.s, PROFILE.U, PROFILE.L,
            PROFILE.k, PROFILE.n0,
        ),
        "agreement_Q": "C(X,3), degree w+1; T_H=1/6 for every anchor",
        "errors_delta_epsilon_rho": ((1, 1, -1), (1, 1, -1)),
        "boundary_X": BOUNDARY_X,
        "cases": cases,
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    payload["runtime_receipt"] = {
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
