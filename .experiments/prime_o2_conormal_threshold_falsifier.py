#!/usr/bin/env python3
"""Exact small-prime falsifier for a universal O2 conormal-rank premise.

For each printed parameter row and deterministic trial, construct a random
received affine line and a degree-w candidate with exactly A prescribed
agreements.  Build the complete global order-two contact kernel, check every
kernel row on the candidate's genuine jet graph, and measure its conormal
rank at two off-domain points.

The scan straddles the elementary 3-minor residual

    r3 = 3 * ((A-w) - (m*A-D)).

It asks two separate questions: whether positive universal source margin and
r3>0 empirically force rank three, and whether rank falls at r3<=0.  This is
a finite-field conjecture/falsifier oracle, not a target theorem.
"""

from __future__ import annotations

import hashlib
import json
import random
import sys

from flint import nmod_mat


sys.path.insert(0, ".experiments")
from higher_jet_literal_matrix import translated_column  # noqa: E402
import asymmetric_second_jet_6900 as F  # noqa: E402


PRIME = 101
TRIALS = 6

# (n,w,A,m,D,s,t,M,L).  The first four rows isolate source-box richness
# at the extremal positive residual r3=3.  The fifth shows the m=2
# degeneration, the sixth has large residual slack, and the final row is
# exactly on the residual-zero threshold.
CASES = (
    (5, 2, 4, 3, 11, 1, 1, 3, 4),
    (5, 2, 4, 3, 11, 1, 1, 4, 4),
    (5, 2, 4, 3, 11, 2, 1, 3, 3),
    (5, 2, 4, 3, 11, 2, 2, 2, 3),
    (6, 2, 5, 2, 8, 1, 1, 3, 6),
    (11, 2, 10, 2, 19, 1, 1, 1, 1),
    (5, 2, 4, 3, 10, 1, 1, 4, 7),
)


def support(w, D, s, t, M, L):
    answer = []
    for second in range(t + 1):
        for first in range(s - second + 1):
            for value in range(M - first - second + 1):
                width = D - w*value - (w-1)*first - (w-2)*second
                for seed in range(L - value - first - second + 1):
                    for xpower in range(max(0, width)):
                        answer.append((xpower, value, first, second, seed))
    return tuple(answer)


def evaluate(coefficients, x, order=0):
    answer = 0
    for exponent, coefficient in enumerate(coefficients):
        if exponent < order:
            continue
        falling = 1
        for j in range(order):
            falling = falling * (exponent-j) % PRIME
        answer += coefficient * falling * pow(x, exponent-order, PRIME)
    return answer % PRIME


def interpolate(values, nodes):
    answer = [0] * len(nodes)
    for value, node in zip(values, nodes):
        basis = [1]
        denominator = 1
        for other in nodes:
            if other == node:
                continue
            new = [0] * (len(basis)+1)
            for i, coefficient in enumerate(basis):
                new[i] = (new[i] - other*coefficient) % PRIME
                new[i+1] = (new[i+1] + coefficient) % PRIME
            basis = new
            denominator = denominator * (node-other) % PRIME
        scale = value * pow(denominator, -1, PRIME) % PRIME
        for i, coefficient in enumerate(basis):
            answer[i] = (answer[i] + scale*coefficient) % PRIME
    return tuple(answer)


def source_arithmetic(case):
    n, w, A, m, D, s, t, M, L = case
    columns = local_rank = 0
    for degree in range(M+1):
        multiplicity = L-degree+1
        q = min(degree, s)
        width = D-w*degree
        columns += multiplicity * (
            F.derivative_count(q, t)*width + F.derivative_moment(q, t))
        local_rank += multiplicity * F.local_rank_layer(m, degree, s, t)
    return {
        "columns": columns,
        "one_node_rank": local_rank,
        "universal_margin": columns-n*local_rank,
        "penalty_mA_minus_D": m*A-D,
        "gap_A_minus_w": A-w,
        "pure_YRS_3minor_residual": 3*((A-w)-(m*A-D)),
    }


def candidate_instance(case, trial):
    n, w, A, _m, _D, _s, _t, _M, _L = case
    rng = random.Random(1_000_003*sum((i+1)*q for i, q in enumerate(case))
                        + trial)
    nodes = tuple(range(n))
    agreement = tuple(sorted(rng.sample(nodes, A)))
    seed = rng.randrange(1, PRIME)
    polynomial = tuple(rng.randrange(PRIME) for _ in range(w)) + (
        rng.randrange(1, PRIME),)
    u1 = tuple(rng.randrange(PRIME) for _ in nodes)
    u0 = [rng.randrange(PRIME) for _ in nodes]
    for node in agreement:
        u0[node] = (evaluate(polynomial, node)-seed*u1[node]) % PRIME
    for node in nodes:
        if node not in agreement:
            forbidden = (evaluate(polynomial, node)-seed*u1[node]) % PRIME
            if u0[node] == forbidden:
                u0[node] = (u0[node]+1) % PRIME
    actual = tuple(node for node in nodes
                   if evaluate(polynomial, node) ==
                   (u0[node]+seed*u1[node]) % PRIME)
    assert actual == agreement
    return tuple(u0), u1, seed, polynomial, agreement


def dense_matrix(columns):
    rows = sorted({row for column in columns for row in column}, key=repr)
    index = {row: i for i, row in enumerate(rows)}
    width = len(columns)
    flat = [0] * (len(rows)*width)
    for j, column in enumerate(columns):
        for row, value in column.items():
            flat[index[row]*width+j] = value % PRIME
    return nmod_mat(len(rows), width, flat, PRIME)


def monomial_gradient(monomial, seed, polynomial, x):
    xp, yp, rp, sp, zp = monomial
    point = (evaluate(polynomial, x), evaluate(polynomial, x, 1),
             evaluate(polynomial, x, 2), seed)
    exponents = (yp, rp, sp, zp)
    answer = []
    for coordinate in range(4):
        if exponents[coordinate] == 0:
            answer.append(0)
            continue
        value = pow(x, xp, PRIME) * exponents[coordinate]
        for j, (base, exponent) in enumerate(zip(point, exponents)):
            value *= pow(base, exponent-(j == coordinate), PRIME)
        answer.append(value % PRIME)
    return tuple(answer)


def graph_value(monomial, seed, polynomial, x):
    xp, yp, rp, sp, zp = monomial
    return (pow(x, xp, PRIME) *
            pow(evaluate(polynomial, x), yp, PRIME) *
            pow(evaluate(polynomial, x, 1), rp, PRIME) *
            pow(evaluate(polynomial, x, 2), sp, PRIME) *
            pow(seed, zp, PRIME)) % PRIME


def trial_receipt(case, trial):
    n, w, A, m, D, s, t, M, L = case
    u0, u1, seed, polynomial, agreement = candidate_instance(case, trial)
    monomials = support(w, D, s, t, M, L)
    columns = []
    for xp, yp, rp, sp, zp in monomials:
        column = {}
        for node in range(n):
            expansion = translated_column(
                xp, (yp, rp, sp), zp, node, u0[node], u1[node],
                m, 2, PRIME)
            for term, value in expansion.items():
                if value:
                    column[(node, term)] = value
        columns.append(column)
    contact = dense_matrix(columns)
    nullspace, nullity = contact.nullspace()
    actual_rank = contact.rank()
    assert actual_rank+nullity == len(monomials)

    # All rows vanish as global polynomials.  D is below m*A, and checking
    # all 101 field points is independently decisive because graph degree is
    # <D<101 for these cases.
    for relation in range(nullity):
        for x in range(PRIME):
            value = sum(int(nullspace[j, relation]) *
                        graph_value(monomial, seed, polynomial, x)
                        for j, monomial in enumerate(monomials)) % PRIME
            assert value == 0

    tangent_polynomial = interpolate(tuple(u1[node] for node in agreement),
                                     agreement)
    offdomain = (n, n+1)
    ranks = []
    vertical_ranks = []
    tangent_checks = []
    for x in offdomain:
        gradients = []
        for coordinate in range(4):
            gradients.extend(monomial_gradient(q, seed, polynomial, x)[
                coordinate] for q in monomials)
        normal = nmod_mat(4, len(monomials), gradients, PRIME) * nullspace
        ranks.append(normal.rank())
        vertical = nmod_mat(3, nullity, [
            int(normal[i, j]) for i in range(3) for j in range(nullity)
        ], PRIME)
        vertical_ranks.append(vertical.rank())
        tangent = (evaluate(tangent_polynomial, x),
                   evaluate(tangent_polynomial, x, 1),
                   evaluate(tangent_polynomial, x, 2), 1)
        tangent_checks.append(all(
            sum(tangent[i]*int(normal[i, j]) for i in range(4)) % PRIME == 0
            for j in range(nullity)))
    return {
        "trial": trial,
        "actual_contact_rank_and_nullity": (actual_rank, nullity),
        "offdomain_conormal_ranks": tuple(ranks),
        "offdomain_vertical_YRS_ranks": tuple(vertical_ranks),
        "canonical_agreement_tangent_annihilated": tuple(tangent_checks),
    }


def main():
    rows = []
    for case in CASES:
        arithmetic = source_arithmetic(case)
        assert arithmetic["columns"] == len(support(
            case[1], case[4], case[5], case[6], case[7], case[8]))
        trials = tuple(trial_receipt(case, trial) for trial in range(TRIALS))
        rows.append({
            "parameters_n_w_A_m_D_s_t_M_L": case,
            **arithmetic,
            "canonical_tangent_forced_by_degree": (
                arithmetic["penalty_mA_minus_D"] >
                arithmetic["gap_A_minus_w"]-2),
            "trials": trials,
            "minimum_and_maximum_observed_rank": (
                min(rank for row in trials
                    for rank in row["offdomain_conormal_ranks"]),
                max(rank for row in trials
                    for rank in row["offdomain_conormal_ranks"]),
            ),
        })

    print("rank_diagnostic=" + repr(tuple(
        (row["parameters_n_w_A_m_D_s_t_M_L"],
         row["universal_margin"], row["pure_YRS_3minor_residual"],
         row["minimum_and_maximum_observed_rank"])
        for row in rows)), flush=True)

    # Positive margin and r3>0 alone fail (row 0).  Raising M from m to m+1,
    # or broadening either derivative cap, repairs the rank in this chamber.
    assert tuple(row["minimum_and_maximum_observed_rank"] for row in rows) == (
        (2, 2), (3, 3), (3, 3), (3, 3), (0, 0), (3, 3), (1, 1))
    assert all(all(rank == 3 for rank in trial["offdomain_vertical_YRS_ranks"])
               for row in rows[1:4] for trial in row["trials"])
    assert all(all(all(trial["canonical_agreement_tangent_annihilated"])
                       for trial in row["trials"])
               for row in rows if row["canonical_tangent_forced_by_degree"])
    result = {
        "prime_and_trials_per_case": (PRIME, TRIALS),
        "rows": rows,
        "verdict": (
            "Positive universal margin and r3>0 do not force conormal rank "
            "three (or vertical tangent injectivity): the first and fifth "
            "rows are exact counterexamples to that stronger premise. In the "
            "m=3 chamber, changing only M from m to m+1 repairs rank two to "
            "rank three; broadening s or t also repairs it. At r3=0 rank "
            "drops again. A plausible target-specific premise is m>=3, "
            "r3>0, and a sufficiently rich terminal quotient (M>=m+1 is "
            "the simplest tested condition), not dimension positivity alone. "
            "Low Jacobian rank by itself makes no claim about Krull grade; "
            "the companion local-dimension audit handles that distinction."
        ),
    }
    canonical = json.dumps(result, sort_keys=True, separators=(",", ":"))
    print(json.dumps(result, indent=2, sort_keys=True))
    print("sha256=" + hashlib.sha256(canonical.encode()).hexdigest())


if __name__ == "__main__":
    main()
