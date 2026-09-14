#!/usr/bin/env python3
"""Exact small Full187 discriminator for a common curvature factor.

This reuses the ten genuine close, non-pencil polynomial candidates from
``moving_scalar_pade_component_counterexample.py``.  It replaces that
first-jet source by the literal asymmetric order-two contact source

    (n,w,g,m,D,s,t,J,L) = (7,2,4,3,12,2,1,5,7)

over GF(11).  This is the componentwise-ceiling small analogue of the target
Full187 flags.  The source uses the exact cutoff ``D=m*g`` and the exact
local translation

    Y = u0 + Z*u1 + E + T*R - T^2*S/2,

with contact weight ``wt(T)=1, wt(E)=3`` at all seven nodes.

The complete contact kernel is computed over GF(11), not sampled.  We then
regard every basis row as a univariate in curvature S over
GF(11)(X,Y,R,Z), compute its monic common gcd, and check all ten selected
graph substitutions ``(Y,R,S,Z)=(P,P',P'',gamma)`` as polynomial identities
in X.  This is the specialization used by the formal Full187 root-forcing
theorem; the alternating sign belongs to the local coordinate change.

This is a bounded discriminator, not a target theorem.
"""

from __future__ import annotations

from collections import Counter
import hashlib
import json
from pathlib import Path
import resource
import sys

from flint import nmod_mat
import sympy as sp


sys.path.insert(0, ".experiments")
import full187_anchor_zero_boundary_degree_audit_6900 as A  # noqa: E402
import full187_total_degree_mapping_cone_gate_6900 as K  # noqa: E402
import moving_scalar_pade_component_counterexample as M  # noqa: E402
import prime_o2_conormal_threshold_falsifier as C  # noqa: E402


P = 11
CASE = (7, 2, 4, 3, 12, 2, 1, 5, 7)
N, W, AGREEMENT, MULTIPLICITY, DEGREE, SLOPE, CURVATURE, ACTIVE, SEED = CASE


def trim(polynomial):
    answer = [coefficient % P for coefficient in polynomial]
    while answer and not answer[-1]:
        answer.pop()
    return tuple(answer)


def poly_add(left, right):
    answer = [0] * max(len(left), len(right))
    for index in range(len(answer)):
        answer[index] = (
            (left[index] if index < len(left) else 0)
            + (right[index] if index < len(right) else 0)
        ) % P
    return trim(answer)


def poly_scale(scalar, polynomial):
    return trim(scalar * coefficient for coefficient in polynomial)


def poly_mul(left, right):
    if not left or not right:
        return ()
    answer = [0] * (len(left) + len(right) - 1)
    for i, x in enumerate(left):
        for j, y in enumerate(right):
            answer[i + j] = (answer[i + j] + x * y) % P
    return trim(answer)


def poly_pow(base, exponent):
    answer = (1,)
    while exponent:
        if exponent & 1:
            answer = poly_mul(answer, base)
        exponent //= 2
        if exponent:
            base = poly_mul(base, base)
    return answer


def derivative(polynomial):
    return trim(i * coefficient for i, coefficient in enumerate(polynomial)
                if i)


def source_kernel():
    C.PRIME = P
    K.P = P
    monomials = C.support(W, DEGREE, SLOPE, CURVATURE, ACTIVE, SEED)
    columns = []
    for xpower, value, first, second, seed in monomials:
        column = {}
        for node in range(N):
            expansion = A.translated_column(
                xpower, (value, first, second), seed, node,
                M.RECEIVED_0[node], M.RECEIVED_1[node],
                MULTIPLICITY, 2, P)
            for local, coefficient in expansion.items():
                if coefficient:
                    column[(node, local)] = coefficient
        columns.append(column)
    rows = tuple(sorted({row for column in columns for row in column},
                        key=repr))
    matrix = nmod_mat(
        len(rows), len(columns),
        [column.get(row, 0) for row in rows for column in columns], P)
    kernel, nullity = K.compact_nullspace(matrix)
    assert kernel.nrows() == len(monomials)
    assert kernel.ncols() == nullity
    return monomials, len(rows), matrix.rank(), kernel, nullity


def relation_terms(monomials, kernel, relation):
    return tuple(
        (monomial, int(kernel[index, relation]) % P)
        for index, monomial in enumerate(monomials)
        if int(kernel[index, relation]) % P
    )


def relation_s_degree(terms):
    return max(second for (_x, _y, _r, second, _z), _c in terms)


def relation_expression(terms, X, Y, R, S, Z):
    return sum(
        coefficient * X**x * Y**y * R**r * S**s * Z**z
        for (x, y, r, s, z), coefficient in terms
    )


def graph_substitution(terms, seed, polynomial):
    first = derivative(polynomial)
    second = derivative(first)
    answer = ()
    for (xpower, value, slope, curvature, zpower), coefficient in terms:
        scalar = coefficient * pow(seed, zpower, P) % P
        scalar = scalar * pow(second[0] if second else 0, curvature, P) % P
        term = (0,) * xpower + (scalar,)
        term = poly_mul(term, poly_pow(polynomial, value))
        term = poly_mul(term, poly_pow(first, slope))
        answer = poly_add(answer, term)
    return answer


def main():
    # Fail accidental growth before constructing the exact matrix.
    resource.setrlimit(resource.RLIMIT_AS, (3 << 30, 3 << 30))
    arithmetic = C.source_arithmetic(CASE)
    assert arithmetic["universal_margin"] == 19

    monomials, contact_rows, rank, kernel, nullity = source_kernel()
    assert (len(monomials), contact_rows, rank, nullity) == (971, 987, 941, 30)
    basis = tuple(
        relation_terms(monomials, kernel, relation)
        for relation in range(nullity)
    )
    degree_histogram = Counter(map(relation_s_degree, basis))
    assert degree_histogram == Counter({1: 29, 0: 1})

    # A degree-zero row is a unit after passing to GF(11)(X,Y,R,Z)[S].
    # We nevertheless ask SymPy for the literal monic gcd in that PID.
    X, Y, R, S, Z = sp.symbols("X Y R S Z")
    coefficient_field = sp.GF(P).frac_field(X, Y, R, Z)
    order = sorted(range(nullity), key=lambda i: relation_s_degree(basis[i]))
    # The first row in this order has S-degree zero.  Converting that exact
    # row to K[S] and making it monic already returns 1.  Hence the gcd with
    # every remaining row is definitionally 1; constructing 29 unnecessary
    # giant fraction-field expressions would only obscure the certificate.
    first_univariate = sp.Poly(
        relation_expression(basis[order[0]], X, Y, R, S, Z),
        S, domain=coefficient_field)
    common = first_univariate.monic()
    # SymPy's fraction-field Poly equality retains generator identity in a
    # way that can compare false even for two printed ``Poly(1, ...)`` values.
    # Degree and the normalized coefficient are the stable exact check.
    assert common.degree() == 0 and common.as_expr() == 1

    sfree = basis[order[0]]
    sfree_base = sp.Poly(
        relation_expression(sfree, X, Y, R, S, Z), X, Y, R, Z, modulus=P)
    assert sfree_base.degree_list() == (10, 5, 1, 7)

    agreement_counts = []
    identities_checked = 0
    for seed, polynomial in M.SELECTED:
        received = tuple(
            (a + seed * b) % P
            for a, b in zip(M.RECEIVED_0, M.RECEIVED_1)
        )
        word = tuple(M.peval(polynomial, node) for node in range(N))
        agreements = sum(a == b for a, b in zip(received, word))
        assert agreements >= AGREEMENT
        agreement_counts.append(agreements)
        for terms in basis:
            assert graph_substitution(terms, seed, polynomial) == ()
            identities_checked += 1

    assert M.maximum_pencil_occupancy() == 2
    payload = {
        "scope": (
            "complete exact GF(11) target-shaped Full187 control; "
            "bounded discriminator, not target transport"
        ),
        "case_N_w_g_m_D_s_t_J_L": CASE,
        "source_columns_contact_rows_rank_nullity": (
            len(monomials), contact_rows, rank, nullity),
        "closed_rank_bound_margin": (
            N * arithmetic["one_node_rank"],
            arithmetic["universal_margin"]),
        "curvature_degree_histogram_of_kernel_basis": tuple(
            sorted(degree_histogram.items())),
        "common_gcd_over_GF11_XY RZ_of_S": "1",
        "primitive_common_gcd_in_GF11_XYRZ_S": "1",
        "quotient_curvature_degree_histogram": tuple(
            sorted(degree_histogram.items())),
        "sfree_basis_row_base_degrees_XY RZ": sfree_base.degree_list(),
        "sfree_basis_row_terms": len(sfree_base.terms()),
        "selected_candidate_count": len(M.SELECTED),
        "selected_agreement_counts": tuple(agreement_counts),
        "maximum_affine_pencil_occupancy": M.maximum_pencil_occupancy(),
        "kernel_graph_identities_checked": identities_checked,
        "selected_graphs_lie_on_common_gcd_branch": False,
        "interpretation": (
            "all ten genuine graph sections lie in the common zero scheme "
            "of all 30 kernel rows, but not on a height-one common curvature "
            "factor; their incidence is codimension at least two"
        ),
        "decision": (
            "STOP_common_relative_S_gcd_as_the_missing_fixed_carrier; "
            "a useful relative-factor route must retain the residual ideal "
            "or prove an additional target-specific height-one dichotomy"
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    payload["peak_rss_kib"] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
