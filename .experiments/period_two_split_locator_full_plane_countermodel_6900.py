#!/usr/bin/env python3
"""Exact finite-field falsifier for the split-locator bivariate shortcut.

This is deliberately a small structural control, not an instance of the
262144-node benchmark.  It retains the features relevant to the proposed
shortcut: a quadratic extension seed, prime-field split locators, prescribed
remainders, an all-node rational identity, a bad fixed direction, and one
distinct exact agreement support for every seed in the full Fp^2 plane.

There are no random choices and no third-party dependencies.
"""

from itertools import combinations


P = 13
NON_SQUARE = 2
NODES = tuple(range(1, P))
ERRORS = 5
AGREEMENTS = 7
SELECTED_DEGREE = 5

# Low-to-high coefficients in F_13[X].  Its degree is 11.
CENTRE = (7, 5, 6, 11, 5, 6, 1, 10, 7, 0, 4, 1)


def trim(poly):
    out = [x % P for x in poly]
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return tuple(out)


def poly_add(left, right):
    out = [0] * max(len(left), len(right))
    for i, value in enumerate(left):
        out[i] += value
    for i, value in enumerate(right):
        out[i] += value
    return trim(out)


def poly_sub(left, right):
    out = [0] * max(len(left), len(right))
    for i, value in enumerate(left):
        out[i] += value
    for i, value in enumerate(right):
        out[i] -= value
    return trim(out)


def poly_scale(scalar, poly):
    return trim([(scalar * value) % P for value in poly])


def poly_mul(left, right):
    out = [0] * (len(left) + len(right) - 1)
    for i, x in enumerate(left):
        for j, y in enumerate(right):
            out[i + j] += x * y
    return trim(out)


def poly_divmod(dividend, divisor):
    remainder = list(trim(dividend))
    divisor = trim(divisor)
    quotient = [0] * max(1, len(remainder) - len(divisor) + 1)
    leading_inverse = pow(divisor[-1], P - 2, P)
    while True:
        remainder = list(trim(remainder))
        if len(remainder) < len(divisor) or remainder == [0]:
            break
        shift = len(remainder) - len(divisor)
        factor = remainder[-1] * leading_inverse % P
        quotient[shift] = factor
        for i, value in enumerate(divisor):
            remainder[i + shift] = (remainder[i + shift] - factor * value) % P
    return trim(quotient), trim(remainder)


def poly_eval(poly, x):
    value = 0
    for coefficient in reversed(poly):
        value = (value * x + coefficient) % P
    return value


def root_product(roots):
    out = (1,)
    for root in roots:
        out = poly_mul(out, ((-root) % P, 1))
    return out


# F_13(alpha), alpha^2 = 2.  A pair (u,v) denotes u + v*alpha.
def k_add(left, right):
    return ((left[0] + right[0]) % P, (left[1] + right[1]) % P)


def k_sub(left, right):
    return ((left[0] - right[0]) % P, (left[1] - right[1]) % P)


def k_neg(value):
    return ((-value[0]) % P, (-value[1]) % P)


def k_mul(left, right):
    u, v = left
    x, y = right
    return ((u * x + NON_SQUARE * v * y) % P, (u * y + v * x) % P)


def k_inv(value):
    u, v = value
    norm = (u * u - NON_SQUARE * v * v) % P
    assert norm != 0
    inv_norm = pow(norm, P - 2, P)
    return (u * inv_norm % P, -v * inv_norm % P)


def k_scale(base_scalar, value):
    return (base_scalar * value[0] % P, base_scalar * value[1] % P)


def k_poly_trim(poly):
    out = [(u % P, v % P) for u, v in poly]
    while len(out) > 1 and out[-1] == (0, 0):
        out.pop()
    return tuple(out)


def k_poly_add(left, right):
    out = [(0, 0)] * max(len(left), len(right))
    for i, value in enumerate(left):
        out[i] = k_add(out[i], value)
    for i, value in enumerate(right):
        out[i] = k_add(out[i], value)
    return k_poly_trim(out)


def k_poly_mul(left, right):
    out = [(0, 0)] * (len(left) + len(right) - 1)
    for i, x in enumerate(left):
        for j, y in enumerate(right):
            out[i + j] = k_add(out[i + j], k_mul(x, y))
    return k_poly_trim(out)


def k_poly_eval(poly, x):
    value = (0, 0)
    for coefficient in reversed(poly):
        value = k_add(k_mul(value, x), coefficient)
    return value


def base_to_k_poly(poly):
    return tuple((value, 0) for value in poly)


ALPHA = (0, 1)
X_MINUS_ALPHA = (k_neg(ALPHA), (1, 0))


def eval_at_alpha(poly):
    return k_poly_eval(base_to_k_poly(poly), ALPHA)


def divide_by_x_minus_alpha(poly):
    """Divide a K[X] polynomial known to vanish at alpha by X-alpha."""
    poly = k_poly_trim(poly)
    assert len(poly) >= 2
    quotient = [(0, 0)] * (len(poly) - 1)
    quotient[-1] = poly[-1]
    for i in range(len(poly) - 2, 0, -1):
        quotient[i - 1] = k_add(poly[i], k_mul(ALPHA, quotient[i]))
    remainder = k_add(poly[0], k_mul(ALPHA, quotient[0]))
    assert remainder == (0, 0)
    quotient = k_poly_trim(quotient)
    assert k_poly_mul(X_MINUS_ALPHA, quotient) == poly
    return quotient


def matrix_rank_mod_p(matrix):
    rows = [list(map(lambda x: x % P, row)) for row in matrix]
    if not rows:
        return 0
    rank = 0
    columns = len(rows[0])
    for column in range(columns):
        pivot = next((r for r in range(rank, len(rows)) if rows[r][column]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        inverse = pow(rows[rank][column], P - 2, P)
        rows[rank] = [(inverse * x) % P for x in rows[rank]]
        for r in range(len(rows)):
            if r != rank and rows[r][column]:
                factor = rows[r][column]
                rows[r] = [
                    (x - factor * y) % P for x, y in zip(rows[r], rows[rank])
                ]
        rank += 1
        if rank == len(rows):
            break
    return rank


def lagrange_interpolate(points):
    """Interpolate K-valued data at pairwise distinct base-field points."""
    out = ((0, 0),)
    for x, value in points:
        numerator = (1,)
        denominator = 1
        for y, _ in points:
            if y == x:
                continue
            numerator = poly_mul(numerator, ((-y) % P, 1))
            denominator = denominator * (x - y) % P
        scale = k_scale(pow(denominator, P - 2, P), value)
        term = tuple(k_mul((coefficient, 0), scale) for coefficient in numerator)
        out = k_poly_add(out, term)
    return k_poly_trim(out)


def main():
    # 2 is a nonsquare, so X^2-2 is irreducible and alpha is not a node.
    assert pow(NON_SQUARE, (P - 1) // 2, P) == P - 1
    node_polynomial = root_product(NODES)
    assert node_polynomial == (P - 1,) + (0,) * 11 + (1,)
    assert len(CENTRE) - 1 == 11

    # For each split error locator q, B is the centre remainder modulo the
    # complementary agreement locator.  Record a lexicographically first q
    # for every residue gamma=B(alpha).
    by_seed = {}
    all_split_locators = 0
    for errors in combinations(NODES, ERRORS):
        error_set = frozenset(errors)
        agreements = tuple(x for x in NODES if x not in error_set)
        q = root_product(errors)
        agreement_locator = root_product(agreements)
        assert poly_mul(q, agreement_locator) == node_polynomial
        _, scalar = poly_divmod(CENTRE, agreement_locator)
        assert len(scalar) - 1 <= AGREEMENTS - 1

        # rem_N(q*f)=q*B, and q|N.  This is the literal prescribed-remainder
        # condition, not the relaxed recurrence kernel.
        q_times_scalar = poly_mul(q, scalar)
        _, prescribed_remainder = poly_divmod(poly_mul(q, CENTRE), node_polynomial)
        assert prescribed_remainder == q_times_scalar
        assert poly_divmod(node_polynomial, q)[1] == (0,)

        seed = eval_at_alpha(scalar)
        by_seed.setdefault(seed, (errors, agreements, q, agreement_locator, scalar))
        all_split_locators += 1

    assert all_split_locators == 792
    assert len(by_seed) == P * P
    assert set(by_seed) == {(u, v) for u in range(P) for v in range(P)}

    agreement_incidence = {x: 0 for x in NODES}
    scalar_vectors = []
    selected_vectors = []

    for seed, (errors, agreements, q, agreement_locator, scalar) in by_seed.items():
        # The exact selected polynomial P_gamma=(B_gamma-gamma)/(X-alpha).
        numerator = list(base_to_k_poly(scalar))
        numerator[0] = k_sub(numerator[0], seed)
        selected = divide_by_x_minus_alpha(tuple(numerator))
        assert len(selected) - 1 <= SELECTED_DEGREE
        assert k_poly_add(k_poly_mul(X_MINUS_ALPHA, selected), (seed,)) == base_to_k_poly(scalar)

        # Fixed all-node rational gauge:
        #   U0=f/(X-alpha), U1=-1/(X-alpha),
        #   P_gamma=U0+gamma*U1 on the exact agreement support.
        for x in NODES:
            xk = (x, 0)
            denominator = k_sub(xk, ALPHA)
            u0 = k_mul((poly_eval(CENTRE, x), 0), k_inv(denominator))
            u1 = k_neg(k_inv(denominator))
            assert k_mul(denominator, u0) == (poly_eval(CENTRE, x), 0)
            assert k_mul(denominator, u1) == (P - 1, 0)
            assert k_mul(denominator, k_poly_eval(selected, xk)) == k_sub(
                (poly_eval(scalar, x), 0), seed
            )
            if x in agreements:
                agreement_incidence[x] += 1
                assert poly_eval(scalar, x) == poly_eval(CENTRE, x)
                assert k_poly_eval(selected, xk) == k_add(u0, k_mul(seed, u1))
            else:
                assert poly_eval(q, x) == 0

        # The fixed U1 direction is bad on this seven-node support at degree
        # five.  Its unique degree<=6 interpolant has degree exactly six.
        u1_points = []
        for x in agreements:
            u1 = k_neg(k_inv(k_sub((x, 0), ALPHA)))
            u1_points.append((x, u1))
        u1_interpolant = lagrange_interpolate(u1_points)
        assert len(u1_interpolant) - 1 == AGREEMENTS - 1
        for x, value in u1_points:
            assert k_poly_eval(u1_interpolant, (x, 0)) == value

        scalar_vectors.append(tuple(scalar) + (0,) * (AGREEMENTS - len(scalar)))
        selected_vectors.append(selected + ((0, 0),) * (SELECTED_DEGREE + 1 - len(selected)))

    # Distinct seeds give distinct q/supports/scalars.  The scalar coefficient
    # family in fact has the maximum possible affine rank in degree <=6.
    assert len({value[2] for value in by_seed.values()}) == P * P
    assert len({value[4] for value in by_seed.values()}) == P * P
    origin = scalar_vectors[0]
    scalar_difference_matrix = [
        [(x - y) % P for x, y in zip(vector, origin)] for vector in scalar_vectors[1:]
    ]
    scalar_affine_rank = matrix_rank_mod_p(scalar_difference_matrix)
    assert scalar_affine_rank == AGREEMENTS

    # The seed projection is the whole grid.  The 169 reduced monomials
    # U^i V^j (0<=i,j<13) have full evaluation rank, so no nonzero polynomial
    # of total degree <=12 can vanish on it.  Degree 12 is the exact scaled
    # Schwartz-Zippel allowance floor((169-1)/13).
    seeds = sorted(by_seed)
    monomial_exponents = [(i, j) for i in range(P) for j in range(P)]
    evaluation_matrix = [
        [pow(u, i, P) * pow(v, j, P) % P for i, j in monomial_exponents]
        for u, v in seeds
    ]
    evaluation_rank = matrix_rank_mod_p(evaluation_matrix)
    assert evaluation_rank == P * P
    assert (P * P - 1) // P == P - 1

    # A nonzero affine bivariate polynomial has 0 or 13 grid zeros.  Every
    # node occurs in a different number of selected agreement supports, so
    # no degree<=1 node-membership polynomial can describe even one node.
    # Here 1=floor((169-1)/(12*13)) is the scaled membership-degree budget.
    incidence_values = tuple(agreement_incidence[x] for x in NODES)
    assert all(count not in (0, P, P * P) for count in incidence_values)
    assert (P * P - 1) // (len(NODES) * P) == 1

    # Projective-high check for the fixed word plane at degree five.  If
    # lambda0*U0+lambda1*U1 were a degree<=5 word on all twelve nodes, then
    # multiplying by X-alpha would contradict deg(f)=11 when lambda0!=0,
    # and evaluation at alpha would contradict lambda1!=0 otherwise.  The
    # exhaustive interpolation below checks the same statement exactly.
    for lambda0 in range(P):
        for lambda1 in range(P):
            if lambda0 == 0 and lambda1 == 0:
                continue
            points = []
            for x in NODES:
                denominator = k_sub((x, 0), ALPHA)
                numerator = (lambda0 * poly_eval(CENTRE, x) - lambda1, 0)
                points.append((x, k_mul(numerator, k_inv(denominator))))
            interpolation = lagrange_interpolate(points)
            assert len(interpolation) - 1 > SELECTED_DEGREE

    print("PASS exact split-locator full-plane countermodel")
    print(f"field=F_{P}, extension=F_{P}(alpha), alpha^2={NON_SQUARE}")
    print(f"nodes={len(NODES)}, locators={all_split_locators}, selected_seeds={len(by_seed)}")
    print(f"seed_projection={P}x{P}=full, reduced_evaluation_rank={evaluation_rank}")
    print(f"scalar_affine_rank={scalar_affine_rank}")
    print(f"agreement_incidence_by_node={incidence_values}")
    print("seed_eliminant_total_degree_floor=12: impossible")
    print("bivariate_node_membership_degree_floor=1: impossible")


if __name__ == "__main__":
    main()
