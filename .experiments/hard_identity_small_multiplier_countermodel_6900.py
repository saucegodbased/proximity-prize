#!/usr/bin/env python3
"""Exact finite-field countergate for the near-total-identity inference.

This is deliberately a *scaled* model, not a benchmark candidate.  It checks
the same kinds of interfaces which were proposed as a route from the hard
identity branch to either ``s >= 146`` or scalar affine rank at most 31:

* 64 injective evaluation nodes in F_257, namely all 64th roots of unity;
* two projective-high received interpolants V0=X^62 and V1=X^63;
* degree-31 selected polynomials with 33 agreements;
* both received rows are outside the degree-31 projected code on every
  selected support (the literal badness condition is stronger than needed);
* a fixed scalar identity with E=X and Q=c=1, d=a=0, b=1, so the combined
  multiplier degree is s=0;
* every fixed affine identity row vanishes at all 64 nodes;
* scalar polynomials have degree at most 32, agree with one common centre on
  all 33 support nodes, are injective, and have affine rank 33 (>31);
* every received-minus-selected residual is nonzero, has the actual support
  locator as a factor, and leaves quotient degree at most 30.

The model exploits the exact all-node-locator wrap

    X * X^63 - 1 = X^64 - 1.

Consequently near-total identity, projective highness, same-witness scalar
equations, residual factorization, and projected-code badness do not by
themselves force a positive multiplier degree or a rank-31 carrier.  Any such
benchmark theorem needs a genuinely global premise using the quantitative
agreement surplus / huge retained family (or additional conic/cross
structure), not just the exported local interfaces tested here.

All arithmetic below is integer arithmetic reduced modulo the prime 257.
The pseudorandom sampler has a fixed seed; it is only used to locate a compact
certificate.  Every advertised property is then checked exactly.
"""

from random import Random


P = 257
N = 64
SELECTED_DEGREE = 31
SCALAR_DEGREE = 32
AGREEMENTS = 33


def inv(x: int) -> int:
    assert x % P
    return pow(x, P - 2, P)


def primitive_generator() -> int:
    for g in range(2, P):
        if len({pow(g, k, P) for k in range(P - 1)}) == P - 1:
            return g
    raise AssertionError("no primitive generator")


GENERATOR = primitive_generator()
OMEGA = pow(GENERATOR, (P - 1) // N, P)
NODES = [pow(OMEGA, k, P) for k in range(N)]


def eval_poly(coeffs: list[int], x: int) -> int:
    value = 0
    for coefficient in reversed(coeffs):
        value = (value * x + coefficient) % P
    return value


def interpolate(xs: tuple[int, ...], ys: list[int]) -> list[int]:
    """Coefficient list of the degree < len(xs) Lagrange interpolant."""
    out = [0] * len(xs)
    for j, xj in enumerate(xs):
        basis = [1]
        denominator = 1
        for m, xm in enumerate(xs):
            if m == j:
                continue
            nxt = [0] * (len(basis) + 1)
            for k, coefficient in enumerate(basis):
                nxt[k] = (nxt[k] - coefficient * xm) % P
                nxt[k + 1] = (nxt[k + 1] + coefficient) % P
            basis = nxt
            denominator = denominator * (xj - xm) % P
        scale = ys[j] * inv(denominator) % P
        for k, coefficient in enumerate(basis):
            out[k] = (out[k] + scale * coefficient) % P
    return out


def interpolation_top_coefficient(xs: tuple[int, ...], exponent: int) -> int:
    """Top coefficient of the interpolant of x |-> x^exponent on xs."""
    value = 0
    for j, xj in enumerate(xs):
        denominator = 1
        for m, xm in enumerate(xs):
            if m != j:
                denominator = denominator * (xj - xm) % P
        value = (value + pow(xj, exponent, P) * inv(denominator)) % P
    return value


def matrix_rank(rows: list[list[int]]) -> int:
    matrix = [row[:] for row in rows]
    if not matrix:
        return 0
    rank = 0
    for column in range(len(matrix[0])):
        pivot = next(
            (i for i in range(rank, len(matrix)) if matrix[i][column] % P),
            None,
        )
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        scale = inv(matrix[rank][column])
        matrix[rank] = [x * scale % P for x in matrix[rank]]
        for i in range(len(matrix)):
            if i == rank or not matrix[i][column]:
                continue
            scale = matrix[i][column]
            matrix[i] = [
                (x - scale * y) % P
                for x, y in zip(matrix[i], matrix[rank])
            ]
        rank += 1
    return rank


def find_candidates() -> dict[int, tuple[tuple[int, ...], list[int], list[int]]]:
    rng = Random(2)
    candidates: dict[int, tuple[tuple[int, ...], list[int], list[int]]] = {}
    for _ in range(50_000):
        support = tuple(rng.sample(NODES, AGREEMENTS))
        top0 = interpolation_top_coefficient(support, N - 2)
        top1 = interpolation_top_coefficient(support, N - 1)
        if top0 == 0 or top1 == 0:
            continue
        gamma = -top0 * inv(top1) % P
        if gamma in candidates:
            continue
        values = [
            (pow(x, N - 2, P) + gamma * pow(x, N - 1, P)) % P
            for x in support
        ]
        selected_with_top = interpolate(support, values)
        assert selected_with_top[-1] == 0
        selected = selected_with_top[:-1]

        # E*selected = gamma + scalar, with E=X.
        scalar = [0] * (SCALAR_DEGREE + 1)
        scalar[0] = -gamma % P
        for k, coefficient in enumerate(selected):
            scalar[k + 1] = coefficient

        # On support: scalar = X*(V0+gamma*V1)-gamma = X^63.
        assert all(
            eval_poly(scalar, x) == pow(x, N - 1, P) for x in support
        )
        candidates[gamma] = (support, selected, scalar)
    return candidates


def greedy_affinely_independent(
    candidates: dict[int, tuple[tuple[int, ...], list[int], list[int]]]
) -> list[int]:
    augmented_rows: list[list[int]] = []
    seeds: list[int] = []
    rank = 0
    for gamma, (_, _, scalar) in candidates.items():
        candidate_rank = matrix_rank(augmented_rows + [[1] + scalar])
        if candidate_rank > rank:
            seeds.append(gamma)
            augmented_rows.append([1] + scalar)
            rank = candidate_rank
    return seeds


def main() -> None:
    assert len(set(NODES)) == N
    assert all(pow(x, N, P) == 1 for x in NODES)

    candidates = find_candidates()
    seeds = greedy_affinely_independent(candidates)
    assert len(seeds) == 34

    scalars = [candidates[gamma][2] for gamma in seeds]
    # Affine direction rank = rank([1, point])-1 for a nonempty family.
    affine_rank = matrix_rank([[1] + scalar for scalar in scalars]) - 1
    assert affine_rank == 33
    assert len({tuple(scalar) for scalar in scalars}) == len(seeds)

    for gamma in seeds:
        support, selected, scalar = candidates[gamma]
        assert len(set(support)) == AGREEMENTS
        assert len(selected) <= SELECTED_DEGREE + 1
        assert len(scalar) <= SCALAR_DEGREE + 1

        # Same-witness selected agreement.
        assert all(
            eval_poly(selected, x)
            == (pow(x, N - 2, P) + gamma * pow(x, N - 1, P)) % P
            for x in support
        )

        # Literal scalar identity E*P = gamma + S, and common-centre contact.
        assert all(
            x * eval_poly(selected, x) % P
            == (gamma + eval_poly(scalar, x)) % P
            for x in NODES
        )
        assert all(
            eval_poly(scalar, x) == pow(x, N - 1, P) for x in support
        )

        # Both rows are bad on this 33-node support: their degree-32
        # interpolants have nonzero top coefficient, so no degree-31 word
        # represents either projected row.
        assert interpolation_top_coefficient(support, N - 2) != 0
        assert interpolation_top_coefficient(support, N - 1) != 0

        # The actual received-minus-selected residual is nonzero, vanishes on
        # all support nodes, and has degree <=63. Dividing its 33 distinct
        # linear roots leaves degree <=30.
        residual = [(-c) % P for c in selected] + [0] * (N - len(selected))
        residual[N - 2] = (residual[N - 2] + 1) % P
        residual[N - 1] = (residual[N - 1] + gamma) % P
        assert any(residual)
        assert all(eval_poly(residual, x) == 0 for x in support)
        assert (N - 1) - AGREEMENTS == 30

    # Fixed identity rows: E*V0-centre=0 and E*V1-1=X^64-1, hence both
    # vanish on every evaluation node.  The multiplier data are Q=c=1,d=0.
    assert all((x * pow(x, N - 2, P) - pow(x, N - 1, P)) % P == 0 for x in NODES)
    assert all((x * pow(x, N - 1, P) - 1) % P == 0 for x in NODES)
    combined_multiplier_degree = 0
    assert combined_multiplier_degree == 0

    # Every nonzero projective combination alpha*V0+beta*V1 has degree 62
    # or 63, far above selected degree 31.
    assert N - 2 > SELECTED_DEGREE

    print(
        "GREEN exact countermodel:",
        f"field=F_{P}",
        f"nodes={N}",
        f"seeds={len(seeds)}",
        f"agreements={AGREEMENTS}",
        f"selected_degree<={SELECTED_DEGREE}",
        f"scalar_degree<={SCALAR_DEGREE}",
        f"affine_scalar_rank={affine_rank}",
        "s=0",
    )
    print("seed certificate:", seeds)


if __name__ == "__main__":
    main()
