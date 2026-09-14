#!/usr/bin/env python3
"""Small exact target-specific V-cascade probe for the F3 kernel seed.

This is intentionally an F_101, N=10 analogue.  It tests the actual packet
direction A_1=B, rather than arbitrary terminal C, in the V-only submodule

  K(X,V) = sum_(n=1)^(M+1) A_n(X) V^n.

The two fat-graph conditions become the exact polynomial divisibilities

  Xi_G^(M-n) | A_n                                           (on G),
  Xi_E^(M-j) | sum_n binom(n,j) A_n,  0 <= j < M             (on E).

Every A_n also obeys the literal weighted half-open window deg A_n<D-nW.
The coefficient A_1 is fixed to B=Xi_H^(M-1)Xi_R^M.  The resulting small
matrix gives a primal or a target-specific obstruction without inferring an
actual-N result from the small field.
"""

from __future__ import annotations

from math import comb


P = 101
N = 10
W = 4
G = 7
ECOUNT = N - G
HCOUNT = W + 1
RCOUNT = G - HCOUNT
M = 4
D = M * G


def trim(a):
    while a and a[-1] % P == 0:
        a.pop()
    return [x % P for x in a]


def add(a, b):
    out = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] = (out[i] + x) % P
    for i, x in enumerate(b):
        out[i] = (out[i] + x) % P
    return trim(out)


def scale(a, c):
    return trim([(c * x) % P for x in a])


def mul(a, b):
    out = [0] * max(0, len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % P
    return trim(out)


def power(a, n):
    out = [1]
    base = a
    while n:
        if n & 1:
            out = mul(out, base)
        n >>= 1
        if n:
            base = mul(base, base)
    return out


def divrem(a, b):
    a = trim(list(a))
    b = trim(list(b))
    if not b:
        raise ZeroDivisionError
    q = [0] * max(0, len(a) - len(b) + 1)
    ib = pow(b[-1], -1, P)
    while len(a) >= len(b):
        k = len(a) - len(b)
        c = a[-1] * ib % P
        q[k] = c
        for j, x in enumerate(b):
            a[k + j] = (a[k + j] - c * x) % P
        trim(a)
    return trim(q), a


def locator(points):
    out = [1]
    for x in points:
        out = mul(out, [(-x) % P, 1])
    return out


def rref_rank_augmented(rows, nvars):
    rows = [list(map(lambda x: x % P, row)) for row in rows]
    pivot_cols = []
    rr = 0
    for c in range(nvars):
        pivot = next((i for i in range(rr, len(rows)) if rows[i][c]), None)
        if pivot is None:
            continue
        rows[rr], rows[pivot] = rows[pivot], rows[rr]
        inv = pow(rows[rr][c], -1, P)
        rows[rr] = [(x * inv) % P for x in rows[rr]]
        for i in range(len(rows)):
            if i != rr and rows[i][c]:
                z = rows[i][c]
                rows[i] = [(x - z * y) % P for x, y in zip(rows[i], rows[rr])]
        pivot_cols.append(c)
        rr += 1
        if rr == len(rows):
            break
    inconsistent = next((row[-1] for row in rows
                         if not any(row[:nvars]) and row[-1]), None)
    return rr, inconsistent, pivot_cols, rows


def main():
    # 2 has order 100, so omega=2^10 has order 10.
    omega = pow(2, 10, P)
    points = [pow(omega, i, P) for i in range(N)]
    assert len(set(points)) == N and pow(omega, N, P) == 1
    xi_h = locator(points[:HCOUNT])
    xi_r = locator(points[HCOUNT:G])
    xi_g = mul(xi_h, xi_r)
    xi_e = locator(points[G:])
    B = mul(power(xi_h, M - 1), power(xi_r, M))
    assert len(B) - 1 == D - W - 1

    # Parametrize A_n by the mandatory G factor.  n=M+1 has no factor.
    specs = []
    offset = 0
    for n in range(2, M + 2):
        width_a = D - n * W
        gpow = max(M - n, 0)
        factor = power(xi_g, gpow)
        width_r = width_a - (len(factor) - 1)
        assert width_r > 0
        specs.append((n, offset, width_r, factor, width_a))
        offset += width_r
    nvars = offset

    # Each remainder coefficient modulo Xi_E^(M-j) is a linear equation.
    rows = []
    labels = []
    for j in range(M):
        modulus = power(xi_e, M - j)
        target = scale(B, comb(1, j) if j <= 1 else 0)
        _, target_rem = divrem(target, modulus)
        col_remainders = []
        for n, off, wr, factor, _ in specs:
            if n < j:
                col_remainders.extend([[]] * wr)
                continue
            scalar = comb(n, j) % P
            for k in range(wr):
                _, rem = divrem(scale(([0] * k) + factor, scalar), modulus)
                col_remainders.append(rem)
        assert len(col_remainders) == nvars
        for degree in range(len(modulus) - 1):
            row = [rem[degree] if degree < len(rem) else 0
                   for rem in col_remainders]
            rhs = (-(target_rem[degree] if degree < len(target_rem) else 0)) % P
            rows.append(row + [rhs])
            labels.append((j, degree))

    rank, inconsistent, pivots, reduced = rref_rank_augmented(rows, nvars)
    print({
        "parameters": (P, N, W, G, ECOUNT, HCOUNT, RCOUNT, M, D),
        "B_degree": len(B) - 1,
        "unknown_dimensions": nvars,
        "constraint_rows": len(rows),
        "matrix_rank": rank,
        "target_in_image": inconsistent is None,
        "nullity_if_consistent": nvars - rank,
        "specs_n_widthR_widthA": tuple((n, wr, wa) for n, _, wr, _, wa in specs),
    })
    if inconsistent is not None:
        bad = next(i for i, row in enumerate(reduced)
                   if not any(row[:nvars]) and row[-1])
        print({"first_reduced_inconsistency_row": bad,
               "normalized_pairing": reduced[bad][-1]})
    else:
        # Set every free coordinate to zero and recover one deterministic
        # primal.  Replay both families of polynomial divisibilities.
        solution = [0] * nvars
        for row_index, pivot in enumerate(pivots):
            solution[pivot] = reduced[row_index][-1]
        polynomials = {1: B}
        for n, off, wr, factor, width_a in specs:
            rpoly = trim(solution[off:off + wr])
            apoly = mul(factor, rpoly)
            assert len(apoly) <= width_a
            polynomials[n] = apoly
        for n, apoly in polynomials.items():
            if n < M:
                assert not divrem(apoly, power(xi_g, M - n))[1]
        for j in range(M):
            total = []
            for n, apoly in polynomials.items():
                if n >= j:
                    total = add(total, scale(apoly, comb(n, j)))
            assert not divrem(total, power(xi_e, M - j))[1]
        print({
            "primal_A_degrees": tuple((n, len(a) - 1)
                                      for n, a in sorted(polynomials.items())),
            "primal_A_coefficients": tuple((n, tuple(a))
                                           for n, a in sorted(polynomials.items())),
            "xi_h": tuple(xi_h), "xi_r": tuple(xi_r),
            "xi_g": tuple(xi_g), "xi_e": tuple(xi_e),
        })


if __name__ == "__main__":
    main()
