#!/usr/bin/env python3
"""Closed local Full187 relation and multiplicative-subgroup HRS dual data.

This is an algebra/interface audit, not a 6900 proof.  It packages two exact
reductions needed after the complete-depth Pascal projection.

* The descending 60-layer Pascal recurrence is the coefficient expansion of
  one lacunary multiple of ``(Y-U)^60``.  Consequently its desired local jets
  are scalar multiples of ``u(x)^(82-f) H_q(C)(x)``; the 126,315 residual
  blocks are filtered realizations of one relation, not independent targets.
* For the N-th roots of unity, the local triangular correction in the exact
  hyperderivative-RS dual is universal.  Only powers of the node alpha and a
  length-at-most-60 scalar series vary; no N-by-N dual matrix is necessary.

The remaining load-bearing question is whether the lacunary relation admits
representatives in all strict Full187 coefficient windows (and then whether
their u0 tails connect to the four packets).
"""

from __future__ import annotations

import hashlib
import json
from math import comb
from pathlib import Path
import resource


P = 2_130_706_433
N = 262_144
M = 60
J = 82
T = J - M


def convolution(left, right, stop=None):
    size = len(left) + len(right) - 1
    if stop is not None:
        size = min(size, stop)
    out = [0] * size
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            if i + j >= size:
                break
            out[i + j] = (out[i + j] + a * b) % P
    return out


def series_inverse(unit, stop):
    assert unit and unit[0] % P
    inv0 = pow(unit[0], -1, P)
    out = [inv0]
    for k in range(1, stop):
        value = sum(unit[i] * out[k - i]
                    for i in range(1, min(k, len(unit) - 1) + 1))
        out.append((-value * inv0) % P)
    assert convolution(unit, out, stop) == [1] + [0] * (stop - 1)
    return out


def series_power(base, exponent, stop):
    assert exponent >= 0
    out = [1]
    factor = list(base[:stop])
    while exponent:
        if exponent & 1:
            out = convolution(out, factor, stop)
        exponent >>= 1
        if exponent:
            factor = convolution(factor, factor, stop)
    return out + [0] * (stop - len(out))


def lacunary_pascal_identity():
    # A(z) is the degree-T truncation of (1-z)^(-M).
    inverse_truncation = [comb(M + i - 1, i) % P for i in range(T + 1)]
    one_minus_z_M = [((-1) ** i * comb(M, i)) % P
                     for i in range(M + 1)]
    product = convolution(one_minus_z_M, inverse_truncation)
    assert len(product) == J + 1
    assert product[0] == 1
    assert product[1:T + 1] == [0] * T

    # For k>T, the exact integer coefficient is
    # (-1)^(k-T) binom(J,k) binom(k-1,T).
    for k in range(T + 1, J + 1):
        closed = ((-1) ** (k - T) * comb(J, k) * comb(k - 1, T)) % P
        assert product[k] == closed

    # Translate k=J-f.  The polynomial identity is
    #
    # (Y-U)^M sum_i binom(M+i-1,i) U^i Y^(T-i)
    #   = Y^J + sum_(f<M) c_f U^(J-f)Y^f.
    c = tuple(product[J - f] for f in range(M))
    for f in range(M):
        closed = ((-1) ** (M - f) * comb(J, f)
                  * comb(J - f - 1, T)) % P
        assert c[f] == closed

        # This is exactly the descending Pascal recurrence after factoring
        # the common u^(J-f) H_q(C) scalar.
        recurrence = comb(J, f)
        recurrence += sum(comb(k, f) * c[k] for k in range(f, M))
        assert recurrence % P == 0

    return {
        "M_J_gap": (M, J, T),
        "inverse_truncation_coefficients_mod_p": tuple(inverse_truncation),
        "lower_coefficient_scalars_c_f_mod_p": c,
        "closed_c_f": (
            "(-1)^(60-f) * binom(82,f) * binom(81-f,22) mod p"),
        "identity": (
            "(Y-U)^60 * sum_(i=0)^22 binom(59+i,i) U^i Y^(22-i) "
            "= Y^82 + sum_(f=0)^59 c_f U^(82-f) Y^f"),
        "pascal_recurrence_checks": M,
    }


def subgroup_dual_triangular_data():
    # At alpha^N=1 and X=alpha+t,
    #   (X^N-1)/(X-alpha) = alpha^(-1) B(t/alpha),
    # B(z)=((1+z)^N-1)/z.  For multiplicity s,
    # 1/A_alpha = alpha^s B(t/alpha)^(-s), where
    # A_alpha=((X^N-1)/(X-alpha))^s.
    # Hence H_l(1/A_alpha)(alpha)=alpha^(s-l)*b_(s,l), with b universal.
    base = [comb(N, ell + 1) % P for ell in range(M)]
    assert base[0] == N
    inv_base = series_inverse(base, M)
    rows = []
    for s in range(1, M + 1):
        b = tuple(series_power(inv_base, s, s))
        # Directly verify B(z)^s * B(z)^(-s)=1 mod z^s.
        lhs = series_power(base, s, s)
        assert convolution(lhs, b, s) == [1] + [0] * (s - 1)
        rows.append((s, b))

    canonical = json.dumps(rows, separators=(",", ":"))
    return {
        "domain_polynomial": "Omega=X^N-1",
        "universal_series": "B(z)=((1+z)^N-1)/z",
        "local_inverse_formula": (
            "H_l(1/A_alpha)(alpha)=alpha^(s-l)*[z^l]B(z)^(-s)"),
        "multiplicity_range": (1, M),
        "triangular_rows_sha256": hashlib.sha256(
            canonical.encode()).hexdigest(),
        "triangular_row_lengths": tuple((s, len(b)) for s, b in rows),
        "correction_warning": (
            "dual Hasse orders reverse and then receive this upper-triangular "
            "local transform; naive same-order HRS duality is false"),
    }


def main():
    stable = {
        "scope": (
            "closed local Pascal relation and exact subgroup-HRS dual "
            "interface only; strict-window realization, u0 tails, packet "
            "bridge, and ProtocolClaim 6900 remain open"),
        "target_p_N_M_J": (P, N, M, J),
        "lacunary_relation": lacunary_pascal_identity(),
        "subgroup_dual": subgroup_dual_triangular_data(),
        "decision": (
            "GREEN_ONE_LACUNARY_RELATION_REPLACES_INDEPENDENT_RESIDUALS__"
            "NEXT_TEST_FILTERED_REPRESENTATIVE_BY_REVERSE_HASSE_DUALS"),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    print(json.dumps({
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
