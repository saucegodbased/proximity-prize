#!/usr/bin/env python3
"""Exact target charge-13 transposed gate, with no ambient-187 matrix.

This file deliberately separates two objects which earlier experiments blurred:

* ``M13_principal`` is the completely specified same-row last-charge block.
  It has eleven polynomial input streams, their strict half-open coefficient
  windows, and the three correlated A/B/C outputs for each stream, including
  every same-row positive-Hasse collision through Hasse order three.
* ``Rlt13`` is the (currently missing) coefficientwise reduction of F0..F3
  through every lower-charge Hermite/contact pivot, including its tails.

Once a reduced residue ``Rlt13(Fi)`` is supplied as 33 target-domain vectors,
``solve_principal_operator`` is an exact matrix-free membership test.  It returns either
the unique strict-window primal polynomial, or one of two explicit transpose
certificates:

* a transposed Schur dual when B or C disagrees with the unique A-derived
  eleven-stream primal;
* a Fourier coefficient-extraction dual when an A polynomial has a nonzero
  coefficient outside its half-open window.

Nonprincipal output rows and their lower-charge pivot tails belong to
``Rlt13``; this file refuses to certify the full gate until they are supplied.

The target instance is literal: p=2130706433, N=2^18, the prescribed first-G,
last-E and first-H node sets, Xi_E, Q=Xi_E^2, q_H=Q mod Xi_H, and the
precommitted error word x^(e-1).  We take gamma=P=0 and U0=0 on G, 1 on E.
Thus the fourth packet is the exact partial-locator packet

    F3 = Xi_H^59 Xi_(G\H)^60 * (Y - Z*q_H),

not a pure Z1 impulse.  Its literal error-contact syndrome is retained in
factored local-translation form.  No small-prime inference is used.
"""

from __future__ import annotations

import argparse
import gc
import hashlib
import json
from math import comb
import resource
import struct
import sys
import time
from dataclasses import dataclass
from typing import Iterable, Sequence

from flint import nmod_poly


P = 2_130_706_433
N = 262_144
GENERATOR = 3
W = 131_071
G = 180_413
E = 81_731
H = W + 1
M = 60
D = 10_824_780
Q_CONTACT = 21
T_BOUND = 10
J_BOUND = 82
L_BOUND = 2_703

CHARGE = 13
STREAMS = 11
BASE_WIDTH = 76_979

A_SCALAR = 603_758_703
B_SCALAR = 693_269_975
C_SCALAR = 642_373_467

PACKETS = ("F0", "F1", "F2", "F3")
GAMMA = 0


def source_width(s: int) -> int:
    if not 0 <= s < STREAMS:
        raise ValueError(f"stream index outside [0,{STREAMS}): {s}")
    return BASE_WIDTH + s


def top_row(kind: str, s: int) -> tuple[int, int, int, int, int]:
    """Return (T,E,R,S,Z) for one of the three unresolved q=0 heads."""
    if kind == "A":
        return (2, 6, 21 - s, s + 1, 2_675)
    if kind == "B":
        return (6, 5, 21 - s, s + 3, 2_674)
    if kind == "C":
        return (3, 6, 22 - s, s + 1, 2_674)
    raise ValueError(f"unknown output kind {kind!r}")


def origin(s: int) -> tuple[int, int, int, int]:
    """Return (Y,R,S,Z) for c_s(X) Y^61 R^(21-s) S^s Z^2621."""
    source_width(s)  # range check
    return (61, 21 - s, s, 2_621)


def output_scalar(kind: str) -> int:
    if kind == "A":
        return A_SCALAR
    if kind == "B":
        return B_SCALAR
    if kind == "C":
        return C_SCALAR
    raise ValueError(f"unknown output kind {kind!r}")


def u1_exponent(kind: str) -> int:
    if kind == "A":
        return 54
    if kind in ("B", "C"):
        return 53
    raise ValueError(f"unknown output kind {kind!r}")


def sha256_u32(values: Iterable[int]) -> str:
    digest = hashlib.sha256()
    chunk: list[int] = []
    for value in values:
        chunk.append(int(value) % P)
        if len(chunk) == 16_384:
            digest.update(struct.pack(f"<{len(chunk)}I", *chunk))
            chunk.clear()
    if chunk:
        digest.update(struct.pack(f"<{len(chunk)}I", *chunk))
    return digest.hexdigest()


def ntt(values: list[int], *, inverse: bool = False) -> None:
    """In-place radix-two transform; forward values are f(omega^j)."""
    n = len(values)
    if n == 0 or n & (n - 1) or (P - 1) % n:
        raise ValueError(f"unsupported transform length {n}")

    j = 0
    for i in range(1, n):
        bit = n >> 1
        while j & bit:
            j ^= bit
            bit >>= 1
        j ^= bit
        if i < j:
            values[i], values[j] = values[j], values[i]

    root = pow(GENERATOR, (P - 1) // n, P)
    if inverse:
        root = pow(root, P - 2, P)

    length = 2
    while length <= n:
        step = pow(root, n // length, P)
        half = length >> 1
        for start in range(0, n, length):
            zeta = 1
            stop = start + half
            for left in range(start, stop):
                right = left + half
                u = values[left]
                v = values[right] * zeta % P
                add = u + v
                if add >= P:
                    add -= P
                sub = u - v
                if sub < 0:
                    sub += P
                values[left] = add
                values[right] = sub
                zeta = zeta * step % P
        length <<= 1

    if inverse:
        inv_n = pow(n, P - 2, P)
        for i, value in enumerate(values):
            values[i] = value * inv_n % P


def geometric_locator(
    omega_powers: Sequence[int], *, start: int, length: int
) -> list[int]:
    """Coefficients of prod_{j=start}^{start+length-1}(X-omega^j).

    This is the exact O(length) q-binomial recurrence already used by the
    target NTT tangent experiments.  It avoids an O(length^2) product tree in
    Python and does not approximate or sample the target locator.
    """
    if length < 0 or start < 0 or start + length > N:
        raise ValueError("invalid geometric locator interval")
    if length == 0:
        return [1]

    denominators = [(1 - omega_powers[k]) % P for k in range(1, length + 1)]
    prefix = [1] * (length + 1)
    for k, denominator in enumerate(denominators):
        if denominator == 0:
            raise AssertionError("locator recurrence encountered zero denominator")
        prefix[k + 1] = prefix[k] * denominator % P
    inverse_product = pow(prefix[-1], P - 2, P)
    denominator_inverses = [0] * length
    for k in range(length - 1, -1, -1):
        denominator_inverses[k] = inverse_product * prefix[k] % P
        inverse_product = inverse_product * denominators[k] % P

    coefficients = [0] * (length + 1)
    coefficients[length] = 1
    q_power = omega_powers[start]
    for k in range(1, length + 1):
        index = length - k
        numerator_factor = (1 - omega_powers[index + 1]) % P
        value = coefficients[index + 1] * q_power % P
        value = value * numerator_factor % P
        value = value * denominator_inverses[k - 1] % P
        coefficients[index] = (-value) % P
        q_power = q_power * omega_powers[1] % P
    return coefficients


def batch_inverse(values: Sequence[int]) -> list[int]:
    """Invert a nonzero field vector with one modular exponentiation."""
    prefix = [1] * (len(values) + 1)
    for j, raw_value in enumerate(values):
        value = int(raw_value) % P
        if value == 0:
            raise ZeroDivisionError(f"zero at batch-inverse position {j}")
        prefix[j + 1] = prefix[j] * value % P
    accumulator = pow(prefix[-1], P - 2, P)
    result = [0] * len(values)
    for j in range(len(values) - 1, -1, -1):
        result[j] = accumulator * prefix[j] % P
        accumulator = accumulator * (int(values[j]) % P) % P
    return result


@dataclass
class TargetInstance:
    omega: int
    omega_powers: list[int]
    xi_e_coefficients: list[int]
    xi_h_coefficients: list[int]
    xi_r_coefficients: list[int]
    q_coefficients: list[int]
    qh_coefficients: list[int]
    u1_values: list[int]
    u1_inverse: list[int]
    u1_pow53: list[int]
    u1_pow53_inverse: list[int]
    f3_selected_error_syndrome: list[int]
    hashes: dict[str, str]
    build_seconds: float


def build_target_instance(*, verbose: bool = False) -> TargetInstance:
    """Construct and check the frozen target instance coefficientwise."""
    started = time.monotonic()
    if G + E != N or H != W + 1 or 2 * E >= G or not (W < 2 * E):
        raise AssertionError("target size ledger changed")

    omega = pow(GENERATOR, (P - 1) // N, P)
    if pow(omega, N, P) != 1 or pow(omega, N // 2, P) == 1:
        raise AssertionError("chosen target root does not have exact order N")
    omega_powers = [1] * (N + 1)
    for j in range(N):
        omega_powers[j + 1] = omega_powers[j] * omega % P
    if omega_powers[N] != 1:
        raise AssertionError("target domain did not close")

    if verbose:
        print("constructing Xi_E and Xi_H", file=sys.stderr)
    xi_e = geometric_locator(omega_powers, start=G, length=E)
    xi_h = geometric_locator(omega_powers, start=0, length=H)
    xi_r = geometric_locator(omega_powers, start=H, length=G - H)
    if xi_e[-1] != 1 or xi_h[-1] != 1 or xi_r[-1] != 1:
        raise AssertionError("non-monic locator")

    xi_e_values = xi_e + [0] * (N - len(xi_e))
    ntt(xi_e_values)
    if any(value != 0 for value in xi_e_values[G:]):
        raise AssertionError("Xi_E failed on an error node")
    if any(value == 0 for value in xi_e_values[:G]):
        raise AssertionError("Xi_E vanished on an agreement node")

    if verbose:
        print("forming Q and exact Hermite remainder q_H", file=sys.stderr)
    q_poly = nmod_poly(xi_e, P) * nmod_poly(xi_e, P)
    xi_h_poly = nmod_poly(xi_h, P)
    qh_poly = q_poly % xi_h_poly
    if q_poly.degree() != 2 * E or qh_poly.degree() > W:
        raise AssertionError("Q/q_H degree contract failed")
    q_coefficients = [int(q_poly[j]) for j in range(q_poly.degree() + 1)]
    qh_coefficients = [int(qh_poly[j]) for j in range(qh_poly.degree() + 1)]

    # Q values are Xi_E values squared.  Check q_H on every one of the H
    # prescribed nodes, rather than relying only on the polynomial remainder.
    q_values = [value * value % P for value in xi_e_values]
    qh_values = qh_coefficients + [0] * (N - len(qh_coefficients))
    ntt(qh_values)
    if qh_values[:H] != q_values[:H]:
        raise AssertionError("q_H does not interpolate Q on the entire H set")

    # Precommitted deterministic error word: delta(x)=x^(E-1).  On G, U1=Q;
    # on E, U1=Q+delta=delta because Xi_E vanishes there.
    u1_values = q_values
    for j in range(G, N):
        u1_values[j] = pow(omega_powers[j], E - 1, P)
    if any(value == 0 for value in u1_values):
        raise AssertionError("precommitted U1 has a zero domain value")
    u1_pow53 = [pow(value, 53, P) for value in u1_values]
    u1_inverse = batch_inverse(u1_values)
    u1_pow53_inverse = batch_inverse(u1_pow53)

    # Exact selected-seed scalar of the F3 error-contact syndrome.  With
    # gamma=P=0 and U0=1 on E, selectedValueResidual is one, so it is B(x).
    # Evaluate the factored B without expanding its degree-10,693,708
    # coefficient vector.
    xi_h_values = xi_h + [0] * (N - len(xi_h))
    xi_r_values = xi_r + [0] * (N - len(xi_r))
    ntt(xi_h_values)
    ntt(xi_r_values)
    b_values = [
        pow(xi_h_values[j], 59, P) * pow(xi_r_values[j], 60, P) % P
        for j in range(N)
    ]
    if any(b_values[j] != 0 for j in range(G)):
        raise AssertionError("F3 partial factor failed to vanish on G")
    f3_selected_error_syndrome = b_values[G:]
    if any(value == 0 for value in f3_selected_error_syndrome):
        raise AssertionError("F3 selected-seed error syndrome vanished")

    # There cannot be a degree <= W all-node polynomial equal to U1: such a
    # polynomial P0 agrees with Q on G roots, while deg(Q-P0) <= 2E < G; hence
    # P0=Q, contradicting deg(Q)=2E>W and the nonzero error offsets.
    if not (max(2 * E, W) < G and 2 * E > W):
        raise AssertionError("degree/root-count exclusion no longer applies")

    hashes = {
        "omega_powers_u32_le": sha256_u32(omega_powers[:-1]),
        "Xi_E_coefficients_u32_le": sha256_u32(xi_e),
        "Xi_H_coefficients_u32_le": sha256_u32(xi_h),
        "Xi_R_coefficients_u32_le": sha256_u32(xi_r),
        "Q_coefficients_u32_le": sha256_u32(q_coefficients),
        "q_H_coefficients_u32_le": sha256_u32(qh_coefficients),
        "U1_domain_values_u32_le": sha256_u32(u1_values),
        "F3_selected_error_syndrome_on_E_u32_le": sha256_u32(
            f3_selected_error_syndrome
        ),
    }
    return TargetInstance(
        omega=omega,
        omega_powers=omega_powers,
        xi_e_coefficients=xi_e,
        xi_h_coefficients=xi_h,
        xi_r_coefficients=xi_r,
        q_coefficients=q_coefficients,
        qh_coefficients=qh_coefficients,
        u1_values=u1_values,
        u1_inverse=u1_inverse,
        u1_pow53=u1_pow53,
        u1_pow53_inverse=u1_pow53_inverse,
        f3_selected_error_syndrome=f3_selected_error_syndrome,
        hashes=hashes,
        build_seconds=time.monotonic() - started,
    )


OutputVectors = dict[tuple[str, int], list[int]]


def hasse_derivative(
    coefficients: Sequence[int], order: int, output_width: int
) -> list[int]:
    """The literal Hasse_order map, truncated to the exact tapered width."""
    if order < 0:
        raise ValueError("negative Hasse order")
    result = [0] * output_width
    stop = min(output_width, max(0, len(coefficients) - order))
    for k in range(stop):
        result[k] = int(coefficients[k + order]) * comb(k + order, order) % P
    return result


def add_scaled_polynomial(target: list[int], source: Sequence[int], scalar: int) -> None:
    scalar %= P
    for k, raw_value in enumerate(source):
        target[k] = (target[k] + scalar * int(raw_value)) % P


COLLISION_TERMS: dict[str, tuple[tuple[int, int], ...]] = {
    "A": ((0, 1), (1, -2)),
    # This is a Hasse-binomial translation operator.  It must not be coded as
    # a composition power of 1-2*Hasse_1 because H1 o H1 = 2*H2.
    "B": ((0, 1), (1, -6), (2, 12), (3, -8)),
    "C": ((0, 1), (1, -1)),
}


def collision_polynomials(
    coefficient_streams: Sequence[Sequence[int]], kind: str
) -> list[list[int]]:
    """Apply the exact same-row positive-Hasse collision operator."""
    if len(coefficient_streams) != STREAMS:
        raise ValueError(f"expected {STREAMS} physical streams")
    terms = COLLISION_TERMS[kind]
    outputs: list[list[int]] = []
    for s in range(STREAMS):
        width = source_width(s)
        output = [0] * width
        for offset, scalar in terms:
            source_index = s + offset
            if source_index >= STREAMS:
                continue
            source = coefficient_streams[source_index]
            if len(source) > source_width(source_index):
                raise ValueError(
                    f"stream {source_index} violates its half-open window"
                )
            # Exact taper identity: width(s+j)-j = width(s).
            if source_width(source_index) - offset != width:
                raise AssertionError("charge-13 taper identity changed")
            derivative = hasse_derivative(source, offset, width)
            add_scaled_polynomial(output, derivative, scalar)
        outputs.append(output)
    return outputs


def invert_collision(
    output_polynomials: Sequence[Sequence[int]], kind: str
) -> list[list[int]]:
    """Invert any tapered upper-unitriangular Hasse collision family."""
    if len(output_polynomials) != STREAMS:
        raise ValueError(f"expected {STREAMS} {kind} polynomials")
    terms = COLLISION_TERMS[kind]
    if terms[0] != (0, 1):
        raise AssertionError("collision diagonal is not one")
    coefficients: list[list[int]] = [[] for _ in range(STREAMS)]
    for s in range(STREAMS - 1, -1, -1):
        width = source_width(s)
        if len(output_polynomials[s]) != width:
            raise ValueError(f"{kind} polynomial has wrong tapered width")
        current = [int(value) % P for value in output_polynomials[s]]
        for offset, scalar in terms[1:]:
            if s + offset >= STREAMS:
                continue
            derivative = hasse_derivative(coefficients[s + offset], offset, width)
            add_scaled_polynomial(current, derivative, -scalar)
        coefficients[s] = current
    if collision_polynomials(coefficients, kind) != [
        list(x) for x in output_polynomials
    ]:
        raise AssertionError(f"upper-unitriangular {kind} inverse failed")
    return coefficients


def invert_a_collision(a_polynomials: Sequence[Sequence[int]]) -> list[list[int]]:
    """Use A as the fixed principal Schur pivot."""
    return invert_collision(a_polynomials, "A")


def polynomial_to_output_values(
    coefficients: Sequence[int], kind: str, instance: TargetInstance
) -> list[int]:
    values = [int(value) % P for value in coefficients]
    if len(values) > N:
        raise ValueError("coefficient vector exceeds target domain")
    values.extend([0] * (N - len(values)))
    ntt(values)
    scalar = output_scalar(kind)
    for j in range(N):
        u_power = instance.u1_pow53[j]
        if kind == "A":
            u_power = u_power * instance.u1_values[j] % P
        values[j] = values[j] * scalar % P * u_power % P
    return values


def output_values_to_polynomial(
    values: Sequence[int], kind: str, instance: TargetInstance
) -> list[int]:
    if len(values) != N:
        raise ValueError("a target output vector must have exactly N entries")
    inv_scalar = pow(output_scalar(kind), P - 2, P)
    coefficients = [0] * N
    for j, raw_value in enumerate(values):
        inverse_u_power = instance.u1_pow53_inverse[j]
        if kind == "A":
            inverse_u_power = inverse_u_power * instance.u1_inverse[j] % P
        coefficients[j] = int(raw_value) % P * inv_scalar % P * inverse_u_power % P
    ntt(coefficients, inverse=True)
    return coefficients


def forward_operator(
    coefficient_streams: Sequence[Sequence[int]], instance: TargetInstance
) -> OutputVectors:
    """Apply the 11-input/33-output coupled principal charge-13 block."""
    outputs: OutputVectors = {}
    for kind in ("A", "B", "C"):
        for s, polynomial in enumerate(collision_polynomials(coefficient_streams, kind)):
            if any(polynomial):
                outputs[(kind, s)] = polynomial_to_output_values(
                    polynomial, kind, instance
                )
    return outputs


def strict_window_dual(
    s: int,
    frequency: int,
    a_values: Sequence[int],
    coefficient: int,
    instance: TargetInstance,
) -> dict[str, object]:
    """Build and directly pair the A-channel Fourier tail functional."""
    inv_n = pow(N, P - 2, P)
    inv_a = pow(A_SCALAR, P - 2, P)
    omega_minus_k = pow(instance.omega, (-frequency) % N, P)
    phase = 1
    pairing = 0
    for j in range(N):
        inverse_u54 = (
            instance.u1_pow53_inverse[j] * instance.u1_inverse[j] % P
        )
        weight = inv_n * phase % P * inv_a % P * inverse_u54 % P
        pairing = (pairing + weight * (int(a_values[j]) % P)) % P
        phase = phase * omega_minus_k % P
    if pairing != coefficient or pairing == 0:
        raise AssertionError("A Fourier-tail transpose certificate failed")
    return {
        "verdict": "DUAL",
        "dual_kind": "A_strict_window_fourier_tail",
        "stream": s,
        "frequency": frequency,
        "window": [0, source_width(s)],
        "support": "all nodes of A stream s",
        "weight_at_node_j": (
            "N^-1*omega^(-j*frequency)*"
            "(A_SCALAR*U1(omega^j)^54)^-1"
        ),
        "pairing": pairing,
        "annihilates_every_legal_coupled_input_column": True,
    }


def solve_principal_operator(
    outputs: OutputVectors, instance: TargetInstance
) -> dict[str, object]:
    """Return an exact coupled M13 primal or explicit transposed Schur dual."""
    for (kind, s), values in outputs.items():
        if kind not in ("A", "B", "C") or not 0 <= s < STREAMS:
            raise ValueError(f"invalid output channel {(kind, s)}")
        if len(values) != N:
            raise ValueError(f"channel {(kind, s)} does not have N values")

    a_polynomials: list[list[int]] = []
    for s in range(STREAMS):
        width = source_width(s)
        a_values = outputs.get(("A", s))
        if a_values is None:
            a_polynomials.append([0] * width)
            continue
        coefficients = output_values_to_polynomial(a_values, "A", instance)
        first_tail = next((k for k in range(width, N) if coefficients[k]), None)
        if first_tail is not None:
            return strict_window_dual(
                s, first_tail, a_values, coefficients[first_tail], instance
            )
        a_polynomials.append(coefficients[:width])

    coefficient_streams = invert_a_collision(a_polynomials)

    # A is an invertible tapered upper-unitriangular block.  Compare the two
    # remaining correlated families against the unique A-derived primal.  A
    # mismatch is separated by the explicit Schur functional
    #   e^T (projection_kind - M_kind M_A^{-1} projection_A).
    for kind in ("B", "C"):
        predicted_polynomials = collision_polynomials(coefficient_streams, kind)
        for s, polynomial in enumerate(predicted_polynomials):
            observed = outputs.get((kind, s))
            if observed is None and not any(polynomial):
                continue
            predicted = polynomial_to_output_values(polynomial, kind, instance)
            if observed is None:
                mismatch = next(j for j, value in enumerate(predicted) if value)
                observed_value = 0
            else:
                mismatch = next(
                    (j for j in range(N) if int(observed[j]) % P != predicted[j]),
                    None,
                )
                if mismatch is None:
                    continue
                observed_value = int(observed[mismatch]) % P
            pairing = (observed_value - predicted[mismatch]) % P
            if pairing == 0:
                raise AssertionError("zero Schur pairing at recorded mismatch")
            return {
                "verdict": "DUAL",
                "dual_kind": f"{kind}_after_A_transposed_Schur",
                "stream": s,
                "node_index": mismatch,
                "node": instance.omega_powers[mismatch],
                "pairing": pairing,
                "functional": (
                    f"e_({kind},{s},{mismatch})^T * "
                    f"(projection_{kind} - M_{kind}*M_A^-1*projection_A)"
                ),
                "M_A_inverse": (
                    "unscale A; inverse target NTT; enforce each strict window; "
                    "back-substitute c_s=dA_s+2*Hasse_1(c_(s+1))"
                ),
                "annihilates_every_legal_coupled_input_column": True,
                "independently_replayed_predicted_value": predicted[mismatch],
            }

    return {
        "verdict": "PRIMAL",
        "streams": [
            {
                "stream": s,
                "window": [0, source_width(s)],
                "degree": next(
                    (
                        k
                        for k in range(source_width(s) - 1, -1, -1)
                        if coefficient_streams[s][k]
                    ),
                    -1,
                ),
                "nonzero_coefficients": sum(value != 0 for value in coefficient_streams[s]),
                "coefficients_u32_le_sha256": sha256_u32(coefficient_streams[s]),
            }
            for s in range(STREAMS)
        ],
        "coefficients": coefficient_streams,
        "literal_33_channel_replay_green": True,
    }


def solve_four_reduced_residues(
    residues: dict[str, OutputVectors], instance: TargetInstance
) -> dict[str, object]:
    """Run the identical coupled path for the four exact reduced packets."""
    if set(residues) != set(PACKETS):
        raise ValueError(f"residue labels must be exactly {PACKETS}")
    return {
        packet: solve_principal_operator(residues[packet], instance)
        for packet in PACKETS
    }


def matrix_manifest(instance: TargetInstance) -> dict[str, object]:
    streams = []
    outputs = []
    for s in range(STREAMS):
        streams.append(
            {
                "stream": s,
                "origin_YRSZ": list(origin(s)),
                "coefficient_window": [0, source_width(s)],
                "dimension": source_width(s),
            }
        )
        for kind in ("A", "B", "C"):
            collision_formula = {
                "A": "dA_s=c_s-2*Hasse_1(c_(s+1))",
                "B": (
                    "dB_s=c_s-6*Hasse_1(c_(s+1))+"
                    "12*Hasse_2(c_(s+2))-8*Hasse_3(c_(s+3))"
                ),
                "C": "dC_s=c_s-Hasse_1(c_(s+1))",
            }[kind]
            outputs.append(
                {
                    "stream": s,
                    "kind": kind,
                    "row_TERSZ": list(top_row(kind, s)),
                    "scalar": output_scalar(kind),
                    "U1_exponent": u1_exponent(kind),
                    "same_row_positive_Hasse_collision": collision_formula,
                    "operator": (
                        f"y[{kind},{s},j] = {output_scalar(kind)} "
                        f"* U1(omega^j)^{u1_exponent(kind)} "
                        f"* eval_at_omega^j(d{kind}_{s})"
                    ),
                }
            )

    principal_provenance_count = sum(
        1
        for kind in ("A", "B", "C")
        for s in range(STREAMS)
        for offset, _scalar in COLLISION_TERMS[kind]
        if s + offset < STREAMS
    )
    if principal_provenance_count != 80:
        raise AssertionError("principal provenance count changed")

    return {
        "gate": "full187_target_charge13_transposed_four_residue",
        "status": "M13_PRINCIPAL_READY_NONPRINCIPAL_RLT13_BLOCKED",
        "field": P,
        "target": {
            "N": N,
            "omega": instance.omega,
            "G_first_nodes": G,
            "E_last_nodes": E,
            "H_first_G_nodes": H,
            "w": W,
            "m": M,
            "D": D,
            "q": Q_CONTACT,
            "t": T_BOUND,
            "J": J_BOUND,
            "L": L_BOUND,
            "error_word_on_E": "delta(X)=X^81730",
            "error_offset_interpolant_degree": E - 1,
            "error_offset_interpolant_degree_checked_exact": True,
            "U0": "0 on G, 1 on E",
            "gamma": GAMMA,
            "P_coefficients": [0],
            "Q": "Xi_E^2",
            "q_H": "Q mod Xi_H",
            "degree_Q": 2 * E,
            "degree_q_H": len(instance.qh_coefficients) - 1,
            "no_degree_le_w_all_node_direction": True,
            "hashes": instance.hashes,
        },
        "matrix": {
            "representation": (
                "matrix-free tapered Hasse-collision plus NTT-diagonal "
                "principal block"
            ),
            "charge": CHARGE,
            "physical_stream_count": STREAMS,
            "correlated_output_count": len(outputs),
            "column_dimension": sum(source_width(s) for s in range(STREAMS)),
            "ambient_row_dimension": len(outputs) * N,
            "streams": streams,
            "outputs": outputs,
            "collision_contract": {
                "A": "sum_j=0^1 binom(1,j)(-2)^j Hasse_j(c_(s+j))",
                "B": "sum_j=0^3 binom(3,j)(-2)^j Hasse_j(c_(s+j))",
                "C": "sum_j=0^1 (-1)^j Hasse_j(c_(s+j))",
                "upper_boundary": "c_s=0 for s>10",
                "taper_identity": "width(s+j)-j=width(s)",
                "each_family_upper_unitriangular": True,
                "q0_heads_positive_Hasse_collisions_total": [33, 47, 80],
                "warning": (
                    "B is an explicit Hasse-binomial operator, not a "
                    "composition power of 1-2*Hasse_1"
                ),
            },
            "scalar_checks": {
                "C_equals_54A_mod_p": (C_SCALAR - 54 * A_SCALAR) % P == 0,
                "4B_equals_C_mod_p": (4 * B_SCALAR - C_SCALAR) % P == 0,
            },
            "transpose_certificates": [
                "A_strict_window_fourier_tail",
                "B_after_A_transposed_Schur",
                "C_after_A_transposed_Schur",
            ],
        },
        "complete_raw_contact_scope_guard": {
            "principal_33_rows_are_not_a_subcomplex": True,
            "structured_q0_origins_across_charges_0_through_13": 72_850,
            "structured_collision_receipt": (
                ".experiments/full187_terminal_hasse_collision_blocks_6900.py"
            ),
            "structured_collision_canonical_sha256_at_integration": (
                "f7e2e7022ec6c2aabc569a254714feefe7b9bcc937d0c91aa0e48ad1625cda76"
            ),
            "fully_expanded_provenance_total": 48_516_523,
            "principal_provenance_total": principal_provenance_count,
            "nonprincipal_provenance_total": 48_516_523 - principal_provenance_count,
            "distinct_all_grade_row_shapes_per_node": 10_011_293,
            "complete_transpose_equation": (
                "for every source t=0..10 and a<76979+t, sum over all nodes "
                "and f,h,aE,cS,q with q+f+2aE+cS<60 of "
                "lambda[node,row]*binom(61,f)*binom(61-f,h)*"
                "multinomial(f;aE,cS,*)*(-1/2)^cS*"
                "U0(node)^(61-f-h)*U1(node)^h*binom(a,q)*"
                "node^(a-q) equals zero"
            ),
            "raw_schema_receipt": (
                ".experiments/full187_charge13_transpose_interface_spec_6900.py"
            ),
            "raw_schema_canonical_sha256_at_integration": (
                "28bc1b68d416740d0d8532b2f651e5fe44edaaf6d8a58f343f58a6475a2748ca"
            ),
        },
        "four_residues": {
            "labels": list(PACKETS),
            "generic_reduced_column_interface": True,
            "pure_Z1_is_not_a_packet": True,
            "first_three": (
                "the exact centered Lambda_G locator packets F0,F1,F2, "
                "including every scalar and -(Z-gamma)Q tail"
            ),
            "F3": {
                "formula": "B*(Y-P-(Z-gamma)*q_H)",
                "specialized_formula": "Xi_H^59*Xi_R^60*(Y-Z*q_H)",
                "B": "Xi_H^59*Xi_R^60",
                "R_nodes": [H, G],
                "degree_B": 60 * G - H,
                "degree_Bq_H_upper_bound": D - 1,
                "boundary_representation": {
                    "Y_coefficient": "B (factored)",
                    "Z_coefficient": "-B*q_H (factored)",
                    "scalar_coefficient": "0",
                },
                "literal_error_contact_syndrome": (
                    "at x in E: trunc_<60 C(B(x+T))*"
                    "(C(contactY+1) + C(U1(x)-q_H(x)-"
                    "(q_H(x+T)-q_H(x)))*Zseed)"
                ),
                "selected_seed_scalar_on_E": "B(x)",
                "selected_seed_scalar_nonzero_at_every_error": True,
                "selected_seed_scalar_hash": instance.hashes[
                    "F3_selected_error_syndrome_on_E_u32_le"
                ],
                "extractability": (
                    "GREEN in exact factored/local-translation form; expansion "
                    "through the lower-charge quotient is not yet available"
                ),
            },
        },
        "required_missing_input": {
            "name": "Rlt13(F0), Rlt13(F1), Rlt13(F2), Rlt13(F3)",
            "shape": "four families of 33 vectors in F_p^N",
            "contract": (
                "coefficientwise normal forms after every charge<13 agreement-"
                "Hermite and sharp contact eliminator, with positive-Hasse/pivot "
                "tails, origin provenance, passive grade, and the exact F3 "
                "error-contact syndrome retained"
            ),
            "why_not_available": (
                "the exact target census records heads and local pivot counts, but "
                "does not define a polynomial-module reduction map or its tail "
                "witnesses; the order-2 closure experiment shows that head-only "
                "pivot reduction is not closed"
            ),
            "nonprincipal_tail_interface": (
                "for every physical c_s column, supply all output rows outside "
                "the 33 same-row heads after certified lower-charge reduction; "
                "the present principal solve is not a certificate against those "
                "rows until this interface is populated"
            ),
            "certificate_scope_guard": (
                "PRIMAL/DUAL exits from solve_principal_operator certify the "
                "coupled 33-row principal quotient only. They become full gate "
                "certificates only after the nonprincipal and prior-source "
                "transpose equations above are supplied and replayed."
            ),
            "only_possible_kernel_mechanism": (
                "cross-origin and/or multi-grade quotient cancellation at the "
                "final passive grade; the isolated 11-stream block is injective"
            ),
        },
        "build": {
            "seconds": round(instance.build_seconds, 3),
            "max_rss_mib": round(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024, 3),
        },
    }


def run_target_self_check(instance: TargetInstance) -> dict[str, object]:
    """Exercise coupled primal and both dual exits at actual p and N."""
    coefficient_streams: list[list[int]] = [[] for _ in range(STREAMS)]
    # Stream 3 forces Hasse collisions into lower A/B/C rows and distinguishes
    # Hasse_2/Hasse_3 from iterated Hasse_1.
    coefficient_streams[3] = [5, 7, 11, 13]
    normalized_streams = [
        [int(value) % P for value in coefficient_streams[s]]
        + [0] * (source_width(s) - len(coefficient_streams[s]))
        for s in range(STREAMS)
    ]
    inverse_checks = {}
    for kind in ("A", "B", "C"):
        recovered = invert_collision(
            collision_polynomials(coefficient_streams, kind), kind
        )
        inverse_checks[kind] = recovered == normalized_streams
    if not all(inverse_checks.values()):
        raise AssertionError("a tapered collision family was not invertible")
    outputs = forward_operator(coefficient_streams, instance)
    primal = solve_principal_operator(outputs, instance)
    if (
        primal["verdict"] != "PRIMAL"
        or primal["streams"][3]["degree"] != 3
        or not primal["literal_33_channel_replay_green"]
    ):
        raise AssertionError("actual-target primal self-check failed")
    primal.pop("coefficients")

    broken_outputs = dict(outputs)
    broken_key = ("B", 0)
    broken_values = broken_outputs[broken_key].copy()
    broken_values[G] = (broken_values[G] + 1) % P
    broken_outputs[broken_key] = broken_values
    schur_dual = solve_principal_operator(broken_outputs, instance)
    if schur_dual.get("dual_kind") != "B_after_A_transposed_Schur":
        raise AssertionError("actual-target transposed-Schur self-check failed")

    s = 0
    illegal_a_polynomial = [0] * (source_width(s) + 1)
    illegal_a_polynomial[source_width(s)] = 1
    illegal_a_values = polynomial_to_output_values(
        illegal_a_polynomial, "A", instance
    )
    tail_dual = solve_principal_operator({("A", s): illegal_a_values}, instance)
    if (
        tail_dual.get("dual_kind") != "A_strict_window_fourier_tail"
        or tail_dual.get("frequency") != source_width(s)
    ):
        raise AssertionError("actual-target Fourier-tail self-check failed")

    del outputs, broken_outputs, broken_values, illegal_a_values
    gc.collect()

    return {
        "field": P,
        "domain": N,
        "all_three_tapered_collision_inverses": inverse_checks,
        "primal": primal,
        "transposed_schur_dual": schur_dual,
        "tail_dual": tail_dual,
        "all_green": True,
        "max_rss_mib": round(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024, 3),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--self-check-target-operator",
        action="store_true",
        help="run actual-p, actual-N primal and both transpose-dual paths",
    )
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()

    instance = build_target_instance(verbose=args.verbose)
    result: dict[str, object] = {"manifest": matrix_manifest(instance)}
    if args.self_check_target_operator:
        result["target_operator_self_check"] = run_target_self_check(instance)
        result["manifest"]["build"]["max_rss_mib"] = round(
            resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024, 3
        )
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
