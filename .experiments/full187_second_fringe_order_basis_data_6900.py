#!/usr/bin/env python3
"""Generate the exact C=1 top-stream second-fringe Padé instance."""

from __future__ import annotations

from math import comb
from pathlib import Path
import argparse
import hashlib
import json
import resource
import struct
import sys

from flint import nmod_poly

sys.path.insert(0, str(Path(__file__).resolve().parent))
import full187_target_charge13_transposed_four_residue_gate_6900 as T


P = 2_130_706_433
N = 262_144
HALF = N // 2
A = 208_058
B = 76_987
C = 76_985
OUT = Path("/tmp/full187_second_fringe_order_basis_data_6900.bin")
BASIS = Path("/tmp/full187_second_fringe_order_basis_certificate_6900.bin")


def omega_digits(poly, omega, count):
    ans = []
    for _ in range(count):
        poly, rem = divmod(poly, omega)
        ans.append(rem)
    return ans


def coeffs(poly, length):
    return [int(poly[i]) for i in range(length)]


def sha_u32(values):
    h = hashlib.sha256()
    for start in range(0, len(values), 16384):
        chunk = values[start:start + 16384]
        h.update(struct.pack(f"<{len(chunk)}I", *chunk))
    return h.hexdigest()


def verify_basis():
    with OUT.open("rb") as stream:
        magic, p, n, order, a, b, c, threshold, count = struct.unpack(
            "<8s8I", stream.read(40))
        assert magic == b"F187SF2\0" and (p, n, order, a, b, c) == (
            P, N, HALF, A, B, C)
        series_data = [list(struct.unpack(
            f"<{order}I", stream.read(4 * order))) for _ in range(count)]
    with BASIS.open("rb") as stream:
        magic, p2, order2, size = struct.unpack("<8s3I", stream.read(20))
        assert magic == b"F187SFB\0" and (p2, order2) == (P, HALF)
        initial_shift = struct.unpack("<4I", stream.read(16))
        final_shift = struct.unpack("<4I", stream.read(16))
        raw = struct.unpack(f"<{16 * size}I", stream.read(4 * 16 * size))
        assert not stream.read(1)
    basis = [[None] * 4 for _ in range(4)]
    at = 0
    for i in range(4):
        for j in range(4):
            basis[i][j] = nmod_poly(list(raw[at:at + size]), P)
            at += size
    series = [
        [nmod_poly(series_data[0], P), nmod_poly(series_data[1], P)],
        [nmod_poly([1], P), nmod_poly([], P)],
        [nmod_poly([], P), nmod_poly([1], P)],
        [-nmod_poly(series_data[2], P), -nmod_poly(series_data[3], P)],
    ]
    zero_checks = 0
    for i in range(4):
        for k in range(2):
            product = sum((basis[i][j] * series[j][k]
                           for j in range(4)), nmod_poly([], P))
            assert not product.truncate(HALF)
            zero_checks += 1
    actual_final = tuple(max(
        (basis[i][j].degree() + initial_shift[j] for j in range(4)),
        default=-1) for i in range(4))
    assert actual_final == final_shift
    assert sum(final_shift) - sum(initial_shift) == 2 * HALF
    assert min(final_shift) > threshold

    lead = [[int(basis[i][j][final_shift[i] - initial_shift[j]])
             if final_shift[i] >= initial_shift[j] else 0
             for j in range(4)] for i in range(4)]
    det = 1
    for col in range(4):
        pivot = next(i for i in range(col, 4) if lead[i][col])
        if pivot != col:
            lead[col], lead[pivot] = lead[pivot], lead[col]
            det = -det % P
        pv = lead[col][col]
        det = det * pv % P
        inv = pow(pv, -1, P)
        for row in range(col + 1, 4):
            factor = lead[row][col] * inv % P
            lead[row] = [(x - factor * y) % P
                         for x, y in zip(lead[row], lead[col])]
    assert det
    print(json.dumps({
        "basis_file": str(BASIS),
        "basis_file_bytes": BASIS.stat().st_size,
        "basis_sha256": hashlib.sha256(BASIS.read_bytes()).hexdigest(),
        "initial_shift": initial_shift,
        "final_shift": final_shift,
        "threshold": threshold,
        "minimum_shifted_degree_gap": min(final_shift) - threshold,
        "shift_gain_equals_two_orders": sum(final_shift) - sum(initial_shift),
        "shift_leading_determinant": det,
        "approximant_zero_checks": zero_checks,
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "decision": "CERTIFIED_STOP_C1_NO_BOUNDED_SECOND_FRINGE_LIFT",
    }, indent=2, sort_keys=True))


def generate():
    instance = T.build_target_instance()
    ucoeff = instance.u1_values.copy()
    T.ntt(ucoeff, inverse=True)
    U = nmod_poly(ucoeff, P)
    omega = nmod_poly([-1] + [0] * (N - 1) + [1], P)
    U2 = U * U
    U3 = U2 * U
    U4 = U2 * U2

    c59 = comb(61, 59) % P
    c58 = comb(61, 58) % P
    c57 = comb(61, 57) % P
    c5957 = comb(59, 57) % P

    p59 = -(c59 * omega_digits(U2, omega, 1)[0])
    x58 = c58 * U3 + 59 * U * p59
    p58 = -omega_digits(x58, omega, 1)[0]
    b58 = x58 + p58
    d58 = omega_digits(b58, omega, 2)
    assert not d58[0]
    t1 = -d58[1]

    x57 = c57 * U4 + 58 * U * p58 + c5957 * U2 * p59
    d57 = omega_digits(x57, omega, 3)
    p57 = -(d57[0] + omega * d57[1])
    b57 = x57 + p57
    db57 = omega_digits(b57, omega, 3)
    assert not db57[0] and not db57[1]
    t2 = -db57[2]

    inv59 = pow(59, -1, P)
    inv1711 = pow(c5957, -1, P)

    # Reverse U at its exact degree N-1 and invert it as a power series.
    ustar = nmod_poly(list(reversed(ucoeff)), P).truncate(HALF)
    vstar = ustar.inverse_series_trunc(HALF)

    # First-fringe prescribed middle product M=(U*B)[A..N).
    mstar_values = [0] * HALF
    morig_values = [0] * N
    for i in range(A, N):
        value = int(t1[i]) * inv59 % P
        morig_values[i] = value
        k = N + B - 2 - i
        assert B - 1 <= k < HALF
        mstar_values[k] = value
    mstar = nmod_poly(mstar_values, P)
    atarget = -(vstar * mstar).truncate(HALF)

    # On j=A-1..N-1 the U*A term vanishes.  The second equation is the
    # middle window of U*K, where K is the high carry of U*B.
    fixed = U * nmod_poly(morig_values, P)
    btarget_values = [0] * HALF
    for j in range(A - 1, N):
        fixed_value = int(fixed[N + j]) if N + j < len(fixed) else 0
        value = (int(t2[j]) * inv1711 - fixed_value) % P
        k = N + B - 3 - j
        assert B - 2 <= k < HALF
        btarget_values[k] = value

    arrays = (
        coeffs(ustar, HALF),
        coeffs(vstar, HALF),
        btarget_values,
        coeffs(atarget, HALF),
    )
    with OUT.open("wb") as stream:
        stream.write(struct.pack("<8s8I", b"F187SF2\0", P, N, HALF,
                                 A, B, C, B - 1, len(arrays)))
        for array in arrays:
            stream.write(struct.pack(f"<{len(array)}I", *array))

    receipt = {
        "output": str(OUT),
        "output_bytes": OUT.stat().st_size,
        "p_N_half_A_B_C": (P, N, HALF, A, B, C),
        "constants_c59_c58_c57_c5957": (c59, c58, c57, c5957),
        "canonical_low_degrees_P59_P58_P57":
            (p59.degree(), p58.degree(), p57.degree()),
        "target_degrees_t1_t2": (t1.degree(), t2.degree()),
        "array_sha256_u32": tuple(sha_u32(x) for x in arrays),
        "binary_sha256": hashlib.sha256(OUT.read_bytes()).hexdigest(),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--verify-basis", action="store_true")
    args = parser.parse_args()
    verify_basis() if args.verify_basis else generate()
