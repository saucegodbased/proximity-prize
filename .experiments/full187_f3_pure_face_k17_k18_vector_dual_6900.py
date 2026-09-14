#!/usr/bin/env python3
"""Exact structured k=17/k=18 vector-dual gate for the Full187 F3 face.

This companion experiment starts from the 41,999-variable reduction in
``full187_f3_pure_face_graph_transform_6900.py``.  It constructs the literal
target modulus and the two modular multiplication operators.  The first mode
only probes the displacement structure of the remaining map; later modes emit
the compact simultaneous-approximant instance and verify its certificate.
"""

from __future__ import annotations

import argparse
from array import array
import hashlib
import json
from pathlib import Path
import resource
import struct
import sys

from flint import nmod_poly

sys.path.insert(0, str(Path(__file__).resolve().parent))
import full187_target_charge13_transposed_four_residue_gate_6900 as T


P = T.P
E_DEG = T.E
M_DEG = 18 * E_DEG
R_WIDTH = 40_240
Z_WIDTH = 1_759
OUT_ROWS = 98_684
LOW_BOUND = M_DEG - OUT_ROWS
A1 = 931_238_467
A2 = 95_217_577
DATA = Path("/tmp/full187_f3_pure_face_k17_k18_vector_dual_6900.bin")
BASIS = Path(
    "/tmp/full187_f3_pure_face_k17_k18_vector_dual_basis_6900.bin")


def sha_u32(values):
    h = hashlib.sha256()
    for start in range(0, len(values), 16384):
        chunk = values[start:start + 16384]
        h.update(struct.pack(f"<{len(chunk)}I", *chunk))
    return h.hexdigest()


def target_operators():
    instance = T.build_target_instance()
    h = nmod_poly(instance.xi_h_coefficients, P)
    rloc = nmod_poly(instance.xi_r_coefficients, P)
    e = nmod_poly(instance.xi_e_coefficients, P)
    g = h * rloc
    modulus = e ** 18
    u = g.pow_mod(58, modulus)
    g31 = g.pow_mod(31, modulus)
    gcd, v, _ = g31.xgcd(modulus)
    assert gcd == nmod_poly([1], P)
    v %= modulus
    assert (g31 * v) % modulus == nmod_poly([1], P)
    assert modulus.degree() == M_DEG
    return e, g, modulus, u, v


def coefficients(poly, length):
    return [int(poly[i]) for i in range(length)]


def exact_kernel_series():
    """Return the six nonzero entries of the reciprocal 4x2 system."""
    p18 = lambda n: __import__("math").prod(
        (n - root) % P for root in range(30, 72)) % P
    c18q, c18a = p18(2), p18(72)
    c17q, c17a = (2 - 29) * c18q % P, (72 - 29) * c18a % P
    assert (c17q, c17a, c18q, c18a, p18(29)) == (
        842_546_268, 1_616_860_076, 1_389_265_538,
        1_276_384_207, 1_276_384_207)
    assert c17q * pow(c17a, -1, P) % P == A1
    assert c18q * pow(c18a, -1, P) % P == A2
    assert (A1 - A2) % P == 836_020_890
    instance = T.build_target_instance()
    h = nmod_poly(instance.xi_h_coefficients, P)
    rloc = nmod_poly(instance.xi_r_coefficients, P)
    e = nmod_poly(instance.xi_e_coefficients, P)
    g = h * rloc
    modulus = e ** 18
    g31e = g.pow_mod(31, e)
    u58 = g.pow_mod(58, modulus)
    eg27 = (e * g.pow_mod(27, modulus)) % modulus
    eg58 = (e * u58) % modulus

    # Reverse at the exact ambient product degrees.  The first equality only
    # asks that its remainder have degree<R_WIDTH, giving order
    # 2*E_DEG-R_WIDTH.  The second asks that its E^18 remainder have degree
    # <LOW_BOUND, giving order E_DEG+OUT_ROWS.  Shift the first column by the
    # order difference to use one ordinary PM-basis call.
    order1 = 2 * E_DEG - R_WIDTH
    order2 = E_DEG + OUT_ROWS
    column_shift = order2 - order1
    assert (order1, order2, column_shift) == (123_222, 180_415, 57_193)
    g31star = g31e.reverse(degree=E_DEG - 1)
    estar = e.reverse(degree=E_DEG)
    u58star = u58.reverse(degree=M_DEG - 1)
    eg27star = eg27.reverse(degree=M_DEG - 1)
    eg58star = eg58.reverse(degree=M_DEG - 1)
    mstar = modulus.reverse(degree=M_DEG)

    # Exact orientation audit on sparse non-palindromic test polynomials.
    ty = nmod_poly([3, 5], P)
    tc = nmod_poly([7, 11], P)
    tz = nmod_poly([13, 17], P)
    ts = nmod_poly([19, 23], P)
    ty_star = ty.reverse(degree=E_DEG - 1)
    tc_star = tc.reverse(degree=E_DEG - 1)
    tz_star = tz.reverse(degree=Z_WIDTH - 1)
    ts_star = ts.reverse(degree=E_DEG - 1)
    direct1 = g31e * ty - e * tc
    reverse1 = (g31star.left_shift(1) * ty_star - estar * tc_star)
    assert reverse1 == direct1.reverse(degree=2 * E_DEG - 1)
    direct2 = (A2 * u58 * ty + (A1 - A2) * eg27 * tc
               + A1 * eg58 * tz - modulus * ts)
    reverse2 = (
        A2 * u58star.left_shift(1) * ty_star
        + (A1 - A2) * eg27star.left_shift(1) * tc_star
        + A1 * eg58star.left_shift(E_DEG - Z_WIDTH + 1) * tz_star
        - mstar * ts_star)
    assert reverse2 == direct2.reverse(degree=M_DEG + E_DEG - 1)
    arrays = (
        g31star.left_shift(column_shift + 1).truncate(order2),
        -estar.left_shift(column_shift).truncate(order2),
        (A2 * u58star.left_shift(1)).truncate(order2),
        ((A1 - A2) * eg27star.left_shift(1)).truncate(order2),
        (A1 * eg58star.left_shift(E_DEG - Z_WIDTH + 1)).truncate(order2),
        -mstar.truncate(order2),
    )
    # Variables are fixed-length reversals (Y,C,Z,S).
    bounds = (E_DEG, E_DEG, Z_WIDTH, E_DEG)
    threshold = E_DEG - 1
    shifts = tuple(threshold - (bound - 1) for bound in bounds)
    assert shifts == (0, 0, 79_972, 0)
    assert all(poly.degree() < order2 for poly in arrays)
    return arrays, bounds, shifts, order2, threshold, order1, column_shift


def generate():
    arrays, bounds, shifts, order, threshold, order1, column_shift = (
        exact_kernel_series())
    with DATA.open("wb") as stream:
        stream.write(struct.pack(
            "<8s12I", b"F3K4X2D", P, E_DEG, M_DEG, R_WIDTH,
            Z_WIDTH, OUT_ROWS, LOW_BOUND, order, threshold,
            len(arrays), len(bounds), column_shift))
        stream.write(struct.pack(f"<{len(bounds)}I", *bounds))
        stream.write(struct.pack(f"<{len(shifts)}I", *shifts))
        for poly in arrays:
            values = coefficients(poly, order)
            stream.write(struct.pack(f"<{len(values)}I", *values))
    print(json.dumps({
        "output": str(DATA),
        "output_bytes": DATA.stat().st_size,
        "p_Edeg_Mdeg_rWidth_zWidth_outRows_lowBound": (
            P, E_DEG, M_DEG, R_WIDTH, Z_WIDTH, OUT_ROWS, LOW_BOUND),
        "bounds_reversed_Y_C_Z_S": bounds,
        "initial_shifts": shifts,
        "effective_orders_columnShift_threshold": (
            order1, order, column_shift, threshold),
        "array_degrees": tuple(poly.degree() for poly in arrays),
        "array_sha256_u32": tuple(
            sha_u32(coefficients(poly, order)) for poly in arrays),
        "binary_sha256": hashlib.sha256(DATA.read_bytes()).hexdigest(),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "decision": "GENERATED_EXACT_RECIPROCAL_4_BY_2_PM_INSTANCE",
    }, indent=2, sort_keys=True))


def read_u32_poly(stream, length):
    raw = array("I")
    raw.fromfile(stream, length)
    if sys.byteorder != "little":
        raw.byteswap()
    assert len(raw) == length
    return nmod_poly(list(raw), P)


def verify_basis():
    """Independently verify every PM-basis product and degree certificate."""
    with DATA.open("rb") as stream:
        header = struct.unpack("<8s12I", stream.read(56))
        magic, p, edeg, mdeg, rwidth, zwidth, outrows, lowbound, order, \
            threshold, count, bound_count, column_shift = header
        assert magic == b"F3K4X2D\0"
        assert (p, edeg, mdeg, rwidth, zwidth, outrows, lowbound) == (
            P, E_DEG, M_DEG, R_WIDTH, Z_WIDTH, OUT_ROWS, LOW_BOUND)
        assert (count, bound_count, column_shift) == (6, 4, 57_193)
        bounds = struct.unpack("<4I", stream.read(16))
        initial_shift = struct.unpack("<4I", stream.read(16))
        arrays = [read_u32_poly(stream, order) for _ in range(6)]
        assert not stream.read(1)
    zero = nmod_poly([], P)
    series = (
        (arrays[0], arrays[2]),
        (arrays[1], arrays[3]),
        (zero, arrays[4]),
        (zero, arrays[5]),
    )

    with BASIS.open("rb") as stream:
        magic2, p2, order2, size = struct.unpack("<8s3I", stream.read(20))
        assert magic2 == b"F3K4X2B\0"
        assert (p2, order2) == (P, order)
        initial2 = struct.unpack("<4I", stream.read(16))
        final_shift = struct.unpack("<4I", stream.read(16))
        assert initial2 == initial_shift
        actual_final = []
        lead = [[0] * 4 for _ in range(4)]
        zero_checks = 0
        component_degrees = []
        for i in range(4):
            row = [read_u32_poly(stream, size) for _ in range(4)]
            degrees = tuple(poly.degree() for poly in row)
            component_degrees.append(degrees)
            shifted_degree = max(
                (degree + initial_shift[j]
                 for j, degree in enumerate(degrees) if degree >= 0),
                default=-1)
            actual_final.append(shifted_degree)
            for j, poly in enumerate(row):
                k = final_shift[i] - initial_shift[j]
                lead[i][j] = int(poly[k]) if 0 <= k < size else 0
            for col in range(2):
                product = sum(
                    (row[j] * series[j][col] for j in range(4)), zero)
                assert not product.truncate(order)
                zero_checks += 1
            del row
        assert not stream.read(1)

    assert tuple(actual_final) == final_shift
    effective_degree = 2 * order - column_shift
    assert sum(final_shift) - sum(initial_shift) == effective_degree
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
            lead[row] = [
                (x - factor * y) % P
                for x, y in zip(lead[row], lead[col])]
    assert det
    found = min(final_shift) <= threshold
    print(json.dumps({
        "basis_file": str(BASIS),
        "basis_file_bytes": BASIS.stat().st_size,
        "basis_sha256": hashlib.sha256(BASIS.read_bytes()).hexdigest(),
        "bounds_reversed_Y_C_Z_S": bounds,
        "initial_shift": initial_shift,
        "final_shift": final_shift,
        "component_degrees": component_degrees,
        "threshold": threshold,
        "minimum_shifted_degree_gap": min(final_shift) - threshold,
        "column_orders_and_shift_gain": (
            order-column_shift, order,
            sum(final_shift)-sum(initial_shift)),
        "shift_leading_determinant": det,
        "approximant_zero_checks": zero_checks,
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "decision": (
            "RED_NONZERO_COUPLED_VECTOR_DUAL" if found else
            "CERTIFIED_GREEN_COUPLED_VECTOR_DUAL_INJECTIVE"),
    }, indent=2, sort_keys=True))


def tail(poly):
    return tuple(int(poly[i]) for i in range(LOW_BOUND, M_DEG))


def r_column(j, e, modulus, u, v):
    y = v.left_shift(j) % modulus
    y0 = y % e
    gq = A1 * y0 + (A2 - A1) * y
    return tail((u * gq) % modulus)


def z_column(j, e, modulus, u):
    gq = A1 * e.left_shift(j)
    return tail((u * gq) % modulus)


def shifted_equal(a, b, direction):
    if direction == "down":
        return a[1:] == b[:-1]
    if direction == "up":
        return a[:-1] == b[1:]
    raise AssertionError(direction)


def probe():
    e, g, modulus, u, v = target_operators()
    rcols = [r_column(j, e, modulus, u, v) for j in range(3)]
    zcols = [z_column(j, e, modulus, u) for j in range(3)]
    receipt = {
        "p_Edeg_Mdeg_rWidth_zWidth_outRows_lowBound": (
            P, E_DEG, M_DEG, R_WIDTH, Z_WIDTH, OUT_ROWS, LOW_BOUND),
        "degrees_E_G_M_U_Ginv31": (
            e.degree(), g.degree(), modulus.degree(), u.degree(), v.degree()),
        "r_column_sha256_u32": tuple(sha_u32(x) for x in rcols),
        "z_column_sha256_u32": tuple(sha_u32(x) for x in zcols),
        "adjacent_shift_tests": {
            "r_down": tuple(shifted_equal(rcols[j], rcols[j + 1], "down")
                            for j in range(2)),
            "r_up": tuple(shifted_equal(rcols[j], rcols[j + 1], "up")
                          for j in range(2)),
            "z_down": tuple(shifted_equal(zcols[j], zcols[j + 1], "down")
                            for j in range(2)),
            "z_up": tuple(shifted_equal(zcols[j], zcols[j + 1], "up")
                          for j in range(2)),
        },
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "decision": "STRUCTURE_PROBE_ONLY",
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--probe", action="store_true")
    parser.add_argument("--generate", action="store_true")
    parser.add_argument("--verify-basis", action="store_true")
    args = parser.parse_args()
    if args.probe:
        probe()
    elif args.generate:
        generate()
    elif args.verify_basis:
        verify_basis()
    else:
        parser.error("select --probe or --generate")


if __name__ == "__main__":
    main()
