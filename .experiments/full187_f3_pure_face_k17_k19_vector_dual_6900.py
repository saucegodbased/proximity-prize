#!/usr/bin/env python3
"""Exact coupled k=17,18,19 vector-dual gate for the Full187 F3 face."""

from __future__ import annotations

from array import array
import argparse
import hashlib
import json
from math import prod
from pathlib import Path
import resource
import struct
import sys

from flint import nmod_poly

sys.path.insert(0, str(Path(__file__).resolve().parent))
import full187_target_charge13_transposed_four_residue_gate_6900 as T


P = T.P
E_DEG = T.E
R_WIDTH = 40_240
U_WIDTH = 1_759
Z_WIDTH = 34_150
OUT_ROWS = 98_684
M_DEG = 19 * E_DEG
LOW_BOUND = M_DEG - OUT_ROWS
A1 = 931_238_467
A2 = 95_217_577
A3 = 570_758_121
C3 = 558_042_203
DATA = Path("/tmp/full187_f3_pure_face_k17_k19_vector_dual_6900.bin")
BASIS = Path("/tmp/full187_f3_pure_face_k17_k19_vector_dual_basis_6900.bin")


def coeffs(poly, length):
    return [int(poly[i]) for i in range(length)]


def sha_u32(values):
    h = hashlib.sha256()
    for start in range(0, len(values), 16384):
        chunk = values[start:start + 16384]
        h.update(struct.pack(f"<{len(chunk)}I", *chunk))
    return h.hexdigest()


def literal_coefficients():
    p18 = lambda n: prod((n-root) % P for root in range(30, 72)) % P
    p17 = lambda n: (n-29) * p18(n) % P
    p19 = lambda n: ((n-29) * prod(
        (n-root) % P for root in range(31, 71))) % P
    values = (
        p17(2), p17(72), p18(2), p18(29), p18(72),
        p19(2), p19(29), p19(71), p19(72))
    assert values == (
        842_546_268, 1_616_860_076,
        1_389_265_538, 1_276_384_207, 1_276_384_207,
        13_670_302, 0, 1_174_437_213, 1_661_892_046)
    assert p17(2)*pow(p17(72), -1, P) % P == A1
    assert p18(2)*pow(p18(29), -1, P) % P == A2
    assert p19(2)*pow(p19(71), -1, P) % P == A3
    assert p19(72)*pow(p19(71), -1, P) % P == C3
    return values


def exact_reciprocal_series():
    values = literal_coefficients()
    instance = T.build_target_instance()
    h = nmod_poly(instance.xi_h_coefficients, P)
    rloc = nmod_poly(instance.xi_r_coefficients, P)
    e = nmod_poly(instance.xi_e_coefficients, P)
    g = h * rloc
    modulus = e ** 19
    e2 = e * e
    g31e = g.pow_mod(31, e)
    u58 = g.pow_mod(58, modulus)
    eg58 = (e * u58) % modulus
    e2g27 = (e2 * g.pow_mod(27, modulus)) % modulus
    e2g58 = (e2 * u58) % modulus

    # After normalizing the three Euler rows, their coefficients on
    # (A2,A29,A71,A72) are
    #   (A1,0,0,1), (A2,1,0,1), (A3,0,1,C3).
    # With x=E^2*g17,y=E*g18,z=g19, parameterize the A72 condition by
    # gA=E*hbar+C3*z+E^2*u.  Eliminating the 18-adic lift gives the output
    # multiplier below; C3 cancels identically.
    mult_h = (A2 * eg58) % modulus
    mult_c = ((A1 - A2) * e2g27) % modulus
    mult_z = (A3 * u58) % modulus
    mult_u = (A1 * e2g58) % modulus

    order1 = 2 * E_DEG - R_WIDTH
    order2 = E_DEG + OUT_ROWS
    column_shift = order2 - order1
    assert (order1, order2, column_shift) == (123_222, 180_415, 57_193)
    gstar = g31e.reverse(degree=E_DEG - 1)
    estar = e.reverse(degree=E_DEG)
    mhstar = mult_h.reverse(degree=M_DEG - 1)
    mcstar = mult_c.reverse(degree=M_DEG - 1)
    mzstar = mult_z.reverse(degree=M_DEG - 1)
    mustar = mult_u.reverse(degree=M_DEG - 1)
    mstar = modulus.reverse(degree=M_DEG)

    # Exact reversal-orientation audit on non-palindromic sparse values.
    th, tc = nmod_poly([3, 5], P), nmod_poly([7, 11], P)
    tz, tu = nmod_poly([13, 17], P), nmod_poly([19, 23], P)
    ts = nmod_poly([29, 31], P)
    ths = th.reverse(degree=E_DEG - 1)
    tcs = tc.reverse(degree=E_DEG - 1)
    tzs = tz.reverse(degree=Z_WIDTH - 1)
    tus = tu.reverse(degree=U_WIDTH - 1)
    tss = ts.reverse(degree=E_DEG - 1)
    direct1 = g31e*th - e*tc
    reverse1 = gstar.left_shift(1)*ths - estar*tcs
    assert reverse1 == direct1.reverse(degree=2*E_DEG - 1)
    direct2 = mult_h*th + mult_c*tc + mult_z*tz + mult_u*tu - modulus*ts
    reverse2 = (
        mhstar.left_shift(1)*ths + mcstar.left_shift(1)*tcs
        + mzstar.left_shift(E_DEG-Z_WIDTH+1)*tzs
        + mustar.left_shift(E_DEG-U_WIDTH+1)*tus - mstar*tss)
    assert reverse2 == direct2.reverse(degree=M_DEG+E_DEG-1)

    arrays = (
        gstar.left_shift(column_shift+1).truncate(order2),
        -estar.left_shift(column_shift).truncate(order2),
        mhstar.left_shift(1).truncate(order2),
        mcstar.left_shift(1).truncate(order2),
        mzstar.left_shift(E_DEG-Z_WIDTH+1).truncate(order2),
        mustar.left_shift(E_DEG-U_WIDTH+1).truncate(order2),
        -mstar.truncate(order2),
    )
    bounds = (E_DEG, E_DEG, Z_WIDTH, U_WIDTH, E_DEG)
    threshold = E_DEG - 1
    shifts = tuple(threshold-(bound-1) for bound in bounds)
    assert shifts == (0, 0, 47_581, 79_972, 0)
    assert all(poly.degree() < order2 for poly in arrays)
    return (arrays, bounds, shifts, order2, threshold, order1,
            column_shift, values)


def generate():
    arrays, bounds, shifts, order, threshold, order1, column_shift, values = (
        exact_reciprocal_series())
    with DATA.open("wb") as stream:
        stream.write(struct.pack(
            "<8s12I", b"F3K1719D", P, E_DEG, M_DEG, R_WIDTH,
            Z_WIDTH, OUT_ROWS, LOW_BOUND, order, threshold,
            len(arrays), len(bounds), column_shift))
        stream.write(struct.pack(f"<{len(bounds)}I", *bounds))
        stream.write(struct.pack(f"<{len(shifts)}I", *shifts))
        for poly in arrays:
            data = coeffs(poly, order)
            stream.write(struct.pack(f"<{len(data)}I", *data))
    print(json.dumps({
        "literal_coefficients": values,
        "normalized_A1_A2_A3_C3": (A1, A2, A3, C3),
        "primal_variables_rows_surplus": (
            4_436_009, 4_413_474, 22_535),
        "dual_variables_rows_surplus": (
            R_WIDTH+Z_WIDTH+U_WIDTH, OUT_ROWS,
            OUT_ROWS-(R_WIDTH+Z_WIDTH+U_WIDTH)),
        "bounds_reversed_H_C_Z_U_S": bounds,
        "initial_shifts": shifts,
        "effective_orders_columnShift_threshold": (
            order1, order, column_shift, threshold),
        "array_degrees": tuple(poly.degree() for poly in arrays),
        "array_sha256_u32": tuple(
            sha_u32(coeffs(poly, order)) for poly in arrays),
        "output": str(DATA),
        "output_bytes": DATA.stat().st_size,
        "binary_sha256": hashlib.sha256(DATA.read_bytes()).hexdigest(),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "decision": "GENERATED_EXACT_K17_K19_5_BY_2_PM_INSTANCE",
    }, indent=2, sort_keys=True))


def read_poly(stream, length):
    raw = array("I")
    raw.fromfile(stream, length)
    if sys.byteorder != "little":
        raw.byteswap()
    assert len(raw) == length
    return nmod_poly(list(raw), P)


def verify_basis():
    with DATA.open("rb") as stream:
        header = struct.unpack("<8s12I", stream.read(56))
        magic, p, edeg, mdeg, rwidth, zwidth, outrows, lowbound, order, \
            threshold, count, bound_count, column_shift = header
        assert magic == b"F3K1719D"
        assert (p,edeg,mdeg,rwidth,zwidth,outrows,lowbound) == (
            P,E_DEG,M_DEG,R_WIDTH,Z_WIDTH,OUT_ROWS,LOW_BOUND)
        assert (count,bound_count,column_shift) == (7,5,57_193)
        bounds=struct.unpack("<5I",stream.read(20))
        initial=struct.unpack("<5I",stream.read(20))
        arrays=[read_poly(stream,order) for _ in range(7)]
        assert not stream.read(1)
    zero=nmod_poly([],P)
    series=((arrays[0],arrays[2]),(arrays[1],arrays[3]),
            (zero,arrays[4]),(zero,arrays[5]),(zero,arrays[6]))
    with BASIS.open("rb") as stream:
        magic2,p2,order2,size=struct.unpack("<8s3I",stream.read(20))
        assert magic2==b"F3K1719B" and (p2,order2)==(P,order)
        assert struct.unpack("<5I",stream.read(20))==initial
        final=struct.unpack("<5I",stream.read(20))
        lead=[[0]*5 for _ in range(5)]
        actual=[]; degrees=[]; checks=0
        for i in range(5):
            row=[read_poly(stream,size) for _ in range(5)]
            ds=tuple(x.degree() for x in row); degrees.append(ds)
            actual.append(max((d+initial[j] for j,d in enumerate(ds)
                               if d>=0),default=-1))
            for j,x in enumerate(row):
                k=final[i]-initial[j]
                lead[i][j]=int(x[k]) if 0<=k<size else 0
            for col in range(2):
                val=sum((row[j]*series[j][col] for j in range(5)),zero)
                assert not val.truncate(order); checks+=1
        assert not stream.read(1)
    assert tuple(actual)==final
    gain=sum(final)-sum(initial)
    assert gain==2*order-column_shift==303_637
    determinant=1
    for col in range(5):
        pivot=next(i for i in range(col,5) if lead[i][col])
        if pivot!=col:
            lead[col],lead[pivot]=lead[pivot],lead[col]
            determinant=-determinant%P
        pv=lead[col][col]; determinant=determinant*pv%P
        inv=pow(pv,-1,P)
        for row in range(col+1,5):
            factor=lead[row][col]*inv%P
            lead[row]=[(x-factor*y)%P for x,y in zip(lead[row],lead[col])]
    assert determinant
    found=min(final)<=threshold
    print(json.dumps({
        "basis_file_bytes":BASIS.stat().st_size,
        "basis_sha256":hashlib.sha256(BASIS.read_bytes()).hexdigest(),
        "bounds_reversed_H_C_Z_U_S":bounds,
        "initial_shift":initial,"final_shift":final,
        "component_degrees":degrees,"threshold":threshold,
        "minimum_shifted_degree_gap":min(final)-threshold,
        "column_orders_and_shift_gain":(order-column_shift,order,gain),
        "shift_leading_determinant":determinant,
        "approximant_zero_checks":checks,
        "peak_rss_kib":resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "decision":("RED_NONZERO_K17_K19_VECTOR_DUAL" if found else
                    "CERTIFIED_GREEN_K17_K19_VECTOR_DUAL_INJECTIVE"),
    },indent=2,sort_keys=True))


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--generate",action="store_true")
    parser.add_argument("--verify-basis",action="store_true")
    args=parser.parse_args()
    if args.generate: generate()
    elif args.verify_basis: verify_basis()
    else: parser.error("select --generate or --verify-basis")


if __name__=="__main__":
    main()
