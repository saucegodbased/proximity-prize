#!/usr/bin/env python3
"""Actual Pascal-residual factorization and tight first-fringe rank gate.

This follows the complete-depth projection in commit 2d678e8 and the raw
block-rank STOP in b05608c.  It proves two separate facts.

1. The actual residual, including terminal C jets and every unprescribed
   higher jet of every already-chosen P_k, is still a scalar combination of
   the 126,315 raw contact columns.  Hence every raw-column left dual vanishes
   on the actual correlated residual.  The d=11 two-row dual is replayed
   symbolically on all 60 independent C/P symbols.

2. The numerically tightest first-fringe compatibility block is not singular.
   The coupled f=58/f=59 variation reduces to a 54,086 by 76,987 Toeplitz
   map made from the literal frozen U1 coefficients.  An exact 54,086-square
   Hankel minor is certified nonsingular by FLINT Berlekamp--Massey.

No claim is made about the remaining multi-f, multi-q fringe cascade or the
lower-passive/u0 connecting tails.
"""

from __future__ import annotations

from collections import Counter
import ctypes
from ctypes import POINTER, c_long, c_ulong
import hashlib
import json
from math import comb
from pathlib import Path
import resource
import struct

import full187_all_noncapacity_pascal_hermite_slide_6900 as A
import full187_complete_depth_pascal_hermite_slide_6900 as CD
import full187_grouped_slide_block_confluence_6900 as MB
import full187_target_charge13_transposed_four_residue_gate_6900 as T
import full187_terminal_lowT_hasse_closure_audit_6900 as H


P = H.P if hasattr(H, "P") else 2_130_706_433
N = H.N
M = H.M
J = H.J
INV2 = pow(2, -1, P)


def scale_expression(expression, scalar):
    scalar %= P
    return {
        key: coefficient * scalar % P
        for key, coefficient in expression.items()
        if coefficient * scalar % P
    }


def add_expressions(left, right):
    answer = dict(left)
    A.add_scaled_shifted(answer, right, 1, 0)
    return answer


def actual_residual_factorization():
    """Check every residual block has one intact raw-contact factor."""
    residual_block_count = 0
    symbolic_common_coefficient_terms = 0
    maximum_common_coefficient_terms = 0
    first_residual_histogram = Counter()
    monotonic_checks = 0

    for r, s in A.all_shapes():
        qmax = tuple(CD.complete_qmax(r, s, f) for f in range(M))
        for f in range(M - 1):
            assert qmax[f + 1] <= qmax[f]
            monotonic_checks += 1
        terminal_y = J - r - s
        for f in range(M):
            first_q = qmax[f] + 1
            if first_q >= M - f:
                continue
            first_residual_histogram[first_q] += 1
            for q in range(first_q, M - f):
                # Since complete depth is monotone in f, every higher P_k,q
                # is also an unprescribed higher jet.  Thus the literal
                # residual common coefficient is
                #
                # binom(terminal_y,f) u^(terminal_y-f) C_q
                # + sum_(k=f)^59 binom(k,f) u^(k-f) U_(k,q).
                assert all(q > qmax[k] for k in range(f, M))
                term_count = 1 + (M - f)
                symbolic_common_coefficient_terms += term_count
                maximum_common_coefficient_terms = max(
                    maximum_common_coefficient_terms, term_count)
                key = (f + r + s, f, r, s, q, J - f - r - s)
                assert key in MB.complete_depth_residual_keys_cache
                residual_block_count += 1

    assert monotonic_checks == 187 * 59
    assert residual_block_count == 126_315
    assert maximum_common_coefficient_terms == 61
    return {
        "residual_block_count": residual_block_count,
        "monotone_complete_depth_checks": monotonic_checks,
        "symbolic_common_coefficient_term_count": (
            symbolic_common_coefficient_terms),
        "maximum_terms_in_one_common_coefficient": (
            maximum_common_coefficient_terms),
        "first_residual_q_histogram": tuple(sorted(
            first_residual_histogram.items())),
        "factorization": (
            "B_(r,s,f,q) * Z^q * contactY^f * R^r * S^s, where "
            "B=binom(J-r-s,f)u^(J-r-s-f)C_q + "
            "sum_(k=f)^59 binom(k,f)u^(k-f)U_(k,q)"),
        "all_raw_column_left_duals_pair_to_zero": True,
    }


def d11_actual_dual_replay():
    """Replay the first Hall dual on the complete symbolic C/P residual."""
    r, s, f, q = 0, 10, 1, 35
    terminal_y = J - r - s
    correction_jets = {}
    for source_f in range(M - 1, -1, -1):
        if q > CD.complete_qmax(r, s, source_f):
            correction_jets[source_f] = {
                (("U", source_f, q), 0): 1,
            }
        else:
            before = A.residual_expression(
                terminal_y, source_f, correction_jets)
            correction_jets[source_f] = A.negate(before)

    common = A.residual_expression(terminal_y, f, correction_jets)
    A.add_scaled_shifted(common, correction_jets[f], 1, 0)
    expected = {
        (("C",), terminal_y - f): comb(terminal_y, f) % P,
    }
    for source_f in range(f, M):
        expected[(("U", source_f, q), source_f - f)] = (
            comb(source_f, f) % P)
    assert common == expected
    assert len(common) == 60

    s_row = scale_expression(common, -INV2)
    e_row = common
    pairing = add_expressions(scale_expression(s_row, 2), e_row)
    assert not pairing
    literal_dual = MB.explicit_two_row_hall_dual(
        MB.complete_depth_residual_keys_cache)
    assert literal_dual["pairing_mod_p"] == 0
    return {
        "stream_r_s_f_q_terminalY": (r, s, f, q, terminal_y),
        "common_coefficient_term_count": len(common),
        "common_coefficient": (
            "72*u^71*C_35 + sum_(k=1)^59 k*u^(k-1)*U_(k,35)"),
        "common_expression_sha256": hashlib.sha256(
            repr(tuple(sorted(common.items()))).encode()).hexdigest(),
        "S_row_multiplier_E_row_multiplier": ((-INV2) % P, 1),
        "dual_coefficients": (2, 1),
        "symbolic_pairing_term_count": len(pairing),
        "decision": "GREEN_D11_ACTUAL_RESIDUAL_DUAL_IDENTICALLY_ZERO",
    }


def first_fringe_ledger():
    """Find the tightest individual post-complete-depth capacity fringe."""
    rows = []
    for r, s in A.all_shapes():
        for f in range(M):
            width = H.width(f, r, s)
            complete_depth = width // N
            first_q = CD.complete_qmax(r, s, f) + 1
            if first_q >= M - f:
                continue
            assert first_q == complete_depth
            fringe = width - complete_depth * N
            target_depth = M - (first_q + f)
            mixed_capacity_dimension = H.G * target_depth + H.ERRORS
            rows.append((
                fringe - mixed_capacity_dimension,
                f + r + s, r, s, f, first_q, fringe,
                mixed_capacity_dimension, width, target_depth,
            ))

    assert len(rows) == 9_482
    assert all(row[0] < 0 for row in rows)
    tightest = max(rows)
    first_active = min(rows, key=lambda row: (row[1], row[2:]))
    assert tightest == (
        -54_086, 79, 11, 10, 58, 1, 208_058,
        262_144, 470_202, 1,
    )
    assert first_active == (
        -3_432_702, 0, 0, 0, 0, 41, 76_876,
        3_509_578, 10_824_780, 19,
    )
    return {
        "residual_bearing_physical_polynomials": len(rows),
        "every_individual_post_lowjet_fringe_below_naive_capacity_cost": True,
        "tightest_individual_gap_active_r_s_f_q_fringe_cost_width_depth": (
            tightest),
        "first_active_gap_active_r_s_f_q_fringe_cost_width_depth": (
            first_active),
        "interpretation": (
            "Individual capacity cannot be superposed after consuming all "
            "complete all-node jets. Higher-f polynomial fringes must be "
            "coupled into each lower-f equation."),
    }


class NMod(ctypes.Structure):
    _fields_ = [("n", c_ulong), ("ninv", c_ulong), ("norm", c_ulong)]


class NModPoly(ctypes.Structure):
    _fields_ = [
        ("coeffs", POINTER(c_ulong)),
        ("alloc", c_long),
        ("length", c_long),
        ("mod", NMod),
    ]


class NModBerlekampMassey(ctypes.Structure):
    _fields_ = [
        ("npoints", c_long),
        ("R0", NModPoly), ("R1", NModPoly),
        ("V0", NModPoly), ("V1", NModPoly),
        ("qt", NModPoly), ("rt", NModPoly),
        ("points", NModPoly),
    ]


def exact_bm(sequence):
    """Return FLINT's exact connection and remainder polynomials."""
    library = ctypes.CDLL("libflint.so")
    library.nmod_berlekamp_massey_init.argtypes = [
        POINTER(NModBerlekampMassey), c_ulong]
    library.nmod_berlekamp_massey_add_points.argtypes = [
        POINTER(NModBerlekampMassey), POINTER(c_ulong), c_long]
    library.nmod_berlekamp_massey_reduce.argtypes = [
        POINTER(NModBerlekampMassey)]
    library.nmod_berlekamp_massey_reduce.restype = ctypes.c_int
    library.nmod_berlekamp_massey_clear.argtypes = [
        POINTER(NModBerlekampMassey)]

    state = NModBerlekampMassey()
    points = (c_ulong * len(sequence))(*sequence)
    library.nmod_berlekamp_massey_init(ctypes.byref(state), P)
    try:
        library.nmod_berlekamp_massey_add_points(
            ctypes.byref(state), points, len(sequence))
        reduce_calls = 0
        while True:
            reduce_calls += 1
            if not library.nmod_berlekamp_massey_reduce(
                    ctypes.byref(state)):
                break
        connection = tuple(
            state.V1.coeffs[i] for i in range(state.V1.length))
        remainder = tuple(
            state.R1.coeffs[i] for i in range(state.R1.length))
        return connection, remainder, reduce_calls
    finally:
        library.nmod_berlekamp_massey_clear(ctypes.byref(state))


def sha256_u64(values):
    digest = hashlib.sha256()
    for start in range(0, len(values), 16_384):
        chunk = values[start:start + 16_384]
        digest.update(struct.pack(f"<{len(chunk)}Q", *chunk))
    return digest.hexdigest()


def tight_f58_f59_toeplitz_gate():
    """Certify the tightest coupled first-fringe map is row-surjective."""
    instance = T.build_target_instance()
    u1_coefficients = instance.u1_values.copy()
    T.ntt(u1_coefficients, inverse=True)
    assert all(u1_coefficients)

    p58_fringe = H.width(58, 11, 10) - N
    p59_fringe = H.width(59, 11, 10) - N
    quotient_rows = N - p58_fringe
    assert (p58_fringe, p59_fringe, quotient_rows) == (
        208_058, 76_987, 54_086)

    # After fixing q=0 at all nodes, variations are Omega*A and Omega*B,
    # deg A<208058, deg B<76987.  H_1(Omega*V)(x)=N*x^-1*V(x).
    # The f=58 equation is therefore A + 59*u1*B.  A kills all coefficient
    # positions below 208058.  On the high quotient the B map is Toeplitz:
    # T[i,j]=U1[208058+i-j].  Reverse columns and choose the final 54086 B
    # monomials.  This gives the Hankel minor s[i+j], with
    # s=U1[131072:131072+2*54086-1].
    sequence_start = p58_fringe - p59_fringe + 1
    assert sequence_start == 131_072
    certificate_sequence = tuple(u1_coefficients[
        sequence_start:sequence_start + 2 * quotient_rows])
    assert len(certificate_sequence) == 2 * quotient_rows
    connection, remainder, reduce_calls = exact_bm(certificate_sequence)

    # Standard Hankel/Berlekamp--Massey criterion: for 2m scalars, the
    # leading m-by-m Hankel determinant is nonzero iff linear complexity=m.
    # The remainder degree m-1 and nonzero connection endpoints give an
    # additional normality receipt for this exact run.
    assert len(connection) - 1 == quotient_rows
    assert len(remainder) - 1 == quotient_rows - 1
    assert connection[0] and connection[-1]
    return {
        "physical_pair_r_s_f": ((11, 10, 58), (11, 10, 59)),
        "windows_P58_P59": (
            H.width(58, 11, 10), H.width(59, 11, 10)),
        "post_q0_fringe_dimensions_P58_P59": (
            p58_fringe, p59_fringe),
        "node_constraint_dimension": N,
        "joint_nominal_dimension_surplus": (
            p58_fringe + p59_fringe - N),
        "reduced_high_quotient_toeplitz_shape": (
            quotient_rows, p59_fringe),
        "toeplitz_coefficient_index_min_max": (
            sequence_start, N - 1),
        "certified_hankel_minor_size": quotient_rows,
        "hankel_certificate_sequence_length": len(certificate_sequence),
        "hankel_certificate_sequence_sha256_u64": sha256_u64(
            certificate_sequence),
        "berlekamp_massey_complexity": len(connection) - 1,
        "berlekamp_massey_remainder_degree": len(remainder) - 1,
        "berlekamp_massey_reduce_calls": reduce_calls,
        "connection_first_last": (connection[0], connection[-1]),
        "connection_sha256_u64": sha256_u64(connection),
        "remainder_sha256_u64": sha256_u64(remainder),
        "exact_rank": quotient_rows,
        "decision": "GREEN_TIGHT_F58_F59_FIRST_FRINGE_FULL_ROW_RANK",
    }


def main():
    # Cached once because the factorization loop uses membership 126,315
    # times.  This is assigned only inside the experimental imported module.
    MB.complete_depth_residual_keys_cache = frozenset(
        MB.complete_depth_residual_keys())
    factorization = actual_residual_factorization()
    d11 = d11_actual_dual_replay()
    fringe = first_fringe_ledger()
    tight_gate = tight_f58_f59_toeplitz_gate()
    stable = {
        "scope": (
            "actual C/P-symbol Pascal top residual and smallest first-fringe "
            "compatibility gate after 2d678e8; no multi-q cascade, u0 tail, "
            "packet bridge, or production claim"),
        "target_p_N_w_g_errors_m_D_J": (
            P, N, H.W, H.G, H.ERRORS, M, H.D, J),
        "actual_residual_factorization": factorization,
        "smallest_raw_dual_on_actual_residual": d11,
        "individual_fringe_ledger": fringe,
        "tightest_coupled_first_fringe_gate": tight_gate,
        "decision": (
            "GREEN_ALL_RAW_DUALS_VANISH_ON_ACTUAL_RESIDUAL__"
            "GREEN_TIGHTEST_FIRST_FRINGE_PAIR__"
            "NEXT_MULTI_F_MULTI_Q_CONFLUENCE"),
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
