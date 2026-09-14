#!/usr/bin/env python3
"""Exact all-stream adjacent-degree first-fringe rank certificate.

For every residual-bearing Full187 coefficient polynomial P_f after the
complete-depth projection, this executable couples its first unsupported
Hasse layer to the still-free fringe of P_(f+1).  It proves that adjacent
bandwidth two is necessary and sufficient for all 9,482 first-fringe blocks
on the literal frozen target.

The 9,482 maps collapse to 219 Hankel sizes in one common cyclic coefficient
sequence of U1.  Exact incremental FLINT Berlekamp--Massey certifies a
nonsingular leading minor at every size.  This is not yet the simultaneous
multi-q cascade: the same polynomial fringes can be reused by later equations.
"""

from __future__ import annotations

from collections import Counter
import ctypes
from ctypes import POINTER, c_long, c_ulong
import hashlib
import json
from pathlib import Path
import resource

from flint import nmod_poly

import full187_actual_pascal_residual_and_first_fringe_gate_6900 as F
import full187_all_noncapacity_pascal_hermite_slide_6900 as A
import full187_complete_depth_pascal_hermite_slide_6900 as CD
import full187_target_charge13_transposed_four_residue_gate_6900 as T
import full187_terminal_lowT_hasse_closure_audit_6900 as H


P = 2_130_706_433
N = H.N
W = H.W
HALF = N // 2
INV2 = pow(2, -1, P)
INV_N = pow(N, -1, P)


def pair_census():
    occurrences = []
    distinct = set()
    depth_drop_histogram = Counter()
    for r, s in A.all_shapes():
        for f in range(H.M - 1):
            first_q = CD.complete_qmax(r, s, f) + 1
            if first_q >= H.M - f:
                continue
            width_f = H.width(f, r, s)
            width_next = H.width(f + 1, r, s)
            depth_f, fringe_f = divmod(width_f, N)
            depth_next, fringe_next = divmod(width_next, N)
            depth_drop = depth_f - depth_next
            assert depth_drop in (0, 1)
            assert first_q == depth_f
            quotient_rows = N - fringe_f
            assert fringe_next >= quotient_rows
            assert (fringe_f - fringe_next + 1) % N == HALF

            # If depth drops, the adjacent polynomial contributes one Hasse
            # order beyond its first fringe.  After normalizing by
            # H_1(Omega)^depth_f, its action on X^j is diagonal with scalar
            #
            # (j + (depth_f-1)(N-1)/2) / N.
            #
            # This is the local triangular hyperderivative weight that a
            # naive reversed-HRS dual would miss.  It is nonzero throughout
            # the strict adjacent fringe, so it preserves W_fringe_next.
            forbidden_monomial = None
            if depth_drop:
                constant = ((depth_f - 1) * (N - 1) * INV2) % P
                forbidden_monomial = (-constant) % P
                assert not 0 <= forbidden_monomial < fringe_next
                assert all(value % P for value in (
                    INV_N * constant,
                    INV_N * (fringe_next - 1 + constant),
                ))

            nominal_surplus = fringe_f + fringe_next - N
            record = (
                nominal_surplus, fringe_f, fringe_next, quotient_rows,
                depth_drop, depth_f, r, s, f, first_q,
                forbidden_monomial,
            )
            occurrences.append(record)
            distinct.add((fringe_f, fringe_next, quotient_rows))
            depth_drop_histogram[depth_drop] += 1

    assert len(occurrences) == 9_482
    assert len(distinct) == 219
    assert depth_drop_histogram == Counter({0: 4_789, 1: 4_693})
    worst = min(occurrences)
    best = max(occurrences)
    assert worst == (
        22_681, 76_876, 207_949, 185_268,
        1, 41, 0, 0, 0, 41, 2_125_463_573,
    )
    assert best == (
        22_901, 208_058, 76_987, 54_086,
        0, 1, 11, 10, 58, 1, None,
    )
    return tuple(occurrences), tuple(sorted(distinct)), {
        "physical_first_fringe_blocks": len(occurrences),
        "distinct_fringe_pair_maps": len(distinct),
        "depth_same_vs_drop_one_histogram": tuple(sorted(
            depth_drop_histogram.items())),
        "nominal_surplus_min_max": (worst[0], best[0]),
        "worst_surplus_fringeF_fringeNext_rows_depthDrop_depth_"
        "r_s_f_q_forbiddenMonomial": worst,
        "best_surplus_fringeF_fringeNext_rows_depthDrop_depth_"
        "r_s_f_q_forbiddenMonomial": best,
        "one_polynomial_bandwidth_fails": True,
        "candidate_minimum_adjacent_bandwidth": 2,
    }


def configure_flint_bm():
    library = ctypes.CDLL("libflint.so")
    library.nmod_berlekamp_massey_init.argtypes = [
        POINTER(F.NModBerlekampMassey), c_ulong]
    library.nmod_berlekamp_massey_add_points.argtypes = [
        POINTER(F.NModBerlekampMassey), POINTER(c_ulong), c_long]
    library.nmod_berlekamp_massey_reduce.argtypes = [
        POINTER(F.NModBerlekampMassey)]
    library.nmod_berlekamp_massey_reduce.restype = ctypes.c_int
    library.nmod_berlekamp_massey_clear.argtypes = [
        POINTER(F.NModBerlekampMassey)]
    return library


def incremental_hankel_certificates(sequence, sizes):
    """Certify each leading size-m Hankel minor by its 2m BM prefix."""
    library = configure_flint_bm()
    state = F.NModBerlekampMassey()
    library.nmod_berlekamp_massey_init(ctypes.byref(state), P)
    position = 0
    receipts = []
    captured_connections = {}
    capture_sizes = {min(sizes), max(sizes)}
    try:
        for size in sizes:
            end = 2 * size
            chunk = (c_ulong * (end - position))(*sequence[position:end])
            library.nmod_berlekamp_massey_add_points(
                ctypes.byref(state), chunk, end - position)
            position = end
            reduce_calls = 0
            while True:
                reduce_calls += 1
                if not library.nmod_berlekamp_massey_reduce(
                        ctypes.byref(state)):
                    break
            complexity = state.V1.length - 1
            remainder_degree = state.R1.length - 1
            endpoints = (
                state.V1.coeffs[0],
                state.V1.coeffs[state.V1.length - 1],
            )
            assert complexity == size
            assert remainder_degree == size - 1
            assert all(endpoints)
            receipt = (
                size, complexity, remainder_degree, reduce_calls, *endpoints)
            receipts.append(receipt)
            if size in capture_sizes:
                captured_connections[size] = tuple(
                    state.V1.coeffs[i] for i in range(state.V1.length))
    finally:
        library.nmod_berlekamp_massey_clear(ctypes.byref(state))
    return tuple(receipts), captured_connections


def normalized_equal(left, right):
    if len(left) != len(right):
        return False
    pivot = next((i for i, value in enumerate(right) if value % P), None)
    if pivot is None:
        return not any(left)
    scalar = left[pivot] * pow(right[pivot], -1, P) % P
    return all(a % P == scalar * b % P for a, b in zip(left, right))


def connection_structure_audit(instance, captured_connections):
    """Check whether endpoint certificates are familiar locator factors."""
    known = {
        "XiE": instance.xi_e_coefficients,
        "XiH": instance.xi_h_coefficients,
        "XiR": instance.xi_r_coefficients,
        "Q": instance.q_coefficients,
        "qH": instance.qh_coefficients,
    }
    receipts = []
    for size, connection in sorted(captured_connections.items()):
        polynomial = nmod_poly(list(connection), P)
        gcd_degrees = tuple(sorted(
            (name, polynomial.gcd(nmod_poly(value, P)).degree())
            for name, value in known.items()
        ))
        assert all(degree == 0 for _name, degree in gcd_degrees)

        truncation_matches = []
        for name, value in known.items():
            if len(value) < len(connection):
                continue
            candidates = {
                "prefix": value[:len(connection)],
                "suffix": value[-len(connection):],
            }
            for location, candidate in candidates.items():
                for orientation, oriented in (
                        ("forward", candidate),
                        ("reverse", candidate[::-1])):
                    if normalized_equal(connection, oriented):
                        truncation_matches.append(
                            (name, location, orientation))
        assert not truncation_matches

        salient_starts = sorted(set(
            start for start in (
                0, T.H - size, T.H, T.G - size, T.G,
                N - size, HALF - size, HALF,
            )
            if 0 <= start and start + size <= N
        ))
        geometric_matches = []
        for start in salient_starts:
            locator = T.geometric_locator(
                instance.omega_powers, start=start, length=size)
            for orientation, candidate in (
                    ("forward", locator), ("reverse", locator[::-1])):
                if normalized_equal(connection, candidate):
                    geometric_matches.append((start, orientation))
        assert not geometric_matches
        receipts.append({
            "size": size,
            "connection_sha256_u64": F.sha256_u64(connection),
            "gcd_degrees_with_known_polynomials": gcd_degrees,
            "known_prefix_suffix_matches": tuple(truncation_matches),
            "salient_geometric_locator_starts_tested": tuple(salient_starts),
            "geometric_locator_matches": tuple(geometric_matches),
        })
    return {
        "endpoint_connection_receipts": tuple(receipts),
        "known_locator_factor_or_truncation_found": False,
        "interpretation": (
            "The exact certificates are currently target-specific Padé/BM "
            "data, not a recognized XiE/XiH/XiR/Q/qH locator theorem."),
    }


def main():
    occurrences, distinct_pairs, census = pair_census()
    sizes = tuple(sorted({row[2] for row in distinct_pairs}))
    assert len(sizes) == 219
    assert (min(sizes), max(sizes)) == (54_086, 185_268)

    instance = T.build_target_instance()
    u1_coefficients = instance.u1_values.copy()
    T.ntt(u1_coefficients, inverse=True)
    assert all(u1_coefficients)
    cyclic_sequence = tuple(
        u1_coefficients[(HALF + index) % N]
        for index in range(2 * max(sizes))
    )
    receipts, connections = incremental_hankel_certificates(
        cyclic_sequence, sizes)
    structure = connection_structure_audit(instance, connections)

    stable = {
        "scope": (
            "all 9482 first unsupported scalar Hasse layers after 2d678e8; "
            "adjacent-degree X-window confluence only; shared later-q "
            "fringes, u0/passive tails, packets, and production remain open"),
        "target_p_N_W_half": (P, N, W, HALF),
        "pair_census": census,
        "uniform_local_weight_formula": {
            "same_complete_depth": "identity on W_b",
            "depth_drops_one": (
                "X^j maps to N^-1*(j+(A-1)(N-1)/2)*X^j"),
            "all_local_diagonal_weights_nonzero": True,
            "correct_dual_orientation": (
                "reverse Hasse order with v_j^-1*H_(s-i)(g/A_j)(alpha_j); "
                "do not use naive reversed HRS"),
        },
        "uniform_toeplitz_reduction": {
            "map": "W_a + U1*W_b -> R=Fp[X]/(X^N-1)",
            "all_pair_start_indices_mod_N": HALF,
            "distinct_hankel_sizes": len(sizes),
            "hankel_size_ranges": (
                (min(size for size in sizes if size < HALF),
                 max(size for size in sizes if size < HALF)),
                (min(size for size in sizes if size > HALF),
                 max(size for size in sizes if size > HALF)),
            ),
            "all_219_BM_complexities_equal_minor_size": True,
            "checkpoint_receipts_first_last_8": (
                receipts[:8], receipts[-8:]),
            "checkpoint_receipts_sha256": hashlib.sha256(
                repr(receipts).encode()).hexdigest(),
            "cyclic_certificate_sequence_sha256_u64": F.sha256_u64(
                cyclic_sequence),
            "exact_global_decision": (
                "ALL_9482_FIRST_FRINGE_ADJACENT_PAIR_MAPS_FULL_ROW_RANK"),
            "minimum_adjacent_degree_bandwidth": 2,
        },
        "connection_structure_audit": structure,
        "decision": (
            "GREEN_ALL_FIRST_FRINGE_PAIRS__"
            "STOP_NO_THEOREM_SIZED_LOCATOR_IDENTITY_YET__"
            "NEXT_SIMULTANEOUS_MULTI_Q_CASCADE"),
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
