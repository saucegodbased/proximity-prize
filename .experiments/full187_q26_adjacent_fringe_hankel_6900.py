#!/usr/bin/env python3
"""Exact adjacent-window certificate for all eleven Full187 q=26 classes.

Commit 4b5ea56 proves that, in the d=29/passive-53 contact sector, the
complete-depth q=0..25 source box leaves eleven independent q=26 classes.
The ninth finite difference from d1620d8 is the same class represented by a
whole U^9 polynomial, so it cannot be added inside that source box.

This experiment uses coefficient freedom *outside* the complete all-node
box.  In stream (r,s)=(21-s,s), couple the adjacent physical polynomials P8
and P9.  Their q=0..25 jets stay fixed under

    delta P8 = Omega^26 A,       deg A < a_s,
    delta P9 = Omega^26 B,       deg B < b_s,

where Omega=X^N-1.  On the f=8,q=26 contact block, after a common invertible
node diagonal, their variation is A+9*u1*B.  Low coefficients are controlled
by A.  The remaining quotient is a Toeplitz map from B whose selected square
minor is Hankel.  We certify that minor exactly, for every s=0..10, using the
literal frozen target and FLINT Berlekamp--Massey over the benchmark field.

This proves the simultaneous first-fringe gate only.  Every induced
higher-q, higher-contact, larger-passive, and u0/error tail is classified and
retained; the subsequent multi-f/multi-q confluence is not claimed here.
"""

from __future__ import annotations

from collections import Counter
import hashlib
import json
from pathlib import Path
import resource

import full187_actual_pascal_residual_and_first_fringe_gate_6900 as F
import full187_q26_complete_depth_rank_6900 as Q
import full187_q26_ninth_difference_bypass_6900 as FD
import full187_target_charge13_transposed_four_residue_gate_6900 as T
import full187_terminal_lowT_hasse_closure_audit_6900 as H


P = F.P
N = H.N
M = H.M
J = H.J
L = 2_703
CONTACT_F = 8
HASSE_Q = 26
SLOPE = H.SLOPE
CURVATURE = H.CURVATURE

assert P == 2_130_706_433
assert N == 262_144
assert M == 60
assert J == 82
assert SLOPE == 21
assert CURVATURE == 10
assert P == 1 + 8_128 * N


def complete_depth_class_linkage():
    """Link the exact q26 cokernel and the whole FD/U^9 representative."""
    target_singletons = []
    for s in range(CURVATURE + 1):
        pair = (SLOPE - s, s)
        column = Q.physical_column(pair, HASSE_Q)
        expected_row = Q.ROW_INDEX[(pair, HASSE_Q)]
        assert column == {expected_row: 1}
        target_singletons.append((s, pair, Q.ROW_KEYS[expected_row]))

    # Re-run the literal integral FD cancellation and the exact whole
    # correlated polynomial factorization.  In particular, this does not
    # split U^9 into eleven unrelated adapted rows.
    finite_difference = FD.finite_difference_and_target_receipt()
    whole_u9 = FD.sharp_basis_factorization_receipt()
    assert finite_difference["all_target_rows_match_in_T_E_R_S_Z"]
    assert finite_difference["all_target_scalars_cancel_mod_target_prime"]
    assert len(whole_u9["stream_receipts"]) == 11

    return {
        "predecessor_complete_depth_rank_commit": "4b5ea56",
        "predecessor_exact_source_rank_nullity": (4_862, 0),
        "predecessor_q26_rank_gain": 11,
        "q26_target_adapted_singletons": tuple(target_singletons),
        "predecessor_canonical_sha256": (
            "9a92f04f3063f9b5f0f5d204c83edbe09231ff4fc518aa81ba4f5482cab7cf8e"),
        "whole_polynomial_identity": (
            "T^26*A^8*R^(21-s)*S^s + sum_(k=1)^9 "
            "(-1)^k*binom(9,k)*T^(26-k)*A^(8+k)*R^(21-s-k)*S^s "
            "= -T^17*A^8*R^(12-s)*(E-T^2*S/2)^9*S^s"),
        "whole_u9_stream_count": len(whole_u9["stream_receipts"]),
        "whole_u9_factorization_support_sizes": tuple(
            receipt["direct_and_factorized_support_sizes"]
            for receipt in whole_u9["stream_receipts"]),
        "whole_u9_order2_parameter_counts": tuple(
            len(receipt[
                "basis_parameters_a0_h_t_b_e_outer_weight_coefficient"])
            for receipt in whole_u9["stream_receipts"]),
        "interpretation": (
            "Modulo the complete-depth q<=25 image, each whole U^9 residual "
            "is exactly its corresponding nonzero q26 class.  Hence an onto "
            "map to arbitrary q26 common coefficients also disposes of the "
            "whole correlated U^9 representatives, without assigning their "
            "adapted monomials independently."),
    }


def source_and_tail_ledger():
    """Prove source legality and classify every structural variation tail."""
    sources = []
    tail_counts = Counter()
    low_jet_zero_checks = 0
    higher_jet_potential_occurrences = 0

    for s in range(CURVATURE + 1):
        r = SLOPE - s
        for source_y, source_z in ((8, 2_674), (9, 2_673)):
            width = H.width(source_y, r, s)
            fringe = width - HASSE_Q * N
            assert HASSE_Q * N < width < (HASSE_Q + 1) * N
            assert source_y + r + s < J
            assert source_y + r + s + source_z == L
            assert r + s == SLOPE and s <= CURVATURE
            sources.append((s, source_y, r, s, source_z, width, fringe))

            # Omega^26 has multiplicity exactly 26 at every domain node.
            # Therefore every structural term below uses a zero coefficient
            # jet for q<26.  Count the exact syntactic local occurrences so
            # the preservation claim is not merely dimensional.
            for contact_f in range(source_y + 1):
                for a_e in range(contact_f + 1):
                    for c_s in range(contact_f - a_e + 1):
                        for h in range(source_y - contact_f + 1):
                            for q in range(HASSE_Q):
                                if q + contact_f + 2 * a_e + c_s < M:
                                    low_jet_zero_checks += 1

                            for q in range(
                                    HASSE_Q,
                                    M - (contact_f + 2 * a_e + c_s)):
                                higher_jet_potential_occurrences += 1
                                u0_power = source_y - contact_f - h
                                passive_z = source_z + h
                                if u0_power > 0:
                                    category = "u0_positive_error_only"
                                elif (q == HASSE_Q and contact_f == 8
                                      and passive_z == 2_674):
                                    category = "desired_f8_q26_z2674"
                                elif contact_f < 8:
                                    assert passive_z > 2_674
                                    category = (
                                        "lower_contact_fullnode_larger_passive")
                                elif q > HASSE_Q:
                                    category = "strictly_higher_Hasse_weight"
                                else:
                                    # The only remaining case is the full
                                    # P9 contact at f=9,q=26,z=2673.  Its
                                    # contact/Hasse weight is 35, one after
                                    # the desired weight 34.
                                    assert (source_y, contact_f, passive_z) == (
                                        9, 9, 2_673)
                                    category = (
                                        "P9_fullcontact_next_weight_z2673")
                                tail_counts[category] += 1

    assert len(sources) == 22
    assert all(item[5] - HASSE_Q * N == item[6] for item in sources)
    assert tail_counts["desired_f8_q26_z2674"] == 11 * (45 + 45)
    assert tail_counts["P9_fullcontact_next_weight_z2673"] == 11 * 55
    assert tail_counts["lower_contact_fullnode_larger_passive"] > 0
    assert tail_counts["u0_positive_error_only"] > 0
    assert tail_counts["strictly_higher_Hasse_weight"] > 0

    return {
        "physical_source_records_s_y_r_s_z_width_fringe": tuple(sources),
        "source_legality": (
            "P8=Y^8 R^(21-s)S^s Z^2674 and "
            "P9=Y^9 R^(21-s)S^s Z^2673 have total degree2703, "
            "active degrees29/30<82, derivative r+s=21 and s<=10"),
        "variation_formula": (
            "deltaP8=(X^N-1)^26*A_s, deg A_s<a_s; "
            "deltaP9=(X^N-1)^26*B_s, deg B_s<b_s"),
        "strict_degree_check": (
            "deg(delta P_i) <= 26N+fringe_i-1 = width(P_i)-1"),
        "exact_structural_q0_to_q25_zero_occurrences": low_jet_zero_checks,
        "potential_q26_and_higher_structural_occurrences": (
            higher_jet_potential_occurrences),
        "q26_and_higher_tail_class_counts": tuple(sorted(tail_counts.items())),
        "tail_orientation": (
            "The f8,q26,z2674 block is the solved diagonal.  The P9 "
            "f9,q26 term has next contact/Hasse weight 35.  Every q>26 "
            "term has strictly higher Hasse weight.  Full-node f<8 terms "
            "move to strictly larger passive Z and belong to the "
            "passive-raising triangular prefix.  All remaining terms have "
            "positive u0 power and vanish on agreement nodes, so they stay "
            "in the error-capacity connecting map.  None is discarded."),
    }


def all_q26_adjacent_hankel_gates():
    """Certify all eleven coupled P8/P9 maps have full row rank."""
    instance = T.build_target_instance()
    u1_coefficients = instance.u1_values.copy()
    T.ntt(u1_coefficients, inverse=True)

    records = []
    for s in range(CURVATURE + 1):
        r = SLOPE - s
        width8 = H.width(8, r, s)
        width9 = H.width(9, r, s)
        fringe8 = width8 - HASSE_Q * N
        fringe9 = width9 - HASSE_Q * N
        quotient_rows = N - fringe8

        assert width8 == 7_023_742 + s
        assert width9 == 6_892_671 + s
        assert fringe8 == 207_998 + s
        assert fringe9 == 76_927 + s
        assert quotient_rows == 54_146 - s
        assert fringe8 + fringe9 > N

        # A controls coefficients 0..fringe8-1.  In the remaining quotient,
        # multiplication by u1 sends B_j to U1[fringe8+i-j].  Select the
        # final quotient_rows B columns j=fringe9-quotient_rows..fringe9-1
        # and reverse them.  Entry (i,k) is sequence[i+k].
        first_selected_b_column = fringe9 - quotient_rows
        assert first_selected_b_column >= 0
        sequence_start = fringe8 - fringe9 + 1
        assert sequence_start == 131_072
        full_toeplitz_index_range = (
            fringe8 - (fringe9 - 1), fringe8 + quotient_rows - 1)
        assert full_toeplitz_index_range == (sequence_start, N - 1)
        selected_minor_index_range = (
            sequence_start, sequence_start + 2 * quotient_rows - 2)
        assert selected_minor_index_range[1] < N
        sequence = tuple(u1_coefficients[
            sequence_start:sequence_start + 2 * quotient_rows])
        assert len(sequence) == 2 * quotient_rows

        connection, remainder, reduce_calls = F.exact_bm(sequence)
        complexity = len(connection) - 1
        remainder_degree = len(remainder) - 1
        assert complexity == quotient_rows
        assert remainder_degree == quotient_rows - 1
        assert connection[0] and connection[-1]

        records.append({
            "s_r": (s, r),
            "windows_P8_P9": (width8, width9),
            "fringes_a_b": (fringe8, fringe9),
            "quotient_toeplitz_shape": (quotient_rows, fringe9),
            "selected_square_B_columns": (
                first_selected_b_column, fringe9 - 1),
            "full_toeplitz_index_min_max": full_toeplitz_index_range,
            "selected_hankel_index_min_max": selected_minor_index_range,
            "hankel_minor_size": quotient_rows,
            "certificate_sequence_length": len(sequence),
            "certificate_sequence_sha256_u64": F.sha256_u64(sequence),
            "berlekamp_massey_complexity": complexity,
            "berlekamp_massey_remainder_degree": remainder_degree,
            "berlekamp_massey_reduce_calls": reduce_calls,
            "connection_first_last": (connection[0], connection[-1]),
            "connection_sha256_u64": F.sha256_u64(connection),
            "remainder_sha256_u64": F.sha256_u64(remainder),
            "exact_rank": quotient_rows,
        })

    assert len(records) == 11
    assert all(record["exact_rank"] == record["quotient_toeplitz_shape"][0]
               for record in records)
    return {
        "literal_frozen_u1_coefficient_sha256_u64": F.sha256_u64(
            u1_coefficients),
        "common_hankel_sequence_start": 131_072,
        "contact_diagonal": (
            "H26(Omega^26 V)(x)=(N*x^-1)^26 V(x), nonzero at every node"),
        "coupled_equation_after_common_diagonal": "A_s + 9*u1*B_s",
        "scalar_9_is_invertible_mod_p": pow(9, -1, P),
        "per_stream_exact_certificates": tuple(records),
        "all_eleven_rectangular_maps_full_row_rank": True,
        "simultaneous_interpretation": (
            "The eleven (r,s) source pairs are distinct physical coefficient "
            "polynomials.  Each coupled map is onto arbitrary F_p^N common "
            "coefficients, so all eleven q26 blocks can be solved at once; "
            "the RHS may be the complete correlated C/P residual rather than "
            "a separated C-only term."),
    }


def main():
    linkage = complete_depth_class_linkage()
    sources_and_tails = source_and_tail_ledger()
    gates = all_q26_adjacent_hankel_gates()
    stable = {
        "scope": (
            "exact frozen-target adjacent P8/P9 coefficient-window solution "
            "of all eleven Full187 f8,q26 first-fringe classes after the "
            "complete-depth q0..25 projection; every induced tail retained, "
            "but no full multi-f/multi-q confluence or packet lift"),
        "target_p_N_w_g_errors_m_D_J_L_slope_curvature": (
            P, N, H.W, H.G, H.ERRORS, M, H.D, J, L, SLOPE, CURVATURE),
        "exact_F3": "B*(Y-P-(Z-gamma)*q_H)",
        "complete_depth_and_U9_linkage": linkage,
        "source_legality_and_tail_ledger": sources_and_tails,
        "adjacent_hankel_gates": gates,
        "decision": (
            "GREEN_ALL_ELEVEN_Q26_FIRST_FRINGES_BY_ADJACENT_P8_P9_HANKEL"),
        "remaining_gate": (
            "compose the retained next-weight, higher-Hasse, larger-passive, "
            "and u0/error tails through the whole multi-f/multi-q confluence; "
            "then connect the exact F0,F1,F2,F3 packet support"),
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
