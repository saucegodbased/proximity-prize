#!/usr/bin/env python3
"""Exact first-m69-defect actual-residual and numerator-zero split gate.

This is deliberately narrower than an arbitrary-rational rank theorem.  It
reconstructs the first descending Pascal defect for the m69 profile, retains
the literal terminal coefficient and every direct predecessor, and checks the
normalized Hasse maps of the first four prefix channels.

The key distinction is that the numerator-zero counterexample at shape
``(0,0,0)`` does not transfer to this first defect.  Here the actual incoming
residual has a factor W, and the W^0 prefix is much larger than the maximum
possible nodal zero set.  A second exact split proves that when the zero set
has at least 134317 nodes, the W^0 and W^1 channels already interpolate all
coordinates.  The remaining high-numerator/small-zero branch is reported as
open rather than inferred from W-divisibility.
"""

from __future__ import annotations

from math import comb
import hashlib
import json
from pathlib import Path
import resource
import struct
import sys


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import m69_reciprocal_all_defect_interval_gate_6900 as profile


P = 2_130_706_433
N = profile.N
Q = 15
ACTIVE = 63
BLOCK_N = 44
HOMOGENEOUS = 24
CONTACT_F = 39
R_EXP = 14
S_EXP = 10
TARGET_Z = profile.L - ACTIVE
TERMINAL_Y = profile.J - R_EXP - S_EXP

AUTHORITIES = {
    "m69_reciprocal_all_defect_interval_gate_6900.py":
        "9417a5797aa188cb6a1381b7c11e54f3df0ecf46908ad452d6dee925e1ae5069",
    "m69_numerator_zero_set_rank_countergate_6900.py":
        "efa5beaf43bd3690684800f43deef7fbddb2d4b696208303b969018e3dd34c8a",
    "full187_actual_pascal_residual_and_first_fringe_gate_6900.py":
        "4f71084905369899563eb496f2b9b044245107bd7a3357aac35336709b02da15",
    "M69RationalTwoPowerGate6900.lean":
        "ab1bba986d0afcea4c2df9ccf9a97e9712c6b9a8f789b54cfbaa286f14b0390c",
}


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sha256_repr(value) -> str:
    return hashlib.sha256(repr(value).encode()).hexdigest()


def normalized_hasse_weight(depth: int, exponent: int, order: int) -> int:
    """Weight of X^exponent in X^q H_q(Omega^depth X^exponent).

    At every NTT root alpha, alpha^N=1, so expansion of
    Omega^depth=(X^N-1)^depth leaves the displayed scalar times alpha^exponent.
    """
    return sum(
        (-1 if (depth - ell) % 2 else 1)
        * comb(depth, ell) * comb(N * ell + exponent, order)
        for ell in range(depth + 1)
    ) % P


def first_defect_and_actual_residual():
    defects, shapes, coefficients = profile.defect_census()
    first = max(defects, key=lambda record: record[0])
    assert first == (ACTIVE, BLOCK_N, HOMOGENEOUS, 1, (14,), (), 1)
    assert (CONTACT_F, R_EXP, S_EXP) in shapes
    assert (CONTACT_F, R_EXP, S_EXP, Q) in coefficients

    chain = []
    for y in profile.raw_y_interval(ACTIVE, BLOCK_N, S_EXP):
        r = ACTIVE - y - S_EXP
        q = BLOCK_N - y + S_EXP
        width = profile.width(y, r, S_EXP)
        depth = min(profile.M - y, width // N)
        chain.append((y, r, S_EXP, q, depth, width, width - depth * N,
                      q < depth))
    assert tuple(record[0] for record in chain) == tuple(range(39, 54))
    assert chain[0] == (
        39, 14, 10, 15, 15, 4_191_058, 258_898, False)
    assert all(record[-1] for record in chain[1:])

    predecessors = []
    for h in range(profile.M - CONTACT_F):
        source_y = CONTACT_F + h
        active = source_y + R_EXP + S_EXP
        source_z = TARGET_Z - h
        width = profile.width(source_y, R_EXP, S_EXP)
        depth = min(profile.M - source_y, width // N)
        fringe = width - depth * N
        scalar = comb(source_y, CONTACT_F) % P
        assert scalar != 0
        predecessors.append((
            h, source_y, R_EXP, S_EXP, Q, source_z, active,
            depth, width, fringe, scalar,
        ))
    assert len(predecessors) == 30
    assert tuple(record[0] for record in predecessors) == tuple(range(30))
    assert tuple(record[9] for record in predecessors[:4]) == (
        258_898, 127_827, 258_900, 127_829)
    assert tuple(record[7] for record in predecessors[:4]) == (15, 15, 14, 14)

    # y=69 would be the h=30 correction, but violates y<M=69.  The special
    # terminal stream has y=70 and therefore reaches the same row with h=31.
    assert CONTACT_F + 30 == profile.M
    assert TERMINAL_Y == 70
    assert TERMINAL_Y - CONTACT_F == 31
    assert TARGET_Z == profile.L - profile.J + 31
    terminal_width = profile.width(TERMINAL_Y, R_EXP, S_EXP)
    terminal_hasse_dimension = terminal_width - Q
    terminal_scalar = comb(TERMINAL_Y, CONTACT_F) % P
    assert (terminal_width, terminal_hasse_dimension) == (127_857, 127_842)
    assert terminal_scalar != 0

    # Absorb all nonzero binomial scalars into the symbols.  Excluding the
    # current h=0 control, every actual incoming term has positive W power.
    actual_terms = (
        (("terminal_C15", 31, terminal_scalar),)
        + tuple((f"U{CONTACT_F+h}_15", h,
                 comb(CONTACT_F + h, CONTACT_F) % P)
                for h in range(1, 30))
    )
    assert min(power for _name, power, _scalar in actual_terms) == 1
    assert all(power >= 1 for _name, power, _scalar in actual_terms)

    return tuple(predecessors), {
        "first_descending_defect": first,
        "raw_chain_y_r_s_q_depth_width_fringe_legal": tuple(chain),
        "unique_omitted_physical_coefficient": (
            CONTACT_F, R_EXP, S_EXP, Q),
        "target_outer_z": TARGET_Z,
        "direct_predecessor_h_range": (0, 29),
        "direct_predecessor_formula": (
            "(y,r,s,q,z,A)=(39+h,14,10,15,2306-h,63+h), h=0..29; "
            "scalar=binom(39+h,39)"),
        "direct_predecessor_records": tuple(predecessors),
        "direct_predecessor_records_sha256": sha256_repr(tuple(predecessors)),
        "missing_h30_reason": "source y=69 violates correction cap y<M=69",
        "terminal_source_y_h_width": (TERMINAL_Y, 31, terminal_width),
        "terminal_normalized_H15_dimension": terminal_hasse_dimension,
        "terminal_scalar_binom_70_39_mod_p": terminal_scalar,
        "actual_incoming_residual": (
            "binom(70,39) W^31 C_15 + sum_(h=1)^29 "
            "binom(39+h,39) W^h U_(39+h,15)"),
        "actual_incoming_terms_name_Wpower_scalar": actual_terms,
        "actual_incoming_residual_has_common_factor_W": True,
        "actual_incoming_residual_vanishes_where_W_equals_zero": True,
    }


def first_four_hasse_prefix_gate(predecessors):
    digest = hashlib.sha256()
    records = []
    total = 0
    for record in predecessors[:4]:
        h, _y, _r, _s, _q, _z, _active, depth, _width, fringe, _scalar = record
        zero_weights = []
        first = last = None
        unique = set()
        for exponent in range(fringe):
            weight = normalized_hasse_weight(depth, exponent, Q)
            digest.update(struct.pack("<Q", weight))
            total += 1
            unique.add(weight)
            if first is None:
                first = weight
            last = weight
            if weight == 0:
                zero_weights.append(exponent)
        assert not zero_weights
        records.append((h, depth, fringe, first, last, len(unique)))

    assert total == 773_454
    # At depth=q the finite difference is the constant N^q.  At depth 14,
    # order 15 leaves an affine nonzero monomial weight on these prefixes.
    assert records[0][3:] == (pow(N, Q, P), pow(N, Q, P), 1)
    assert records[1][3:] == (pow(N, Q, P), pow(N, Q, P), 1)
    assert records[2][-1] == records[2][2]
    assert records[3][-1] == records[3][2]
    return {
        "normalized_map": (
            "A_h -> X^15 H_15((X^N-1)^depth_h A_h) at NTT nodes"),
        "first_four_h_depth_fringe_firstweight_lastweight_unique":
            tuple(records),
        "checked_weight_count": total,
        "zero_weights": (),
        "every_first_four_normalized_H15_map_is_a_diagonal_prefix_isomorphism":
            True,
        "packed_weight_sha256_u64": digest.hexdigest(),
        "resulting_four_prefix_map": (
            "F_<258898 + W F_<127827 + W^2 F_<258900 + "
            "W^3 F_<127829"),
    }


def terminal_hasse_gate():
    width = profile.width(TERMINAL_Y, R_EXP, S_EXP)
    digest = hashlib.sha256()
    zero = []
    for exponent in range(Q, width):
        weight = comb(exponent, Q) % P
        digest.update(struct.pack("<Q", weight))
        if weight == 0:
            zero.append(exponent)
    assert not zero
    assert width - Q == 127_842
    return {
        "normalized_terminal_map": "C -> X^15 H_15(C)",
        "coefficient_support_interval": (15, width - 1),
        "dimension": width - Q,
        "all_binomial_weights_nonzero": True,
        "packed_weight_sha256_u64": digest.hexdigest(),
        "actual_fixed_target_space": "W^31 * X^15 H_15(C)",
    }


def numerator_zero_split_gate():
    max_zeros = 149_776
    base_prefix = 258_898
    w_prefix = 127_827
    large_zero_threshold = N - w_prefix
    assert large_zero_threshold == 134_317
    assert max_zeros < base_prefix
    assert N - large_zero_threshold == w_prefix

    # If z>=134317, interpolate the target on Z with A0.  It can do so since
    # z<=149776<258898.  Then W*A1, which is zero on Z and invertible on Live,
    # corrects all remaining values because |Live|<=127827.
    for z in (large_zero_threshold, max_zeros):
        assert z <= base_prefix
        assert N - z <= w_prefix

    return {
        "full_leaf_numerator_degree_and_nodal_zero_cap": max_zeros,
        "first_defect_W0_prefix_dimension": base_prefix,
        "first_defect_W1_prefix_dimension": w_prefix,
        "zero_countergate_shape_base_prefix": ((0, 0, 0), 127_729),
        "countergate_does_not_transfer_to_first_defect": True,
        "reason": (
            "the first-defect base prefix 258898 exceeds every possible "
            "N0 nodal zero count 149776, and the actual incoming RHS is zero "
            "on that set anyway"),
        "large_zero_threshold": large_zero_threshold,
        "large_zero_two_channel_theorem": (
            "if 134317<=z<=149776, Lagrange-interpolate A0 on the z zeros; "
            "then interpolate A1=(target-A0)/W on the at most 127827 live "
            "nodes. Thus A0+W*A1 is onto all N coordinates."),
        "existing_no_wrap_numerator_degree_cutoff": 129_449,
        "unresolved_parameter_branch": (
            "129450<=deg(N0)<=149776 and nodalZeros(N0)<=134316"),
        "actual_W_positive_target_removes_only_zero_supported_duals": True,
        "W_positive_alone_proves_four_prefix_membership": False,
    }


def main():
    for filename, expected in AUTHORITIES.items():
        assert file_sha256(HERE / filename) == expected
    predecessors, actual = first_defect_and_actual_residual()
    prefixes = first_four_hasse_prefix_gate(predecessors)
    terminal = terminal_hasse_gate()
    zero_split = numerator_zero_split_gate()
    stable = {
        "scope": (
            "exact first descending m69 Pascal defect and its literal actual "
            "C/U residual; no claim about later defects or full confluence"),
        "profile_M_slope_curvature_J_L": (
            profile.M, profile.SLOPE, profile.CURVATURE,
            profile.J, profile.L),
        "authority_sha256": tuple(sorted(AUTHORITIES.items())),
        "first_defect_actual_residual": actual,
        "first_four_literal_prefix_channels": prefixes,
        "terminal_H15_space": terminal,
        "numerator_zero_split": zero_split,
        "decision": (
            "GREEN_FIRST_DEFECT_ACTUAL_RHS_HAS_W_FACTOR__"
            "GREEN_LARGE_ZERO_TWO_CHANNEL_BRANCH__"
            "STOP_HIGH_NUMERATOR_SMALL_ZERO_FOUR_PREFIX_CONTAINMENT"),
        "scope_guard": (
            "The cb97180 numerator-zero dual is harmless at the first defect. "
            "This does not prove that every other four-prefix cokernel vector "
            "annihilates W^31*H15(C), nor does it solve the remaining "
            "129450..149776 numerator-degree branch with <=134316 nodal zeros."),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    assert peak < 512 * 1024
    print(json.dumps({
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": file_sha256(Path(__file__)),
        "peak_rss_kib": peak,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
