#!/usr/bin/env python3
"""Complete direct-predecessor universal STOP for the Full187 A57 quotient.

Commit 8b1b1fc closes the A57 missing quotient for one frozen u1, while
49afff4 gives a hostile high/root-free monomial for the first h=1 rescue.
This script enumerates *every* physical u0-free predecessor which can survive
the committed A57 scalar dual, not just the nearest one.

There is exactly one source shape for each frozen-U power h=0..23.  After all
earlier coefficient jets are preserved, its remaining window is strictly
smaller than N.  For u1=X^133120, the normalized H12 map is diagonal on
coefficient monomials and each family is contained in an explicit shifted
interval.  The union of all 24 intervals is exactly 0..255162; exhaustive
exact weights are nonzero, so the image rank is exactly 255163 and the suffix
255163..262143 is an exact 6981-dimensional cokernel.

This is a structural STOP only for the complete direct u0-free predecessor
rescue.  It does not exclude a theorem restricting the actual packet RHS or
a source mechanism outside this physical family.
"""

from __future__ import annotations

from math import comb
import hashlib
import json
from pathlib import Path
import resource
import struct

import full187_a57_partial_fringe_lowerz_rescue_gate_6900 as A57
import full187_parametric_pascal_straightening_window_gate_6900 as S


P = S.P
N = S.N
M = S.M
J = S.F.J
OUTER_Z = S.OUTER_Z
HOSTILE_DEGREE = 133_120
MISSING_EXPONENT = 255_163

AUTHORITIES = {
    "full187_a57_partial_fringe_lowerz_rescue_gate_6900.py":
        "ec5116b762db74f106a6e25c79cdba494263df020efc4ba6727730f931649d39",
    "full187_parametric_pascal_straightening_window_gate_6900.py":
        "f9c504d835c2a47009da6b27eef7b9d1f43535f11501ed960e2c94d9ae50a951",
    "Full187A57UniversalHighDirectionCountergate6900.lean":
        "b5a9ad24f5a92ca16d666ff70a9407fefd50e9183926049a46f595b3eae98fb2",
    "LowReceivedDirectionScalarSplit1331196900.lean":
        "6852d3896d787c2cd9502aafe5ca69a9faecace833744ed8702cb768f7443501",
}


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def predecessor_fringe(h):
    k = h // 2
    return 208_036 + 2 * k if h % 2 == 0 else 76_965 + 2 * k


def hostile_shift(h):
    return h * HOSTILE_DEGREE % N


def complete_physical_predecessor_census():
    """Invert every u0-free physical source surviving the A57 raw dual."""
    rows, raw57, legal57, omitted_key, _omitted_column, dual = (
        A57.a57_missing_dual_data())
    del rows, raw57, legal57, dual
    assert omitted_key == (36, 11, 10, 12, OUTER_Z)

    records = []
    for h in range(M):
        contact_f, r, s, q, target_z = omitted_key
        # omitted_key is ordered (y=f,r,s,q,z), so spell this out rather
        # than silently identifying its first field with a source exponent.
        assert (contact_f, r, s, q, target_z) == (
            36, 11, 10, 12, OUTER_Z)
        source_y = contact_f + h
        if source_y >= M:
            continue
        source_z = target_z - h
        active = source_y + r + s
        selected, depths, _rank = S.minimal_prefix_basis(
            active, enforce_capacity=True)
        del selected
        depth = dict(depths)[(source_y, r, s)]
        width = S.F.H.width(source_y, r, s)
        quotient_dimension = width - depth * N
        scalar = comb(source_y, contact_f) % P
        assert scalar
        record = (
            h, source_y, r, s, q, source_z, active, depth, width,
            quotient_dimension, scalar,
        )
        records.append(record)

    assert len(records) == 24
    assert tuple(record[0] for record in records) == tuple(range(24))
    for h, source_y, r, s, q, source_z, active, depth, width, fringe, _scalar in records:
        k = h // 2
        assert (source_y, r, s, q, source_z, active) == (
            36 + h, 11, 10, 12, OUTER_Z - h, 57 + h)
        if h % 2 == 0:
            assert (depth, fringe) == (12 - k, 208_036 + 2 * k)
        else:
            assert (depth, fringe) == (12 - k, 76_965 + 2 * k)
        assert fringe == predecessor_fringe(h) < N
        assert width == 3_353_764 - h * 131_071

    census_hash = hashlib.sha256(repr(tuple(records)).encode()).hexdigest()
    assert census_hash == (
        "073cdc3855beff6fd4d768344b1fcaae8b28f39fd7e04761ef817bace4442865")
    return tuple(records), {
        "a57_dual_visible_contact_f_r_s_q_target_z": omitted_key,
        "complete_h_range": (0, 23),
        "physical_predecessor_count": len(records),
        "source_formula": (
            "(y,r,s,q,z,A)=(36+h,11,10,12,2625-h,57+h); "
            "h=0..23; scalar=binom(36+h,36)"),
        "prefix_depth_formula": (
            "d_(2k)=12-k and d_(2k+1)=12-k"),
        "residual_dimension_formula": (
            "rho_(2k)=208036+2k and rho_(2k+1)=76965+2k"),
        "every_residual_strictly_below_N": True,
        "coefficient_independent_full_node_or_constant_channel": False,
        "records_sha256": census_hash,
        "records": tuple(records),
    }


def normalized_hasse_weight(depth, exponent):
    """X^exponent weight in X^12 H12(Omega^depth * X^exponent).

    Expanding Omega^d=(X^N-1)^d and evaluating at an N-th root leaves
    X^exponent times this scalar.  Division by N^12 is an irrelevant common
    unit, so only nonvanishing is used for exact rank.
    """
    return sum(
        (-1 if (depth - ell) % 2 else 1)
        * comb(depth, ell) * comb(N * ell + exponent, 12)
        for ell in range(depth + 1)
    ) % P


def hostile_monomial_complete_image(records):
    """Exact support/rank for u1=X^133120 for all 24 source kernels."""
    assert HOSTILE_DEGREE >= 133_120
    # X^d is nonzero on every NTT node because every node is nonzero.
    assert HOSTILE_DEGREE < N
    support = set()
    weight_digest = hashlib.sha256()
    weight_count = 0
    zero_weights = []
    interval_records = []

    for record in records:
        h, _y, _r, _s, _q, _z, _active, depth, _width, fringe, _scalar = record
        shift = hostile_shift(h)
        interval_start = shift
        interval_end = shift + fringe - 1
        assert interval_end < N  # no cyclic wrap in this hostile family
        expected_shift = (
            4_096 * (h // 2)
            if h % 2 == 0 else 133_120 + 4_096 * (h // 2))
        assert shift == expected_shift

        for exponent in range(fringe):
            weight = normalized_hasse_weight(depth, exponent)
            weight_digest.update(struct.pack("<Q", weight))
            weight_count += 1
            if not weight:
                zero_weights.append((h, depth, exponent))
                continue
            support.add(shift + exponent)

        if h % 2 == 0:
            k = h // 2
            assert (interval_start, interval_end) == (
                4_096 * k, 208_035 + 4_098 * k)
        else:
            k = h // 2
            assert (interval_start, interval_end) == (
                133_120 + 4_096 * k, 210_084 + 4_098 * k)
        interval_records.append((
            h, depth, fringe, shift, interval_start, interval_end))

    assert not zero_weights
    assert weight_count == 3_420_276
    assert support == set(range(MISSING_EXPONENT))
    defect = N - len(support)
    assert (len(support), defect) == (255_163, 6_981)
    interval_hash = hashlib.sha256(
        repr(tuple(interval_records)).encode()).hexdigest()
    support_hash = hashlib.sha256(
        repr(tuple(sorted(support))).encode()).hexdigest()
    assert interval_hash == (
        "0c86fdc65b5b2e27a5150efbc74367a02911ffb630773460cf3c321d6a6d9b4e")
    assert support_hash == (
        "f11f0cf353961207be5353c6b11653a22a65ea47bac54c8174177553ec2da439")
    assert weight_digest.hexdigest() == (
        "df51951c7566457fd6d25d97c42ce46612db1b7851fe9d0975e12aee55b08077")

    return {
        "hostile_received_direction": "u1=X^133120",
        "high_degree_and_root_free_on_NTT_domain": True,
        "normalized_family_map": (
            "V_h -> X^(h*133120 mod 262144)*V_h; "
            "deg(V_h)<rho_h; exact H12 monomial weights retained"),
        "even_interval_formula": (
            "h=2k: [4096k,208035+4098k], 0<=k<=11"),
        "odd_interval_formula": (
            "h=2k+1: [133120+4096k,210084+4098k], 0<=k<=11"),
        "interval_records": tuple(interval_records),
        "interval_records_sha256": interval_hash,
        "exact_hasse_weight_count": weight_count,
        "zero_hasse_weights": tuple(zero_weights),
        "all_exact_hasse_weights_nonzero": True,
        "all_hasse_weights_sha256_u64": weight_digest.hexdigest(),
        "exact_image_support": (0, MISSING_EXPONENT - 1),
        "exact_image_support_sha256": support_hash,
        "exact_image_rank": len(support),
        "exact_cokernel_suffix": (MISSING_EXPONENT, N - 1),
        "exact_cokernel_dimension": defect,
        "explicit_missing_coefficient": MISSING_EXPONENT,
        "decision": "RED_ALL_24_DIRECT_U0FREE_PREDECESSORS",
    }


def actual_rhs_confinement_audit():
    """Record the theorem-interface search, without inventing confinement."""
    # The universal endpoint cut quantifies arbitrary U, seeds, agreement
    # sets, and selected low-degree polynomials.  No imported premise states
    # that the Full187 A57 quotient RHS lies in the 255163-prefix image (or
    # annihilates coefficient 255163).  The earlier raw module deliberately
    # accepts arbitrary incoming coefficient functions.  A target-instance
    # zero or sampled RHS is therefore not a universal theorem.
    return {
        "endpoint_authority_commit": "f8560b5",
        "universal_promotion_countergate_commit": "49afff4",
        "corrected_compiled_high_branch": (
            "LowReceivedDirectionScalarSplit1331196900: natDegree(u1)>=133120"),
        "searched_invariants": (
            "A57/n38/q12", "actual residual factorization",
            "universal high-direction endpoint premises"),
            "existing_theorem_forcing_rhs_coeff_255163_zero": False,
        "endpoint_premises_include_rhs_support_or_Hankel_condition": False,
        "honest_status": (
            "No already-present theorem confines the actual universal packet "
            "RHS away from the hostile suffix. Proving such confinement is "
            "a new mathematical obligation; this gate does not assume it."),
    }


def main():
    here = Path(__file__).resolve().parent
    for filename, expected in AUTHORITIES.items():
        assert file_sha256(here / filename) == expected
    records, census = complete_physical_predecessor_census()
    hostile = hostile_monomial_complete_image(records)
    rhs = actual_rhs_confinement_audit()
    stable = {
        "scope": (
            "complete direct u0-free physical predecessor family for the "
            "A57 missing scalar quotient under universal high/root-free u1; "
            "no frozen-target cascade, no indirect new source mechanism, "
            "and no production/submission change"),
        "target_p_N_M_J_outerZ": (P, N, M, J, OUTER_Z),
        "authority_sha256": tuple(sorted(AUTHORITIES.items())),
        "complete_physical_predecessor_census": census,
        "hostile_monomial_complete_image": hostile,
        "actual_universal_rhs_confinement_audit": rhs,
        "decision": (
            "STRUCTURAL_STOP_COMPLETE_DIRECT_U0FREE_PREDECESSOR_RESCUE__"
            "HOSTILE_MONOMIAL_EXACT_DEFECT_6981__"
            "NO_EXISTING_ACTUAL_RHS_CONFINEMENT_THEOREM"),
        "scope_guard": (
            "The STOP covers all 24 direct u0-free predecessors visible to "
            "the exact A57 dual. It does not prove the universal bad-family "
            "theorem false and does not exclude a separate count of "
            "deficient directions, an indirect source family, or a newly "
            "proved actual-RHS confinement invariant."),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    peak_rss_kib = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    assert peak_rss_kib < 3 * 1024 * 1024
    print(json.dumps({
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": file_sha256(Path(__file__)),
        "peak_rss_kib": peak_rss_kib,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
