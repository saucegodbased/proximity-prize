#!/usr/bin/env python3
"""Exact extra-node low-head factorization and independence gate.

For the faithful F101 m8 chamber, let ``head`` be contact at the nine old
nodes restricted to epsilon orders 0,...,4.  At the fresh boundary node x=9,
form a compatible local probe using the candidate P, agreement tangent Q,
and seed gamma.  This script proves coefficientwise on every source monomial
that the four raw boundary derivatives factor through that local probe:

    F_Y = [eps^3 T] probe(F)
    F_R = d_R [eps^0] probe(F)
    F_S = d_S [eps^0] probe(F)
    F_Z = d_Z [eps^0] probe(F) - u1 * F_Y.

It then tests the genuinely load-bearing finite statement

    rank(head, probe) = rank(head) + rank(probe),

i.e. the fresh probe image is independent modulo the old-node head image.
Codomains here are the actual images of the two maps, not their larger raw
row universes.  Exact arithmetic is over F101 under a hard 4.2 GB cap.
"""

from __future__ import annotations

from dataclasses import asdict, replace
import gc
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import k0_capacity_positive_layer_attribution_6900 as Layer  # noqa: E402
import k0_corrected_terminal_connecting_transpose_gate_6900 as Gate  # noqa: E402
import k0_degree4_degree5_full_sr_attribution_6900 as Degree  # noqa: E402
import k0_first_positive_passive_universal_falsifier_6900 as Old  # noqa: E402
from k0_centered_head_y_correction_gate_6900 import (  # noqa: E402
    flattened_raw_column,
)


P = Gate.P
ADDRESS_SPACE_CAP_BYTES = Gate.ADDRESS_SPACE_CAP_BYTES
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
if soft < 0 or soft > ADDRESS_SPACE_CAP_BYTES:
    resource.setrlimit(resource.RLIMIT_AS,
                       (ADDRESS_SPACE_CAP_BYTES, hard))


def local_probe_column(monomial, x, u0, u1, m, head_cutoff):
    return {row: value for row, value in flattened_raw_column(
        monomial, x, u0, u1, m).items() if row[0] < head_cutoff}


def power(base, exponent):
    return pow(base % P, exponent, P)


def evaluate_local(poly, S0, R0, Z0):
    """Evaluate a local polynomial after eps=T=0."""
    answer = 0
    for (eps, s, t, r, z), coefficient in poly.items():
        if eps or t:
            continue
        answer += (coefficient * power(S0, s) * power(R0, r) *
                   power(Z0, z))
    return answer % P


def local_partial_at_eps0(poly, coordinate, S0, R0, Z0):
    """Derivative in local S/R/Z (indices 1/3/4) at eps=T=0."""
    answer = 0
    for monomial, coefficient in poly.items():
        eps, s, t, r, z = monomial
        exponents = (s, r, z)
        if eps or t:
            continue
        j = {1: 0, 3: 1, 4: 2}[coordinate]
        if exponents[j] == 0:
            continue
        value = coefficient * exponents[j]
        bases = (S0, R0, Z0)
        for k, (base, exponent) in enumerate(zip(bases, exponents)):
            value *= power(base, exponent - (k == j))
        answer += value
    return answer % P


def eps3_t_readout(poly, S0, R0, Z0):
    """Evaluate the coefficient of eps^3*T at local S/R/Z."""
    answer = 0
    for (eps, s, t, r, z), coefficient in poly.items():
        if eps != 3 or t != 1:
            continue
        answer += (coefficient * power(S0, s) * power(R0, r) *
                   power(Z0, z))
    return answer % P


def probe_readout(poly, u1, S0, R0, Z0):
    y = eps3_t_readout(poly, S0, R0, Z0)
    r = local_partial_at_eps0(poly, 3, S0, R0, Z0)
    s = local_partial_at_eps0(poly, 1, S0, R0, Z0)
    z = (local_partial_at_eps0(poly, 4, S0, R0, Z0) - u1 * y) % P
    return (y, r, s, z)


def fill_matrix(columns, rows, label):
    row_index = {row: i for i, row in enumerate(rows)}
    matrix = nmod_mat(len(rows), len(columns), P)
    for j, column in enumerate(columns, start=1):
        for row, value in column.items():
            matrix[row_index[row], j - 1] = value
        if j % 1000 == 0:
            print(f"fill {label} {j}/{len(columns)}", file=sys.stderr,
                  flush=True)
    return matrix


def exact_rank(columns, rows, label):
    matrix = fill_matrix(columns, rows, label)
    print(f"rref {label}: {matrix.nrows()}x{matrix.ncols()}",
          file=sys.stderr, flush=True)
    _, rank = matrix.rref(inplace=True)
    del matrix
    gc.collect()
    return rank


def exact_old_rank(profile, receipt, monomials, rows, head_cutoff):
    row_index = {row: i for i, row in enumerate(rows)}
    matrix = nmod_mat(len(rows), len(monomials), P)
    for j, monomial in enumerate(monomials, start=1):
        for row, value in Gate.formal_column(
                profile, receipt, monomial).items():
            i = row_index.get(row)
            if i is not None and row[1] < head_cutoff:
                matrix[i, j - 1] = value
        if j % 1000 == 0:
            print(f"fill old low head {j}/{len(monomials)}",
                  file=sys.stderr, flush=True)
    print(f"rref old low head: {matrix.nrows()}x{matrix.ncols()}",
          file=sys.stderr, flush=True)
    _, rank = matrix.rref(inplace=True)
    del matrix
    gc.collect()
    return rank


def exact_joint_rank(profile, receipt, monomials, probe_columns,
                     old_rows, probe_rows, head_cutoff):
    old_index = {row: i for i, row in enumerate(old_rows)}
    probe_index = {row: len(old_rows) + i
                   for i, row in enumerate(probe_rows)}
    matrix = nmod_mat(len(old_rows) + len(probe_rows), len(monomials), P)
    for j, (monomial, probe) in enumerate(
            zip(monomials, probe_columns), start=1):
        for row, value in Gate.formal_column(
                profile, receipt, monomial).items():
            i = old_index.get(row)
            if i is not None and row[1] < head_cutoff:
                matrix[i, j - 1] = value
        for row, value in probe.items():
            matrix[probe_index[row], j - 1] = value
        if j % 1000 == 0:
            print(f"fill old+probe {j}/{len(monomials)}",
                  file=sys.stderr, flush=True)
    print(f"rref old+probe: {matrix.nrows()}x{matrix.ncols()}",
          file=sys.stderr, flush=True)
    _, rank = matrix.rref(inplace=True)
    del matrix
    gc.collect()
    return rank


def boundary_gain_on_probe_kernel(probe_columns, probe_rows, boundaries):
    matrix = fill_matrix(probe_columns, probe_rows, "probe factorization")
    print(f"rref probe factorization: {matrix.nrows()}x{matrix.ncols()}",
          file=sys.stderr, flush=True)
    _, rank = matrix.rref(inplace=True)
    pivots = Layer.pivot_columns(matrix, rank)
    pivot_set = set(pivots)
    basis = {}
    for column in range(matrix.ncols()):
        if column in pivot_set:
            continue
        residual = list(boundaries[column])
        for row, pivot_column in enumerate(pivots):
            coefficient = int(matrix[row, column]) % P
            if coefficient:
                old = boundaries[pivot_column]
                residual = [(value - coefficient * old[i]) % P
                            for i, value in enumerate(residual)]
        Gate.add_boundary_basis(basis, tuple(residual))
    del matrix
    gc.collect()
    return rank, len(basis), Gate.basis_vectors(basis)


def main():
    started = time.monotonic()
    profile = replace(Degree.PROFILE, L=10)
    receipt = Degree.Full.M8.monomial_tangent_receipt(
        profile, Degree.TRIAL, 0)
    monomials = tuple(Degree.K0.support(profile))
    assert len(monomials) == 11178
    head_cutoff = profile.m - 3
    extra_x = profile.n
    gamma = receipt.seed % P
    candidate_value = Old.evaluate(receipt.polynomial, extra_x, P)
    u1 = Old.evaluate(receipt.tangent, extra_x, P)
    u0 = (candidate_value - gamma * u1) % P
    R0 = Old.evaluate(receipt.polynomial, extra_x, P, 1)
    S0 = Old.evaluate(receipt.polynomial, extra_x, P, 2) \
        * pow(2, -1, P) % P

    probe_columns = []
    old_rows_set = set()
    probe_rows_set = set()
    boundaries = []
    for position, monomial in enumerate(monomials, start=1):
        old = {row: value for row, value in Gate.formal_column(
            profile, receipt, monomial).items() if row[1] < head_cutoff}
        probe = local_probe_column(
            monomial, extra_x, u0, u1, profile.m, head_cutoff)
        boundary = Gate.formal_boundary(profile, receipt, monomial)
        # This is the semantic factorization check, on every actual basis
        # monomial rather than on a random sample.
        assert probe_readout(probe, u1, S0, R0, gamma) == boundary
        probe_columns.append(probe)
        boundaries.append(boundary)
        old_rows_set.update(old)
        probe_rows_set.update(probe)
        if position % 1000 == 0:
            print(f"generate/factor {position}/{len(monomials)}",
                  file=sys.stderr, flush=True)
    probe_columns = tuple(probe_columns)
    boundaries = tuple(boundaries)
    old_rows = tuple(sorted(old_rows_set, key=repr))
    probe_rows = tuple(sorted(probe_rows_set, key=repr))

    # Primitive images give an explicit four-axis section of readout.
    primitives = (
        (0, 1, 0, 0, 0),  # Y
        (0, 0, 1, 0, 0),  # R
        (0, 0, 0, 1, 0),  # S
        (0, 0, 0, 0, 1),  # Z
    )
    primitive_readouts = tuple(probe_readout(
        local_probe_column(q, extra_x, u0, u1, profile.m, head_cutoff),
        u1, S0, R0, gamma) for q in primitives)
    assert primitive_readouts == (
        (1, 0, 0, 0), (0, 1, 0, 0),
        (0, 0, 1, 0), (0, 0, 0, 1))
    assert all(q in set(monomials) for q in primitives)

    probe_rank, probe_kernel_boundary_gain, probe_kernel_boundary_basis = \
        boundary_gain_on_probe_kernel(
            probe_columns, probe_rows, boundaries)
    assert probe_kernel_boundary_gain == 0

    old_rank = exact_old_rank(
        profile, receipt, monomials, old_rows, head_cutoff)
    joint_rank = exact_joint_rank(
        profile, receipt, monomials, probe_columns, old_rows, probe_rows,
        head_cutoff)
    joint_row_count = len(old_rows) + len(probe_rows)
    independent = joint_rank == old_rank + probe_rank
    assert (old_rank, probe_rank, joint_rank) == (4734, 526, 5260)
    assert independent

    stable = {
        "scope": (
            "faithful F101 m8 extra-node low-head readout factorization and "
            "joint-image independence gate"),
        "field": P,
        "profile_n_w_g_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "agreement_set": receipt.agreement,
        "old_nodes_and_extra_node": (receipt.nodes, extra_x),
        "low_head_and_terminal_epsilon_orders": (
            tuple(range(head_cutoff)),
            tuple(range(head_cutoff, profile.m))),
        "extra_anchor_u0_u1_seed_candidate_R_Hasse2S": (
            u0, u1, gamma, candidate_value, R0, S0),
        "readout_formula": (
            "Y=[eps^3*T]G; R=d_R[eps^0]G; S=d_S[eps^0]G; "
            "Z=d_Z[eps^0]G-u1*Y, evaluated at (S,R,Z)="
            "(Hasse2(P),P',gamma)"),
        "all_source_monomials_factorization_checked": len(monomials),
        "primitive_Y_R_S_Z_readouts": primitive_readouts,
        "primitive_four_axis_section_source_legal": True,
        "old_probe_joint_row_counts": (
            len(old_rows), len(probe_rows), joint_row_count),
        "old_probe_joint_ranks": (old_rank, probe_rank, joint_rank),
        "probe_kernel_boundary_gain_and_basis": (
            probe_kernel_boundary_gain, probe_kernel_boundary_basis),
        "boundary_factors_through_probe":
            probe_kernel_boundary_gain == 0,
        "probe_readout_surjective": True,
        "joint_rank_equals_sum": independent,
        "joint_map_onto_product_of_actual_images": independent,
        "verdict": (
            "GREEN" if independent else
            "RED: extra probe has a nonzero coupling defect modulo old head"),
        "codomain_guard": (
            "Surjectivity is onto range(old head) x range(extra probe), not "
            "onto the larger syntactic row universes. This is the exact "
            "finite strictness statement needed after replacing codomains "
            "by their images."),
        "scope_guard": (
            "Finite receipt-specific evidence only. It neither proves the "
            "target joint rank nor constructs a target capped CRT section."),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    payload = {
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(
            Path(__file__).read_bytes()).hexdigest(),
        "runtime": {
            "seconds": round(time.monotonic() - started, 3),
            "peak_rss_kib": resource.getrusage(
                resource.RUSAGE_SELF).ru_maxrss,
            "hard_address_space_cap_bytes": ADDRESS_SPACE_CAP_BYTES,
        },
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
