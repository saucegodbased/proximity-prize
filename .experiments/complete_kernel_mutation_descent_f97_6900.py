#!/usr/bin/env python3
"""Exact coupled CRT/Hermite filtering and mutation-descent discriminator.

This is a lower-6900 research experiment only.  It reuses the frozen F97,
N=8 contact fixture where every individual canonical CRT/Hermite generator
is source-illegal, then asks whether *all coupled combinations* recover the
literal filtered contact kernel.  A second stage fixes the four boundary
values at the off-domain probe and reduces an unconstrained CRT lift by
boundary-zero contact mutations in one declared tapered monomial order.

The calculation is deliberately finite and exact.  Any triangular moves
reported below are Gaussian closure of the complete finite mutation space;
they are not advertised as a target-scale recurrence or a theorem that the
same leaders persist when the caps change.
"""

from __future__ import annotations

import hashlib
import json
import resource
import sys
import time

from flint import nmod_mat

import abr4_crt_hermite_cap_generator_gate_6900 as base


P = base.P


def all_ambient_columns(u1_values):
    """A triangularly complete bounded normal-coordinate simplex.

    Unlike the frozen *individual-filtering* test, normal ``R,S`` exponents
    are not cut by the ordinary derivative faces.  Rewriting an admitted
    ordinary ``Y`` as ``F + U0 + U1*Z + T*R - T^2*S/2`` can move its active
    degree into either normal derivative exponent.  The invariant bounds are
    therefore only ``b+r+s <= ACTIVE_CAP`` and
    ``b+r+s+z <= SEED_CAP``.  Reimposing the ordinary ``r+s`` and ``s`` caps
    here is exactly the incomplete ambient-generator filtering under audit.
    """
    f = base.contact_normal(u1_values)
    f_powers = tuple(base.normal_pow(f, b)
                     for b in range(base.ACTIVE_CAP + 1))
    labels = []
    columns = []
    for b in range(base.ACTIVE_CAP + 1):
        for r in range(base.ACTIVE_CAP - b + 1):
            for s in range(base.ACTIVE_CAP - b - r + 1):
                for z in range(base.SEED_CAP - b - r - s + 1):
                    for h in range(base.M):
                        if h + 3 * b < base.M:
                            continue
                        for a in range(base.N):
                            prefix = {(a, h, 0, r, s, z): 1}
                            ordinary = base.pullback(
                                base.normal_mul(prefix, f_powers[b]))
                            if ordinary:
                                labels.append((a, h, b, r, s, z))
                                columns.append(ordinary)
    assert len(columns) == 6048
    return tuple(labels), tuple(columns)


def shifted_key(monomial):
    """The predeclared shifted/tapered monomial order.

    This is the literal F97 analogue of the archived term-over-shape order

        (a + w*y + (w-1)*r + (w-2)*s, y+r+s+z, z,s,r,y,a).

    Every entry is additive under monomial multiplication, and the final
    exponent tie-breakers make the key injective.  Lexicographic comparison
    is consequently a genuine monomial order, not a post-hoc ordering by a
    clipped cap-defect function.  We take the greatest *illegal* monomial as
    the rewrite leader.
    """
    xp, y, r, s, z = monomial
    slope = r + s
    active = y + slope
    seed = active + z
    shifted_x = xp + base.W * y + (base.W - 1) * r + (base.W - 2) * s
    return (shifted_x, seed, z, s, r, y, xp)


def dense_from_sparse(rows, columns):
    return nmod_mat(len(rows), len(columns), [
        columns[column].get(row, 0)
        for row in rows for column in range(len(columns))
    ], P)


def boundary_at_probe(column):
    units = ((1, 0, 0, 0), (0, 1, 0, 0),
             (0, 0, 1, 0), (0, 0, 0, 1))
    answer = []
    for unit in units:
        value = 0
        for (xp, y, r, s, z), coefficient in column.items():
            if (y, r, s, z) == unit:
                value = (value + coefficient * pow(base.PROBE, xp, P)) % P
        answer.append(value)
    return tuple(answer)


def add_scaled(target, source, scalar):
    for monomial, coefficient in source.items():
        value = (target.get(monomial, 0) + scalar * coefficient) % P
        if value:
            target[monomial] = value
        else:
            target.pop(monomial, None)


def independent_column_indices(vectors):
    chosen = []
    old_rank = 0
    for index, _ in enumerate(vectors):
        trial = nmod_mat(4, len(chosen) + 1, [
            vectors[j][i] for i in range(4)
            for j in chosen + [index]
        ], P)
        rank = trial.rank()
        if rank > old_rank:
            chosen.append(index)
            old_rank = rank
            if rank == 4:
                break
    assert old_rank == 4
    return tuple(chosen)


def raw_boundary_mutation_profile(label, u1_values):
    """Profile the uncompleted, boundary-zero CRT mutations.

    Four ambient columns give a section of boundary evaluation.  Subtracting
    that section from every other ambient column gives a fixed generating set
    of the complete boundary-zero mutation space without solving any illegal
    rows.  If its distinct raw leaders do not reach the exact mutation-image
    rank, the declared order is not a complete rewrite system: new leaders
    must be manufactured by coupled S-polynomials/global elimination.
    """
    labels, columns = all_ambient_columns(u1_values)
    betas = tuple(boundary_at_probe(column) for column in columns)
    pivots = independent_column_indices(betas)
    pivot_matrix = nmod_mat(4, 4, [
        betas[pivots[j]][i] for i in range(4) for j in range(4)
    ], P)
    inverse = pivot_matrix.inv()

    raw_leaders = {}
    support_sizes = []
    zero_mutations = 0
    for j, column in enumerate(columns):
        if j in pivots:
            continue
        alpha = [
            sum(int(inverse[i, k]) * betas[j][k] for k in range(4)) % P
            for i in range(4)
        ]
        mutation = dict(column)
        for i, coefficient in enumerate(alpha):
            add_scaled(mutation, columns[pivots[i]], -coefficient)
        assert boundary_at_probe(mutation) == (0, 0, 0, 0)
        illegal_support = tuple(
            monomial for monomial in mutation if not base.source_legal(monomial))
        if not illegal_support:
            zero_mutations += 1
            continue
        leader = max(illegal_support, key=shifted_key)
        raw_leaders[leader] = raw_leaders.get(leader, 0) + 1
        support_sizes.append(len(illegal_support))

    actual_contact = base.contact_matrix(u1_values)
    literal_kernel, actual_nullity = actual_contact.nullspace()
    # Polynomial boundary rank agrees with probe rank in this fixture; we
    # recompute the probe restriction directly on the literal kernel.
    literal_beta = nmod_mat(4, len(base.SOURCE), [
        boundary_at_probe({monomial: 1})[i]
        for i in range(4) for monomial in base.SOURCE
    ], P)
    filtered_boundary = literal_beta * literal_kernel
    filtered_boundary_rank = filtered_boundary.rank()
    boundary_dual, boundary_dual_nullity = filtered_boundary.transpose().nullspace()
    boundary_dual_vectors = tuple(
        tuple(int(boundary_dual[i, j]) % P for i in range(4))
        for j in range(boundary_dual_nullity)
    )
    missing_unit = None
    missing_pairing = None
    if boundary_dual_vectors:
        witness = boundary_dual_vectors[0]
        missing_unit = next(i for i, coefficient in enumerate(witness)
                            if coefficient)
        missing_pairing = witness[missing_unit]
        assert all(
            sum(witness[i] * int(filtered_boundary[i, j])
                for i in range(4)) % P == 0
            for j in range(filtered_boundary.ncols())
        )
    mutation_image_rank = (
        len(columns) - 4 - (actual_nullity - filtered_boundary_rank))

    leader_counts = sorted(raw_leaders.values(), reverse=True)
    result = {
        "label": label,
        "ambient_columns_boundary_pivots": (len(columns), pivots),
        "individually_source_legal_ambient_columns": sum(
            bool(column) and all(base.source_legal(monomial)
                                 for monomial in column)
            for column in columns),
        "boundary_pivot_normal_labels": tuple(labels[j] for j in pivots),
        "literal_nullity_probe_boundary_rank": (
            actual_nullity, filtered_boundary_rank),
        "probe_boundary_annihilator_basis": boundary_dual_vectors,
        "first_missing_unit_residual_index_pairing": (
            missing_unit, missing_pairing),
        "exact_boundary_zero_mutation_illegal_image_rank": mutation_image_rank,
        "raw_nonzero_zero_illegal_mutations": (
            len(support_sizes), zero_mutations),
        "distinct_raw_illegal_leaders": len(raw_leaders),
        "missing_leaders_requiring_coupled_closure_at_least":
            mutation_image_rank - len(raw_leaders),
        "raw_leader_max_multiplicity": max(leader_counts, default=0),
        "raw_illegal_support_min_max_sum": (
            min(support_sizes, default=0), max(support_sizes, default=0),
            sum(support_sizes)),
        "top_raw_leaders_with_multiplicity": tuple(sorted(
            raw_leaders.items(), key=lambda pair: shifted_key(pair[0]),
            reverse=True)[:12]),
    }
    return result


def mat_hash(matrix):
    payload = {
        "nrows": matrix.nrows(),
        "ncols": matrix.ncols(),
        "entries": [int(matrix[i, j]) % P
                    for i in range(matrix.nrows())
                    for j in range(matrix.ncols())],
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode()).hexdigest()


def one_case(label, u1_values):
    labels, columns = all_ambient_columns(u1_values)
    all_rows = set().union(*(column.keys() for column in columns))
    legal_rows = tuple(base.SOURCE)
    legal_set = set(legal_rows)
    illegal_rows = tuple(sorted(all_rows - legal_set,
                                key=shifted_key, reverse=True))
    assert all(not base.source_legal(row) for row in illegal_rows)
    assert all(base.source_legal(row) for row in legal_rows)

    illegal = dense_from_sparse(illegal_rows, columns)
    coefficient_kernel, coefficient_nullity = illegal.nullspace()
    legal = dense_from_sparse(legal_rows, columns)
    coupled = legal * coefficient_kernel
    coupled_rank = coupled.rank()

    contact = base.contact_matrix(u1_values)
    actual_kernel, actual_nullity = contact.nullspace()
    coupled_contact_rank = (contact * coupled).rank()
    joined_rank = nmod_mat(legal.nrows(), coupled.ncols() + actual_kernel.ncols(), [
        int(coupled[i, j]) if j < coupled.ncols()
        else int(actual_kernel[i, j - coupled.ncols()])
        for i in range(legal.nrows())
        for j in range(coupled.ncols() + actual_kernel.ncols())
    ], P).rank()

    beta_ambient = nmod_mat(4, len(columns), [
        boundary_at_probe(columns[j])[i]
        for i in range(4) for j in range(len(columns))
    ], P)
    beta_coupled = beta_ambient * coefficient_kernel

    return {
        "label": label,
        "ambient_columns": len(columns),
        "ambient_rows_legal_illegal": (
            len(all_rows), len(legal_rows), len(illegal_rows)),
        "illegal_projection_rank_nullity": (
            illegal.rank(), coefficient_nullity),
        "coupled_legal_image_rank": coupled_rank,
        "literal_contact_rank_nullity": (contact.rank(), actual_nullity),
        "contact_rank_on_coupled_image": coupled_contact_rank,
        "joined_coupled_actual_kernel_rank": joined_rank,
        "probe_boundary_rank_ambient_coupled": (
            beta_ambient.rank(), beta_coupled.rank()),
        "illegal_matrix_sha256": mat_hash(illegal),
        "coupled_legal_matrix_sha256": mat_hash(coupled),
        "first_last_illegal_rows": (illegal_rows[:3], illegal_rows[-3:]),
        "first_last_normal_labels": (labels[:3], labels[-3:]),
    }


def main():
    started = time.monotonic()
    if "--raw-profile" in sys.argv:
        profiles = (
            raw_boundary_mutation_profile("matched", base.GOOD_VALUES),
            raw_boundary_mutation_profile("retained_bad", base.BAD_VALUES),
        )
        result = {
            "scope": "raw boundary-zero mutation leaders only",
            "profiles": profiles,
        }
        canonical = json.dumps(result, sort_keys=True, separators=(",", ":"))
        output = dict(result)
        output["canonical_sha256"] = hashlib.sha256(
            canonical.encode()).hexdigest()
        output["elapsed_seconds"] = round(time.monotonic() - started, 6)
        output["max_rss_kib"] = resource.getrusage(
            resource.RUSAGE_SELF).ru_maxrss
        print(json.dumps(output, indent=2, sort_keys=True))
        return
    cases = (
        one_case("matched", base.GOOD_VALUES),
        one_case("retained_bad", base.BAD_VALUES),
    )
    result = {
        "scope": "finite exact F97/N8 discriminator; not target transport",
        "parameters": (
            base.P, base.N, base.W, base.G, base.M, base.D,
            base.SLOPE_CAP, base.CURVATURE_CAP,
            base.ACTIVE_CAP, base.SEED_CAP, base.PROBE,
        ),
        "declared_illegal_order": (
            "descending lex (shifted-X=x+3y+2r+s, active+seed total, "
            "z,s,r,y,x), restricted to source-illegal monomials"
        ),
        "cases": cases,
    }
    canonical = json.dumps(result, sort_keys=True, separators=(",", ":"))
    output = dict(result)
    output["canonical_sha256"] = hashlib.sha256(
        canonical.encode()).hexdigest()
    output["elapsed_seconds"] = round(time.monotonic() - started, 6)
    output["max_rss_kib"] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
