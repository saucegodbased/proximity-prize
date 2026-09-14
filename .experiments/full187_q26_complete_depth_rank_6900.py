#!/usr/bin/env python3
"""Exact d=29 rank gate for complete-depth Full187 versus the q=26 fringe.

This is the small adapted-basis version of the 11,748 by 4,862 raw contact
matrix.  It never treats physical homogeneous blocks as independent.  Write

  A = E + T*R - T^2*S/2,  V = Y-T*R,  W = V+T^2*S/2.

After factoring A^8, the 187 ordinary source monomials form the (21,10)
flag.  The source-side Order2 basis

  Y^8 R^b V^rho W^e S^c

is unitriangular over F_p[T], and its contact images have distinct sharp
leading terms.  Thus contact truncation at weight 60 is exactly coefficient
truncation modulo T^(60-v(b,e)) in each adapted coordinate.  We build the
unitriangular change of basis exactly over the benchmark field, rank the
physical q=0..25 box, and append precisely the eleven boundary q=26 blocks.

Only this one active/passive sector is tested.  No production files change.
"""

from __future__ import annotations

from collections import Counter
import argparse
from functools import lru_cache
import hashlib
import json
from math import comb
from pathlib import Path
import resource


P = 2_130_706_433
ACTIVE = 29
BASE_Y = 8
FLAG_DEGREE = 21
S_CAP = 10
CONTACT_CUTOFF = 60
COMPLETE_QMAX = 25
INV2 = pow(2, -1, P)
A_LITERAL = {
    (0, 1, 0, 0): 1,
    (1, 0, 1, 0): 1,
    (2, 0, 0, 1): (-INV2) % P,
}
U_LITERAL = {
    (0, 1, 0, 0): 1,
    (2, 0, 0, 1): (-INV2) % P,
}


def poly_add_to(dst, src, scale=1, shift=0):
    """dst += scale*T^shift*src, deleting exact zero coefficients."""
    scale %= P
    if not scale:
        return
    for degree, coefficient in src.items():
        key = degree + shift
        value = (dst.get(key, 0) + scale * coefficient) % P
        if value:
            dst[key] = value
        elif key in dst:
            del dst[key]


def poly_mul(left, right):
    out = {}
    for dl, cl in left.items():
        for dr, cr in right.items():
            key = dl + dr
            out[key] = (out.get(key, 0) + cl * cr) % P
    return {degree: coefficient for degree, coefficient in out.items()
            if coefficient}


def mv_mul(left, right):
    """Multiply sparse polynomials in literal contact variables T,E,R,S."""
    out = {}
    for ml, cl in left.items():
        for mr, cr in right.items():
            monomial = tuple(ml[i] + mr[i] for i in range(4))
            out[monomial] = (out.get(monomial, 0) + cl * cr) % P
    return {monomial: coefficient for monomial, coefficient in out.items()
            if coefficient}


def mv_pow(base, exponent):
    out = {(0, 0, 0, 0): 1}
    while exponent:
        if exponent & 1:
            out = mv_mul(out, base)
        base = mv_mul(base, base)
        exponent //= 2
    return out


def mv_monomial(t=0, e=0, r=0, s=0):
    return {(t, e, r, s): 1}


def mv_add_to(dst, src, scale=1, t_shift=0, truncate=True):
    scale %= P
    for monomial, coefficient in src.items():
        shifted = (monomial[0] + t_shift, *monomial[1:])
        if truncate and shifted[0] + 3 * shifted[1] >= CONTACT_CUTOFF:
            continue
        value = (dst.get(shifted, 0) + scale * coefficient) % P
        if value:
            dst[shifted] = value
        elif shifted in dst:
            del dst[shifted]


def pairs():
    """Physical standard monomials, in the unitriangular pivot order."""
    out = []
    for total in range(FLAG_DEGREE + 1):
        for b in range(total + 1):
            c = total - b
            if c <= S_CAP:
                out.append((b, c))
    assert len(out) == 187
    return tuple(out)


PAIRS = pairs()
PAIR_INDEX = {pair: i for i, pair in enumerate(PAIRS)}


def adapted_parameters(pair):
    """Return h, min(h,10), e, rho, valuation, coefficient cap."""
    b, c = pair
    h = FLAG_DEGREE - b
    capped = min(h, S_CAP)
    assert c <= capped
    e = capped - c
    rho = h - capped
    valuation = BASE_Y + 2 * rho + 3 * e
    cap = max(0, CONTACT_CUTOFF - valuation)
    return h, capped, e, rho, valuation, cap


def adapted_in_standard(pair):
    """Expand one adapted source basis vector in ordinary (b,c) rows.

    B_(b,c) = Y^8 R^b (Y-TR)^rho
                (Y-TR+T^2 S/2)^e S^c.
    Its coefficient at ordinary row (b,c) is exactly one; every other row
    has strictly larger b+c, proving the order PAIRS is unitriangular.
    """
    b, c = pair
    h, _capped, e, rho, _valuation, _cap = adapted_parameters(pair)
    out = {}
    # Choose l copies of T^2*S/2 from W^e, leaving V^(h-c-l).
    for l in range(e + 1):
        n = rho + e - l
        assert n == h - c - l
        outer = comb(e, l) * pow(INV2, l, P) % P
        # Choose j copies of -T*R from V^n.
        for j in range(n + 1):
            row = (b + j, c + l)
            assert row in PAIR_INDEX
            assert PAIR_INDEX[row] >= PAIR_INDEX[pair]
            degree = 2 * l + j
            coefficient = outer * comb(n, j) * ((-1) ** j) % P
            polynomial = out.setdefault(row, {})
            poly_add_to(polynomial, {degree: coefficient})
    assert out[pair] == {0: 1}
    return out


ADAPTED_EXPANSIONS = {pair: adapted_in_standard(pair) for pair in PAIRS}


def standard_in_adapted(pair):
    """Invert the unitriangular basis for one ordinary monomial exactly."""
    residual = {pair: {0: 1}}
    answer = {}
    for pivot in PAIRS:
        coefficient = residual.pop(pivot, None)
        if not coefficient:
            continue
        answer[pivot] = coefficient
        expansion = ADAPTED_EXPANSIONS[pivot]
        for row, polynomial in expansion.items():
            if row == pivot:
                continue
            product = poly_mul(coefficient, polynomial)
            target = residual.setdefault(row, {})
            poly_add_to(target, product, scale=-1)
            if not target:
                del residual[row]
    assert not residual
    return answer


STANDARD_EXPANSIONS = {pair: standard_in_adapted(pair) for pair in PAIRS}


ROW_KEYS = tuple(
    (pair, k)
    for pair in PAIRS
    for k in range(adapted_parameters(pair)[-1])
)
ROW_INDEX = {key: i for i, key in enumerate(ROW_KEYS)}


def physical_column(pair, q):
    """Truncated contact image of T^q times one physical source monomial."""
    out = {}
    for adapted_pair, polynomial in STANDARD_EXPANSIONS[pair].items():
        cap = adapted_parameters(adapted_pair)[-1]
        for degree, coefficient in polynomial.items():
            k = q + degree
            if k >= cap:
                continue
            row = ROW_INDEX[(adapted_pair, k)]
            value = (out.get(row, 0) + coefficient) % P
            if value:
                out[row] = value
            elif row in out:
                del out[row]
    return out


def subtract_scaled(column, pivot, factor):
    for row, coefficient in pivot.items():
        value = (column.get(row, 0) - factor * coefficient) % P
        if value:
            column[row] = value
        elif row in column:
            del column[row]


def sparse_rank(columns, keep_witnesses=False):
    """Deterministic exact sparse column echelon form over the target field."""
    pivots = {}
    provenance = {} if keep_witnesses else None
    zero_relations = []
    maximum_live = 0
    for label, original in columns:
        column = dict(original)
        relation = {label: 1} if keep_witnesses else None
        while column:
            row = min(column)
            if row not in pivots:
                inverse = pow(column[row], -1, P)
                column = {r: c * inverse % P for r, c in column.items()}
                pivots[row] = column
                if keep_witnesses:
                    relation = {key: value * inverse % P
                                for key, value in relation.items() if value}
                    provenance[row] = relation
                break
            factor = column[row]
            subtract_scaled(column, pivots[row], factor)
            if keep_witnesses:
                for key, coefficient in provenance[row].items():
                    value = (relation.get(key, 0) - factor * coefficient) % P
                    if value:
                        relation[key] = value
                    elif key in relation:
                        del relation[key]
            maximum_live = max(maximum_live, len(column))
        if not column and keep_witnesses:
            zero_relations.append((label, relation))
    return pivots, zero_relations, maximum_live


def transformation_receipt():
    expansion_nnz = sum(
        sum(len(polynomial) for polynomial in expansion.values())
        for expansion in STANDARD_EXPANSIONS.values())
    maximum_degree = max(
        degree
        for expansion in STANDARD_EXPANSIONS.values()
        for polynomial in expansion.values()
        for degree in polynomial)
    # Verify both directions on every basis vector, rather than trusting the
    # triangular inversion routine.
    for source_pair, inverse_expansion in STANDARD_EXPANSIONS.items():
        recovered = {}
        for adapted_pair, coefficient in inverse_expansion.items():
            for ordinary_pair, polynomial in ADAPTED_EXPANSIONS[adapted_pair].items():
                product = poly_mul(coefficient, polynomial)
                target = recovered.setdefault(ordinary_pair, {})
                poly_add_to(target, product)
                if not target:
                    del recovered[ordinary_pair]
        assert recovered == {source_pair: {0: 1}}
    return {
        "ordinary_and_adapted_basis_size": len(PAIRS),
        "adapted_truncated_coordinate_count": len(ROW_KEYS),
        "standard_to_adapted_polynomial_nnz": expansion_nnz,
        "standard_to_adapted_maximum_T_degree": maximum_degree,
        "adapted_cap_histogram": tuple(sorted(Counter(
            adapted_parameters(pair)[-1] for pair in PAIRS).items())),
        "all_187_two_sided_unitriangular_checks": True,
    }


def literal_contact_basis_receipt():
    """Falsify the valuation/cap model against literal A and U expansion."""
    A8 = mv_pow(A_LITERAL, BASE_Y)
    support_histogram = Counter()
    payload = []
    for pair in PAIRS:
        b, c = pair
        _h, _capped, e, rho, valuation, cap = adapted_parameters(pair)
        generator = mv_mul(
            A8,
            mv_mul(mv_monomial(r=b, s=c),
                   mv_mul(mv_pow(U_LITERAL, rho), mv_monomial(e=e))),
        )
        weights = {monomial: monomial[0] + 3 * monomial[1]
                   for monomial in generator}
        minimum = min(weights.values())
        minimum_terms = tuple(sorted(
            (monomial, generator[monomial])
            for monomial, weight in weights.items() if weight == minimum))
        expected_pivot = (BASE_Y + 2 * rho, e, BASE_Y + b, c + rho)
        expected_coefficient = pow(-INV2 % P, rho, P)
        assert minimum == valuation
        assert minimum_terms == ((expected_pivot, expected_coefficient),)
        assert cap == max(0, CONTACT_CUTOFF - minimum)
        assert all(monomial[1] + monomial[2] + monomial[3] == ACTIVE
                   for monomial in generator)
        support_histogram[len(generator)] += 1
        payload.append((pair, e, rho, valuation, cap,
                        expected_pivot, expected_coefficient,
                        tuple(sorted(generator.items()))))
    return {
        "literal_A8_support": len(A8),
        "literal_generator_support_histogram": tuple(sorted(
            support_histogram.items())),
        "all_187_unique_minimum_pivots_and_caps_verified": True,
        "literal_generators_sha256": hashlib.sha256(
            repr(tuple(payload)).encode()).hexdigest(),
    }


@lru_cache(maxsize=None)
def literal_adapted_generator(pair):
    b, c = pair
    _h, _capped, e, rho, _valuation, _cap = adapted_parameters(pair)
    return mv_mul(
        mv_pow(A_LITERAL, BASE_Y),
        mv_mul(mv_monomial(r=b, s=c),
               mv_mul(mv_pow(U_LITERAL, rho), mv_monomial(e=e))),
    )


@lru_cache(maxsize=None)
def literal_A_power(exponent):
    return mv_pow(A_LITERAL, exponent)


def literal_physical_column(pair, q):
    """Direct T^q A^y R^b S^c contact expansion, weight-truncated."""
    b, c = pair
    y = ACTIVE - b - c
    raw = mv_mul(literal_A_power(y), mv_monomial(r=b, s=c))
    out = {}
    mv_add_to(out, raw, t_shift=q)
    return out


def literal_reconstruction(pair, q):
    """Reconstruct a physical column from its adapted coordinates."""
    out = {}
    coordinates = physical_column(pair, q)
    for row, coefficient in coordinates.items():
        adapted_pair, k = ROW_KEYS[row]
        mv_add_to(out, literal_adapted_generator(adapted_pair),
                  scale=coefficient, t_shift=k)
    return out


def literal_all_column_crosscheck():
    hasher = hashlib.sha256()
    count = 0
    entries = 0
    source_entries = 0
    q26_boundary_entries = 0
    boundary_pairs = {(FLAG_DEGREE - s, s) for s in range(S_CAP + 1)}
    for pair in PAIRS:
        for q in range(COMPLETE_QMAX + 2):
            direct = literal_physical_column(pair, q)
            reconstructed = literal_reconstruction(pair, q)
            assert reconstructed == direct
            count += 1
            entries += len(direct)
            if q <= COMPLETE_QMAX:
                source_entries += len(direct)
            elif pair in boundary_pairs:
                q26_boundary_entries += len(direct)
            hasher.update(repr((pair, q, tuple(sorted(direct.items())))).encode())
    assert count == 187 * 27
    assert source_entries == 592_636
    assert q26_boundary_entries == 495
    return {
        "physical_columns_q0_through_q26_checked": count,
        "literal_truncated_support_entries": entries,
        "literal_q0_through_q25_source_support_entries": source_entries,
        "literal_eleven_q26_boundary_support_entries": q26_boundary_entries,
        "literal_columns_sha256": hasher.hexdigest(),
    }


def dot(left, right):
    if len(left) > len(right):
        left, right = right, left
    return sum(coefficient * right.get(row, 0)
               for row, coefficient in left.items()) % P


def dual_witness(free_row, pivots):
    """Exact cokernel functional normalized to one on a free coordinate."""
    witness = {free_row: 1}
    for pivot_row in sorted(pivots, reverse=True):
        # Pivot columns have coefficient one at pivot_row and no earlier row.
        tail_value = sum(
            coefficient * witness.get(row, 0)
            for row, coefficient in pivots[pivot_row].items()
            if row != pivot_row
        ) % P
        value = (-tail_value) % P
        if value:
            witness[pivot_row] = value
    assert all(dot(witness, column) == 0 for column in pivots.values())
    assert witness[free_row] == 1
    return witness


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--census-only", action="store_true")
    args = parser.parse_args()

    transform = transformation_receipt()
    contact_basis = literal_contact_basis_receipt()
    literal_crosscheck = literal_all_column_crosscheck()
    source_columns = []
    source_nnz = 0
    zero_source_columns = []
    # Natural diagonal columns first minimizes fill; then the missing-diagonal
    # cap fringe.  This is merely an elimination order, not an independence
    # assumption.
    direct = []
    fringe = []
    for pair in PAIRS:
        cap = adapted_parameters(pair)[-1]
        for q in range(COMPLETE_QMAX + 1):
            column = physical_column(pair, q)
            item = (("source", pair, q), column)
            (direct if q < cap else fringe).append(item)
            source_nnz += len(column)
            if not column:
                zero_source_columns.append((pair, q))
    source_columns = direct + fringe
    assert len(source_columns) == 187 * 26 == 4_862

    target_pairs = tuple((FLAG_DEGREE - s, s) for s in range(S_CAP + 1))
    target_columns = [(('target_q26', pair), physical_column(pair, 26))
                      for pair in target_pairs]
    assert all(column for _label, column in target_columns)

    stable = {
        "scope": (
            "exact simultaneous d29/passive53 complete-depth q0..25 source "
            "box, augmented only by the eleven y8,r+s21,s<=10 q26 blocks"),
        "target_p_active_flag_scap_cutoff_qmax": (
            P, ACTIVE, FLAG_DEGREE, S_CAP, CONTACT_CUTOFF, COMPLETE_QMAX),
        "transformation": transform,
        "literal_contact_basis": contact_basis,
        "literal_all_column_crosscheck": literal_crosscheck,
        "physical_source_columns_support_nnz": (
            len(source_columns), source_nnz),
        "literal_zero_source_columns": tuple(zero_source_columns),
        "q26_target_columns_support_nnz": (
            len(target_columns), sum(len(c) for _l, c in target_columns)),
    }

    if args.census_only:
        stable.update({
            "decision": "CENSUS_ONLY",
            "remaining_gate": "exact source and augmented modular ranks",
        })
    else:
        pivots, source_relations, max_live = sparse_rank(
            source_columns, keep_witnesses=False)
        source_rank = len(pivots)

        # Reduce each target against the same source echelon form, then each
        # earlier independent target.  Record which actual targets add rank.
        augmented_pivots = dict(pivots)
        target_residuals = []
        target_rank_gain = 0
        for label, original in target_columns:
            column = dict(original)
            while column:
                row = min(column)
                if row not in augmented_pivots:
                    inverse = pow(column[row], -1, P)
                    column = {r: c * inverse % P
                              for r, c in column.items()}
                    augmented_pivots[row] = column
                    target_rank_gain += 1
                    target_residuals.append((label, "independent", ROW_KEYS[row],
                                             len(column)))
                    break
                subtract_scaled(column, augmented_pivots[row], column[row])
                max_live = max(max_live, len(column))
            if not column:
                target_residuals.append((label, "in_source_or_prior_targets"))

        stable.update({
            "exact_source_rank_nullity": (
                source_rank, len(source_columns) - source_rank),
            "exact_augmented_rank_target_gain": (
                len(augmented_pivots), target_rank_gain),
            "q26_target_reduction_receipts": tuple(target_residuals),
            "maximum_sparse_live_column_nnz": max_live,
            "decision": (
                "GREEN_ALL_Q26_TARGETS_IN_COMPLETE_DEPTH_AGGREGATE_IMAGE"
                if target_rank_gain == 0 else
                "RED_Q26_TARGETS_EXTEND_COMPLETE_DEPTH_AGGREGATE_IMAGE"),
            "interpretation": (
                "GREEN means replacement is possible in aggregate but does "
                "not mean the separated per-stream Pascal prescriptions can "
                "be superposed. RED means the complete-depth box leaves a "
                "literal q26 cokernel of the reported dimension."),
        })

        dual_receipts = []
        for label, target_column in target_columns:
            assert len(target_column) == 1
            target_row, target_coefficient = next(iter(target_column.items()))
            assert target_coefficient == 1 and target_row not in pivots
            witness = dual_witness(target_row, pivots)
            assert all(dot(witness, column) == 0
                       for _source_label, column in source_columns)
            evaluations = tuple(dot(witness, column)
                                for _target_label, column in target_columns)
            target_index = target_columns.index((label, target_column))
            assert evaluations[target_index] == 1
            assert sum(value != 0 for value in evaluations) == 1
            encoded = tuple((ROW_KEYS[row], coefficient)
                            for row, coefficient in sorted(witness.items()))
            dual_receipts.append((
                label, ROW_KEYS[target_row], len(witness), evaluations,
                hashlib.sha256(repr(encoded).encode()).hexdigest()))
        stable["exact_q26_cokernel_dual_receipts"] = tuple(dual_receipts)

    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    print(json.dumps({
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
