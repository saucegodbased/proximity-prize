#!/usr/bin/env python3
"""Exact small-field falsifier for the k=0 last-passive-face criterion.

For several relaxed-source profiles, this finds the first passive cap ``L``
whose *complete* source has positive nominal contact margin.  It compares

* the complete cap-``L`` source, and
* cap ``L-1`` plus only the newly available positive-``Z`` columns.

Every datum has a retained-bad agreement tangent of degree greater than
``w``.  Paired seed-zero/nonzero receipts are literal translations: ``u0``
is changed so that ``u0 + gamma*u1`` and hence the agreement/error pattern
are unchanged.  Candidate degree, agreement pattern, tangent shape, and
off-agreement direction/error pattern are varied deterministically.

All ranks are exact over the stated prime field.  This is a bounded
falsifier/mechanism discriminator, not a target theorem.
"""

from __future__ import annotations

from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import random
import resource
import sys
import time

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import secondjet_candidate_major_function_field_rank_gate_6900 as K0  # noqa: E402
from higher6810_secondjet_retarget_exact import relaxed_rank_bound  # noqa: E402
from higher_jet_literal_matrix import translated_column  # noqa: E402


# Keep an accidental profile expansion below the experiment lane's budget.
FOUR_GIB = 4 * 1024**3
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
if soft < 0 or soft > FOUR_GIB:
    resource.setrlimit(resource.RLIMIT_AS, (FOUR_GIB, hard))


PROFILES = (
    # p, n, w, agreement, m, B, s, U, first-positive L
    (17, 6, 2, 4, 3, 2, 1, 5, 4),
    (29, 9, 2, 6, 3, 2, 1, 5, 3),
    (101, 7, 3, 5, 3, 2, 1, 5, 4),
    (17, 10, 3, 7, 3, 2, 1, 5, 3),
    (29, 11, 4, 8, 3, 2, 1, 5, 3),
    (101, 6, 2, 4, 4, 2, 1, 6, 5),
)


DATA_FAMILIES = (
    # name, agreement kind, candidate kind, tangent kind, off-u1, errors
    ("prefix_max_minpoly", "prefix", "max", "minimal", "poly", "same"),
    ("spread_zero_top", "spread", "zero", "top", "arbitrary", "varying"),
    ("random_mid_spike", "random", "mid", "spike", "arbitrary", "alternating"),
)


def trim(poly: tuple[int, ...], p: int) -> tuple[int, ...]:
    out = tuple(x % p for x in poly)
    while len(out) > 1 and out[-1] == 0:
        out = out[:-1]
    return out


def degree(poly: tuple[int, ...], p: int) -> int:
    return len(trim(poly, p)) - 1


def evaluate(poly: tuple[int, ...], x: int, p: int, order: int = 0) -> int:
    answer = 0
    for exponent, coefficient in enumerate(poly):
        if exponent < order:
            continue
        falling = 1
        for j in range(order):
            falling = falling * (exponent - j) % p
        answer = (answer + coefficient * falling
                  * pow(x, exponent - order, p)) % p
    return answer


def interpolate(values: tuple[int, ...], nodes: tuple[int, ...],
                p: int) -> tuple[int, ...]:
    answer = [0] * len(nodes)
    for value, node in zip(values, nodes):
        basis = [1]
        denominator = 1
        for other in nodes:
            if other == node:
                continue
            nxt = [0] * (len(basis) + 1)
            for i, coefficient in enumerate(basis):
                nxt[i] = (nxt[i] - other * coefficient) % p
                nxt[i + 1] = (nxt[i + 1] + coefficient) % p
            basis = nxt
            denominator = denominator * (node - other) % p
        scale = value * pow(denominator, -1, p) % p
        for i, coefficient in enumerate(basis):
            answer[i] = (answer[i] + scale * coefficient) % p
    return trim(tuple(answer), p)


def agreement_set(profile: K0.Profile, kind: str, family_index: int):
    nodes = tuple(range(profile.n))
    if kind == "prefix":
        return nodes[:profile.agreements]
    if kind == "spread":
        order = nodes[::2] + nodes[1::2]
        return tuple(sorted(order[:profile.agreements]))
    if kind == "random":
        rng = random.Random(9173 * profile.n + 101 * profile.w + family_index)
        return tuple(sorted(rng.sample(nodes, profile.agreements)))
    raise ValueError(kind)


def polynomial_for(profile: K0.Profile, kind: str, p: int):
    if kind == "zero":
        return (0,)
    if kind == "mid":
        d = max(1, profile.w // 2)
        return tuple((3 + 5 * i) % p for i in range(d)) + (1,)
    if kind == "max":
        return tuple((7 + 3 * i) % p for i in range(profile.w)) + (1,)
    raise ValueError(kind)


def tangent_for(profile: K0.Profile, agreement: tuple[int, ...],
                kind: str, p: int):
    if kind == "minimal":
        return (0,) * (profile.w + 1) + (1,)
    if kind == "top":
        return (0,) * (profile.agreements - 1) + (1,)
    if kind == "spike":
        # A Lagrange basis vector is maximally concentrated on the retained
        # nodes while still having the top possible interpolant degree.
        values = (0,) * (len(agreement) - 1) + (1,)
        tangent = interpolate(values, agreement, p)
        assert degree(tangent, p) == profile.agreements - 1
        return tangent
    raise ValueError(kind)


def make_custom_receipt(profile: K0.Profile, p: int, gamma: int,
                        agreement_kind: str, candidate_kind: str,
                        tangent_kind: str, off_direction_kind: str,
                        error_kind: str, randomness_tag: int) -> K0.Receipt:
    nodes = tuple(range(profile.n))
    agreement = agreement_set(profile, agreement_kind, randomness_tag)
    agreement_lookup = set(agreement)
    polynomial = polynomial_for(profile, candidate_kind, p)
    tangent = tangent_for(profile, agreement, tangent_kind, p)
    assert profile.w < degree(tangent, p) < profile.agreements

    rng = random.Random(
        p * 1_000_003 + sum((i + 1) * value for i, value in
                            enumerate(asdict(profile).values()))
        + 97 * randomness_tag)
    u1 = []
    for x in nodes:
        if x in agreement_lookup or off_direction_kind == "poly":
            u1.append(evaluate(tangent, x, p))
        else:
            u1.append(rng.randrange(p))
    u0 = []
    errors = []
    for x in nodes:
        if x in agreement_lookup:
            error = 0
        elif error_kind == "same":
            error = 1
        elif error_kind == "varying":
            error = 1 + x % (p - 1)
        elif error_kind == "alternating":
            error = 1 if x % 2 == 0 else p - 1
        else:
            raise ValueError(error_kind)
        errors.append(error)
        u0.append((evaluate(polynomial, x, p) - gamma * u1[x] + error) % p)

    actual = tuple(
        x for x in nodes
        if evaluate(polynomial, x, p) == (u0[x] + gamma * u1[x]) % p)
    assert actual == agreement
    recovered = interpolate(tuple(u1[x] for x in agreement), agreement, p)
    assert recovered == trim(tangent, p)
    return K0.Receipt(nodes, agreement, gamma, polynomial,
                      tuple(u0), tuple(u1), tangent)


def make_receipt(profile: K0.Profile, p: int, family_index: int,
                 gamma: int) -> K0.Receipt:
    (name, agreement_kind, candidate_kind, tangent_kind,
     off_direction_kind, error_kind) = DATA_FAMILIES[family_index]
    del name
    return make_custom_receipt(
        profile, p, gamma, agreement_kind, candidate_kind, tangent_kind,
        off_direction_kind, error_kind, family_index)


def contact_kernel(profile: K0.Profile, receipt: K0.Receipt,
                   monomials, p: int, outer_indices=None):
    selected_outer = None if outer_indices is None else set(outer_indices)
    columns = []
    rows_set = set()
    for xp, yp, rp, sp, zp in monomials:
        column = {}
        for node in receipt.nodes:
            expansion = translated_column(
                xp, (yp, rp, sp), zp, node, receipt.u0[node],
                receipt.u1[node], profile.m, 2, p)
            for term, value in expansion.items():
                if (value % p and
                        (selected_outer is None or term[0] in selected_outer)):
                    column[(node, term)] = value % p
                    rows_set.add((node, term))
        columns.append(column)
    rows = tuple(sorted(rows_set, key=repr))
    row_index = {row: i for i, row in enumerate(rows)}
    matrix = nmod_mat(len(rows), len(monomials), p)
    for j, column in enumerate(columns):
        for row, value in column.items():
            matrix[row_index[row], j] = value
    kernel, nullity = matrix.nullspace()
    return len(rows), len(monomials) - nullity, kernel, nullity


def gradient_vector(monomial, receipt: K0.Receipt, x: int, p: int):
    xp, yp, rp, sp, zp = monomial
    point = (
        evaluate(receipt.polynomial, x, p),
        evaluate(receipt.polynomial, x, p, 1),
        evaluate(receipt.polynomial, x, p, 2),
        receipt.seed % p,
    )
    exponents = (yp, rp, sp, zp)
    answer = []
    for coordinate in range(4):
        if exponents[coordinate] == 0:
            answer.append(0)
            continue
        value = pow(x, xp, p) * exponents[coordinate] % p
        for j, (base, exponent) in enumerate(zip(point, exponents)):
            value = value * pow(base, exponent - (j == coordinate), p) % p
        answer.append(value)
    return tuple(answer)


def boundary_image(monomials, kernel, nullity: int,
                   receipt: K0.Receipt, x: int, p: int):
    flat = []
    gradients = tuple(gradient_vector(q, receipt, x, p) for q in monomials)
    for coordinate in range(4):
        flat.extend(vector[coordinate] for vector in gradients)
    raw = nmod_mat(4, len(monomials), flat, p)
    image = raw * kernel
    tangent_jet = (
        evaluate(receipt.tangent, x, p),
        evaluate(receipt.tangent, x, p, 1),
        evaluate(receipt.tangent, x, p, 2),
        1,
    )
    nonzero_tangent_pairings = 0
    for relation in range(nullity):
        pairing = sum(tangent_jet[i] * int(image[i, relation])
                      for i in range(4)) % p
        nonzero_tangent_pairings += pairing != 0
    return image.rank(), nonzero_tangent_pairings


def run_source(profile: K0.Profile, receipt: K0.Receipt, monomials, p: int,
               outer_indices=None):
    rows, rank, kernel, nullity = contact_kernel(
        profile, receipt, monomials, p, outer_indices)
    evaluations = []
    for x in range(p):
        if x in receipt.nodes:
            continue
        gain, pairings = boundary_image(
            monomials, kernel, nullity, receipt, x, p)
        evaluations.append((x, gain, pairings))
    fixed = next(row for row in evaluations if row[0] == profile.n)
    maximum = max(row[1] for row in evaluations)
    first_max = next(row for row in evaluations if row[1] == maximum)
    return {
        "columns_contact_rows_rank_nullity": (
            len(monomials), rows, rank, nullity),
        "boundary_Xn_gain_nonzero_bad_tangent_pairings": fixed,
        "max_off_domain_gain_and_first_witness": (maximum, first_max),
    }


def run_profile(spec):
    p, n, w, agreement_count, m, B, s, U, L = spec
    profile = K0.Profile(n, w, agreement_count, m, B, s, U, L, 0, 1)
    previous = K0.Profile(n, w, agreement_count, m, B, s, U, L - 1, 0, 1)
    complete = K0.support(profile)
    old = K0.support(previous)
    old_set = set(old)
    new = tuple(q for q in complete if q not in old_set)
    passive = tuple(q for q in new if q[4] > 0)
    active = tuple(q for q in new if q[4] == 0)
    passive_extension = old + passive
    local = relaxed_rank_bound(m, L, B, s, U)
    old_local = relaxed_rank_bound(m, L - 1, B, s, U)
    margin = len(complete) - n * local
    old_margin = len(old) - n * old_local
    assert margin > 0 and old_margin <= 0
    assert set(active).isdisjoint(passive)
    assert old_set | set(active) | set(passive) == set(complete)

    cases = []
    for family_index, family in enumerate(DATA_FAMILIES):
        seed_pair = []
        for gamma in (0, 5 % p):
            receipt = make_receipt(profile, p, family_index, gamma)
            passive_result = run_source(
                profile, receipt, passive_extension, p)
            complete_result = run_source(profile, receipt, complete, p)
            seed_pair.append({
                "seed": gamma,
                "agreement_set": receipt.agreement,
                "candidate_and_tangent_degrees": (
                    degree(receipt.polynomial, p),
                    degree(receipt.tangent, p)),
                "passive_extension": passive_result,
                "complete_cap": complete_result,
            })
        # Seed translation is an automorphism preserving each downward-closed
        # cap and its relative positive-Z face modulo the old cap.
        def invariant_signature(result):
            fixed = result["boundary_Xn_gain_nonzero_bad_tangent_pairings"]
            maximum = result["max_off_domain_gain_and_first_witness"]
            return (
                result["columns_contact_rows_rank_nullity"],
                fixed[1], maximum[0],
            )

        # A nullspace basis can change under translation, so the *number* of
        # nonzero pairings with its canonical columns is not invariant.  The
        # contact dimensions and boundary-image ranks are invariant.
        assert invariant_signature(seed_pair[0]["passive_extension"]) == \
            invariant_signature(seed_pair[1]["passive_extension"])
        assert invariant_signature(seed_pair[0]["complete_cap"]) == \
            invariant_signature(seed_pair[1]["complete_cap"])
        cases.append({
            "family": family,
            "seed_translation_pair": seed_pair,
        })
    return {
        "field": p,
        "profile_n_w_g_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "old_complete_active_new_passive_new_counts": (
            len(old), len(complete), len(active), len(passive)),
        "old_and_first_positive_complete_margins": (old_margin, margin),
        "cases": cases,
    }


def main():
    started = time.monotonic()
    profiles = []
    for i, spec in enumerate(PROFILES, start=1):
        print(f"profile {i}/{len(PROFILES)} {spec}", file=sys.stderr,
              flush=True)
        profiles.append(run_profile(spec))

    passive_gains = []
    complete_gains = []
    complete_defects = []
    passive_defects = []
    for profile_index, profile in enumerate(profiles):
        for case in profile["cases"]:
            for seed_case in case["seed_translation_pair"]:
                passive_gain = (seed_case["passive_extension"]
                                ["max_off_domain_gain_and_first_witness"][0])
                complete_gain = (seed_case["complete_cap"]
                                 ["max_off_domain_gain_and_first_witness"][0])
                passive_gains.append(passive_gain)
                complete_gains.append(complete_gain)
                descriptor = {
                    "profile_index": profile_index,
                    "field": profile["field"],
                    "profile": profile["profile_n_w_g_m_B_s_U_L_k_n0"],
                    "family": case["family"],
                    "seed": seed_case["seed"],
                    "candidate_and_tangent_degrees":
                        seed_case["candidate_and_tangent_degrees"],
                }
                if passive_gain < 4:
                    passive_defects.append({
                        **descriptor,
                        "receipt": seed_case["passive_extension"],
                    })
                if complete_gain < 4:
                    complete_defects.append({
                        **descriptor,
                        "receipt": seed_case["complete_cap"],
                    })
    payload = {
        "scope": (
            "exact small-field sweep of first-positive complete cap versus "
            "old cap plus only the last passive face; bounded falsifier"
        ),
        "profiles": profiles,
        "passive_extension_rank4_cases_and_total": (
            sum(gain == 4 for gain in passive_gains), len(passive_gains)),
        "complete_cap_rank4_cases_and_total": (
            sum(gain == 4 for gain in complete_gains), len(complete_gains)),
        "complete_cap_rank_defect_receipts": complete_defects,
        "passive_extension_rank_defect_count": len(passive_defects),
        "verdict": (
            "RED at this finite scope: retained-bad tangent plus first "
            "positive complete-source margin does not universally force "
            "boundary rank four; passive-only attachment is still weaker. "
            "The listed exact defects require a sharper source/profile or "
            "data-independent connecting-map hypothesis."
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    payload["runtime"] = {
        "seconds": round(time.monotonic() - started, 3),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    print("compact_result=" + json.dumps({
        "passive_rank4": payload["passive_extension_rank4_cases_and_total"],
        "complete_rank4": payload["complete_cap_rank4_cases_and_total"],
        "complete_defects": complete_defects,
        "canonical_sha256": payload["canonical_sha256"],
    }, sort_keys=True), file=sys.stderr, flush=True)
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
