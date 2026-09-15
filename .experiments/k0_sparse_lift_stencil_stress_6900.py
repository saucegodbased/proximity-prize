#!/usr/bin/env python3
"""Stress-test the first exact full-face boundary lift across data families.

This deliberately does *not* reuse ``relation_receipt`` from
``k0_small_full_face_sparse_lift_6900``.  That exploratory formatter contains
an invalid naive associated-contact interpretation: replacing ``Y`` by
``Y-QZ`` without simultaneously transporting the jet variables does not
preserve the flattened contact map.  Here we record only literal contact
identities, formal Hasse-boundary ranks, and raw monomial support.

The tracked elimination order is deterministic but not canonical.  Hence the
first relation is a witness for the stated order, not a minimal-support claim.
All arithmetic is exact over the indicated prime field.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import asdict
import argparse
import gc
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_poly

sys.path.insert(0, ".experiments")
import k0_first_positive_passive_universal_falsifier_6900 as Old  # noqa: E402
import k0_flattened_contact_sweep_regression_6900 as Flat  # noqa: E402
import k0_small_full_face_sparse_lift_6900 as Seed  # noqa: E402


FOUR_GIB = 4 * 1024**3
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
if soft < 0 or soft > FOUR_GIB:
    resource.setrlimit(resource.RLIMIT_AS, (FOUR_GIB, hard))


def add_sparse(target, source, scale, prime):
    for key, value in source.items():
        updated = (target.get(key, 0) + scale * value) % prime
        if updated:
            target[key] = updated
        else:
            target.pop(key, None)


def boundary_of_relation(relation, boundaries, prime):
    answer = [0, 0, 0, 0]
    for index, coefficient in relation.items():
        for coordinate, value in enumerate(boundaries[index]):
            answer[coordinate] = (
                answer[coordinate] + coefficient * value) % prime
    return tuple(answer)


def shape(monomial):
    _x, _y, r, s, _z = monomial
    if s:
        return "S"
    if r == 1:
        return "R"
    if r >= 2:
        return "R2+"
    return "raw"


def polynomial_receipt(terms, prime):
    coefficients = [0] * (max(terms, default=-1) + 1)
    for exponent, coefficient in terms.items():
        coefficients[exponent] = coefficient % prime
    poly = nmod_poly(coefficients, prime)
    if poly == 0:
        return {"degree": -1, "sha256": hashlib.sha256(b"0").hexdigest()}
    canonical = ",".join(str(int(x)) for x in poly.coeffs())
    return {
        "degree": poly.degree(),
        "sha256": hashlib.sha256(canonical.encode()).hexdigest(),
    }


def support_receipt(relation, monomials, old_count, boundaries, prime):
    support = sorted((index, coefficient % prime)
                     for index, coefficient in relation.items()
                     if coefficient % prime)
    grouped = {}
    for index, coefficient in support:
        xp, y, r, s, z = monomials[index]
        part = "old" if index < old_count else "face"
        grouped.setdefault((part, y, r, s, z), {})[xp] = coefficient
    grouped_receipt = []
    for key, terms in sorted(grouped.items(), key=repr):
        grouped_receipt.append({
            "part_Y_R_S_Z": key,
            "x_coefficient": polynomial_receipt(terms, prime),
        })
    canonical = json.dumps(
        [(i, monomials[i], c) for i, c in support],
        separators=(",", ":"))
    counts = Counter(
        ("old" if i < old_count else "face", shape(monomials[i]))
        for i, _ in support)
    return {
        "support_size_old_face": (
            len(support),
            sum(i < old_count for i, _ in support),
            sum(i >= old_count for i, _ in support)),
        "support_counts_by_part_and_shape": tuple(sorted(counts.items())),
        "face_cell_types_Y_R_S_Z": tuple(
            key[1:] for key in sorted(grouped, key=repr) if key[0] == "face"),
        "grouped_x_polynomials": grouped_receipt,
        "boundary": boundary_of_relation(relation, boundaries, prime),
        "support_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
    }


def profile_at_cap(profile, cap):
    return Old.K0.Profile(
        profile.n, profile.w, profile.agreements, profile.m, profile.B,
        profile.s, profile.U, cap, profile.k, profile.n0)


def positive_face(old, successor_profile):
    old_set = set(old)
    return tuple(monomial for monomial in Old.K0.support(successor_profile)
                 if monomial not in old_set and monomial[4] > 0)


def extract_case(label, prime, profile, successor_cap, family_index, gamma,
                 receipt_override=None, family_name=None):
    started = time.monotonic()
    successor = profile_at_cap(profile, successor_cap)
    receipt = (receipt_override if receipt_override is not None else
               Old.make_receipt(profile, prime, family_index, gamma))
    old = Old.K0.support(profile)
    face = positive_face(old, successor)
    monomials = old + face
    columns = [Flat.flattened_column(
        successor, receipt, monomial, prime) for monomial in monomials]
    boundaries = [Flat.formal_boundary_gradient(
        monomial, receipt, profile.n, prime) for monomial in monomials]

    contact = Seed.TrackedColumnEchelon(prime)
    normal = Flat.SparseRank(prime)
    first_fourth = None
    first_fourth_position = None
    old_boundary_events = []
    face_boundary_events = []

    for index in range(len(old)):
        independent, relation = contact.add(columns[index], index)
        if independent:
            continue
        boundary = boundary_of_relation(relation, boundaries, prime)
        before = normal.rank
        normal.add(dict(enumerate(boundary)))
        if normal.rank > before:
            old_boundary_events.append((index, monomials[index], normal.rank))
    old_rank = contact.rank
    old_normal_rank = normal.rank

    individually_old_correctable = 0
    individually_add_fourth = 0
    for local_index in range(len(face)):
        index = len(old) + local_index
        remainder, relation = contact.reduce(columns[index], index)
        if remainder:
            continue
        individually_old_correctable += 1
        trial = Flat.SparseRank(prime)
        for pivot in normal.pivots.values():
            trial.add(pivot)
        before = trial.rank
        trial.add(dict(enumerate(boundary_of_relation(
            relation, boundaries, prime))))
        individually_add_fourth += trial.rank > before

    for local_index in range(len(face)):
        index = len(old) + local_index
        independent, relation = contact.add(columns[index], index)
        if independent:
            continue
        boundary = boundary_of_relation(relation, boundaries, prime)
        before = normal.rank
        normal.add(dict(enumerate(boundary)))
        if normal.rank > before:
            face_boundary_events.append(
                (local_index, monomials[index], normal.rank, len(relation)))
            if normal.rank == 4 and first_fourth is None:
                first_fourth = relation
                first_fourth_position = local_index

    relation_summary = None
    if first_fourth is not None:
        contact_sum = {}
        for index, coefficient in first_fourth.items():
            add_sparse(contact_sum, columns[index], coefficient, prime)
        assert not contact_sum
        relation_summary = support_receipt(
            first_fourth, monomials, len(old), boundaries, prime)

    result = {
        "label": label,
        "field": prime,
        "profile_n_w_g_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "successor_cap": successor_cap,
        "family": (family_name if family_name is not None else
                   Old.DATA_FAMILIES[family_index][0]),
        "gamma": gamma,
        "columns_old_face": (len(old), len(face)),
        "contact_rank_old_face_extension": (old_rank, contact.rank),
        "normal_rank_old_face_extension": (old_normal_rank, normal.rank),
        "old_boundary_events": tuple(old_boundary_events),
        "face_boundary_events": tuple(face_boundary_events),
        "individual_face_columns_old_correctable_add_fourth": (
            individually_old_correctable, individually_add_fourth),
        "first_fourth_face_position": first_fourth_position,
        "first_fourth_relation": relation_summary,
        "seconds": round(time.monotonic() - started, 3),
    }
    del columns, boundaries, contact, normal
    gc.collect()
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--quick", action="store_true",
        help="run the seed profile only (all families and two translations)")
    parser.add_argument(
        "--summary", action="store_true",
        help="print a compact projection while hashing the full receipt")
    args = parser.parse_args()
    started = time.monotonic()

    seed = Old.K0.Profile(10, 2, 7, 3, 2, 1, 5, 2, 0, 1)
    specs = [
        ("seed_m3_p101", 101, seed, 3, family, gamma)
        for family in range(len(Old.DATA_FAMILIES))
        for gamma in (0, 5)
    ]
    # Isolate the role of off-agreement directions while leaving every other
    # seed datum fixed.  At gamma zero u0 and therefore the agreement set stay
    # unchanged when u1 is perturbed outside the agreement set.
    base_receipt = Old.make_receipt(seed, 101, 0, 0)
    for name, changed_nodes in (
            ("prefix_max_minpoly_one_error_u1_plus1", (7,)),
            ("prefix_max_minpoly_all_errors_u1_plus1", (7, 8, 9))):
        changed_u1 = list(base_receipt.u1)
        for node in changed_nodes:
            changed_u1[node] = (changed_u1[node] + 1) % 101
        changed_receipt = Old.K0.Receipt(
            base_receipt.nodes, base_receipt.agreement, base_receipt.seed,
            base_receipt.polynomial, base_receipt.u0, tuple(changed_u1),
            base_receipt.tangent)
        specs.append(("seed_m3_p101_perturb", 101, seed, 3, 0, 0,
                      changed_receipt, name))
    if not args.quick:
        # Same jet order over another field/profile, then a fourth-order jet.
        p, n, w, g, m, b, s, u, cap = Old.PROFILES[3]
        cross_m3 = Old.K0.Profile(n, w, g, m, b, s, u, cap - 1, 0, 1)
        specs.extend(("cross_m3_p17", p, cross_m3, cap, family, 0)
                     for family in range(len(Old.DATA_FAMILIES)))
        p, n, w, g, m, b, s, u, cap = Old.PROFILES[-1]
        cross_m4 = Old.K0.Profile(n, w, g, m, b, s, u, cap - 1, 0, 1)
        specs.extend(("cross_m4_p101", p, cross_m4, cap, family, 0)
                     for family in range(len(Old.DATA_FAMILIES)))

    rows = []
    for index, spec in enumerate(specs, start=1):
        print(f"case {index}/{len(specs)} {spec[0]} family={spec[4]} "
              f"gamma={spec[5]}", file=sys.stderr, flush=True)
        rows.append(extract_case(*spec))

    payload = {
        "scope": (
            "exact tracked-elimination stress test of the first full-face "
            "fourth-boundary witness"),
        "warning": (
            "raw support only: no associated-coordinate/contact claim; the "
            "first relation depends on deterministic column/pivot order"),
        "cases": rows,
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(
        canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    payload["runtime"] = {
        "seconds": round(time.monotonic() - started, 3),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "address_space_cap_bytes": FOUR_GIB,
    }
    if args.summary:
        compact_rows = []
        for row in rows:
            relation = row["first_fourth_relation"]
            compact_rows.append({
                key: row[key] for key in (
                    "label", "field", "family", "gamma",
                    "profile_n_w_g_m_B_s_U_L_k_n0", "successor_cap",
                    "columns_old_face", "contact_rank_old_face_extension",
                    "normal_rank_old_face_extension", "face_boundary_events",
                    "first_fourth_face_position",
                    "individual_face_columns_old_correctable_add_fourth",
                    "seconds")
            } | ({"first_fourth_relation": None} if relation is None else {
                "first_fourth_relation": {
                    key: relation[key] for key in (
                        "support_size_old_face",
                        "support_counts_by_part_and_shape",
                        "face_cell_types_Y_R_S_Z", "boundary",
                        "support_sha256")
                }
            }))
        payload = {
            "cases": compact_rows,
            "full_receipt_canonical_sha256": payload["canonical_sha256"],
            "script_sha256": payload["script_sha256"],
            "runtime": payload["runtime"],
        }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
