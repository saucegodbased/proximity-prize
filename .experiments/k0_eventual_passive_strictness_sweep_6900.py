#!/usr/bin/env python3
"""Exact small-profile sweep for eventual complete-face strictness.

For old passive caps ``L >= U`` the exact face at ``L+1`` is obtained from
the preceding face by multiplication by ``Z``.  Consequently, once the
filtered connecting obstruction vanishes it stays zero.  This script measures
the first such cap in finite literal contact matrices and aggressively checks
candidate uniform bounds against several target-sign profiles and receipts.

The contact is exactly

    Y = u0 + u1*Z + eps*R - eps^2*S + eps^3*T  (mod eps^m)

over F_101.  These computations are mechanism discriminators, not a theorem
at the target parameters.
"""

from __future__ import annotations

from dataclasses import asdict, replace
import argparse
import gc
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import k0_eps0_filtered_obstruction_gate_6900 as Gate  # noqa: E402
import k0_first_positive_passive_universal_falsifier_6900 as Old  # noqa: E402
import k0_flattened_contact_sweep_regression_6900 as Flat  # noqa: E402


CAP = 4_200_000_000
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
if soft < 0 or soft > CAP:
    resource.setrlimit(resource.RLIMIT_AS, (CAP, hard))


# name, profile at L=U, maximum number of extra old-cap layers
PROFILES = (
    ("target_sign_m4", Old.K0.Profile(12, 5, 8, 4, 2, 1, 5, 5, 0, 1), 8),
    # Exact target scaling relation m=3B-1, s=B/2, U=4B.
    ("target_relation_m5", Old.K0.Profile(
        12, 5, 8, 5, 2, 1, 8, 8, 0, 1), 8),
    # Faithful target ratio chamber: 2e<g<e+w, with e=n-g.
    ("target_faithful_m5", Old.K0.Profile(
        16, 7, 11, 5, 2, 1, 8, 8, 0, 1), 8),
    ("target_sign_m3", Old.K0.Profile(10, 3, 6, 3, 2, 1, 5, 5, 0, 1), 8),
    ("target_sign_m5", Old.K0.Profile(14, 5, 8, 5, 3, 1, 7, 7, 0, 1), 10),
    ("target_sign_s2", Old.K0.Profile(15, 6, 9, 5, 4, 2, 7, 7, 0, 1), 10),
    ("target_scaled", Old.K0.Profile(12, 5, 8, 6, 2, 1, 8, 8, 0, 1), 10),
    # Ratio-wall controls distinguish target-sign effects from local jet data.
    ("ratio_wall_m4", Old.K0.Profile(6, 2, 4, 4, 2, 1, 6, 6, 0, 1), 3),
    ("ratio_wall_m6", Old.K0.Profile(11, 5, 8, 6, 2, 1, 8, 8, 0, 1), 3),
)


# name, agreement, candidate, tangent, off-agreement u1, errors, RNG tag
FAMILIES = (
    ("arb_spread", "spread", "zero", "top", "arbitrary", "varying", 11),
    ("arb_random", "random", "mid", "spike", "arbitrary", "alternating", 23),
    ("arb_minimal", "random", "max", "minimal", "arbitrary", "varying", 37),
    ("poly_control", "prefix", "max", "minimal", "poly", "same", 0),
    # Special constructor below: tangent is the squared error locator.
    ("locator_square", "prefix", "max", "locator_square", "arbitrary",
     "varying", 53),
)


def poly_mul(left, right):
    answer = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            answer[i + j] = (answer[i + j] + a * b) % 101
    return tuple(answer)


def locator_square_receipt(profile):
    """Target-faithful retained-bad direction Q=Xi_E^2 on agreements."""
    nodes = tuple(range(profile.n))
    agreement = nodes[:profile.agreements]
    errors = nodes[profile.agreements:]
    locator = (1,)
    for node in errors:
        locator = poly_mul(locator, ((-node) % 101, 1))
    tangent = poly_mul(locator, locator)
    polynomial = Old.polynomial_for(profile, "max", 101)
    assert Old.degree(tangent, 101) == 2 * len(errors)
    assert profile.w < Old.degree(tangent, 101) < profile.agreements

    u1 = []
    for node in nodes:
        expected = Old.evaluate(tangent, node, 101)
        if node in agreement:
            u1.append(expected)
        else:
            value = (17 * node + 3 * node * node + 29) % 101
            if value == expected:
                value = (value + 1) % 101
            u1.append(value)
    assert all(u1[node] != Old.evaluate(tangent, node, 101)
               for node in errors)
    u0 = tuple(
        Old.evaluate(polynomial, node, 101) if node in agreement
        else (Old.evaluate(polynomial, node, 101) + 1 + node) % 101
        for node in nodes)
    receipt = Old.K0.Receipt(
        nodes, agreement, 0, polynomial, u0, tuple(u1), tangent)
    actual = tuple(node for node in nodes
                   if Old.evaluate(polynomial, node, 101) == u0[node])
    assert actual == agreement
    assert Old.interpolate(
        tuple(u1[node] for node in agreement), agreement, 101) == tangent
    return receipt


def exact_rank(columns, rows, label: str) -> int:
    """Delegate to the literal exact F_101 rank implementation."""
    return Gate.exact_rank(tuple(columns), tuple(rows), label)


def contact_plus_boundary_rank(columns, rows, boundaries, label: str) -> int:
    """Rank of contact augmented by four formal Hasse-boundary rows."""
    row_index = {row: i for i, row in enumerate(rows)}
    matrix = nmod_mat(len(rows) + 4, len(columns), 101)
    for j, (column, boundary) in enumerate(zip(columns, boundaries)):
        for row, value in column.items():
            i = row_index.get(row)
            if i is not None:
                matrix[i, j] = value
        for coordinate, value in enumerate(boundary):
            matrix[len(rows) + coordinate, j] = value
    print(f"rank {label}: {matrix.nrows()}x{matrix.ncols()}",
          file=sys.stderr, flush=True)
    _, rank = matrix.rref(inplace=True)
    del matrix
    gc.collect()
    return rank


def collapsed_at_zeta(column, zeta: int):
    """Evaluate the local polynomial variable Z and retain all other rows."""
    answer = {}
    for (node, local), value in column.items():
        eps, sp, tp, rp, zp = local
        row = (node, (eps, sp, tp, rp))
        answer[row] = (answer.get(row, 0) + value * pow(zeta, zp, 101)) % 101
    return {row: value for row, value in answer.items() if value}


def pair_mul(x, y):
    """Multiply in F_101[a]/(a^2-2); 2 is a nonsquare modulo 101."""
    return ((x[0] * y[0] + 2 * x[1] * y[1]) % 101,
            (x[0] * y[1] + x[1] * y[0]) % 101)


def pair_pow(x, exponent: int):
    answer = (1, 0)
    while exponent:
        if exponent & 1:
            answer = pair_mul(answer, x)
        x = pair_mul(x, x)
        exponent //= 2
    return answer


def extension2_rank(base, zeta, label: str):
    """Exact rank after evaluation in F_(101^2), via 2x2 base blocks."""
    evaluated = []
    rows_set = set()
    for column in base:
        answer = {}
        for (node, local), value in column.items():
            eps, sp, tp, rp, zp = local
            row = (node, (eps, sp, tp, rp))
            power = pair_pow(zeta, zp)
            old = answer.get(row, (0, 0))
            answer[row] = ((old[0] + value * power[0]) % 101,
                           (old[1] + value * power[1]) % 101)
        answer = {row: value for row, value in answer.items()
                  if value != (0, 0)}
        evaluated.append(answer)
        rows_set.update(answer)
    rows = tuple(sorted(rows_set, key=repr))
    row_index = {row: i for i, row in enumerate(rows)}
    matrix = nmod_mat(2 * len(rows), 2 * len(base), 101)
    for j, column in enumerate(evaluated):
        for row, (a, b) in column.items():
            i = row_index[row]
            # Multiplication by a+b*alpha in basis (1,alpha), alpha^2=2.
            matrix[2 * i, 2 * j] = a
            matrix[2 * i, 2 * j + 1] = 2 * b
            matrix[2 * i + 1, 2 * j] = b
            matrix[2 * i + 1, 2 * j + 1] = a
    print(f"rank {label}: {matrix.nrows()}x{matrix.ncols()}",
          file=sys.stderr, flush=True)
    _, base_rank = matrix.rref(inplace=True)
    assert base_rank % 2 == 0
    rank = base_rank // 2
    del matrix
    gc.collect()
    return rank, len(rows), len(base)


def polynomial_module_specializations(monomials, columns, label: str):
    """Lower-bound the K(Z)-rank by exact ranks at several F_101 values.

    Monomials with source Z exponent zero freely generate the complete source
    over K[Z] once L>=U.  Evaluating their contact columns at a field element
    gives a specialization of that finite polynomial matrix.
    """
    base = tuple(column for q, column in zip(monomials, columns) if q[4] == 0)
    results = []
    for zeta in (0, 1, 7):
        evaluated = tuple(collapsed_at_zeta(column, zeta) for column in base)
        rows = tuple(sorted(set().union(*(set(c) for c in evaluated)), key=repr))
        rank = exact_rank(evaluated, rows, f"{label} module Z={zeta}")
        results.append({
            "field": "F101", "zeta": zeta, "rank": rank,
            "rows": len(rows), "columns": len(base),
        })
    for zeta in ((0, 1), (1, 1), (7, 3)):
        rank, rows, count = extension2_rank(
            base, zeta, f"{label} module Z={zeta[0]}+{zeta[1]}a")
        results.append({
            "field": "F101[a]/(a^2-2)", "zeta": zeta, "rank": rank,
            "rows": rows, "columns": count,
        })
    return tuple(results)


def build_columns(profile, receipt, cap: int):
    largest = replace(profile, L=cap)
    monomials = tuple(Old.K0.support(largest))
    source_degree = tuple(sum(q[1:]) for q in monomials)
    columns = tuple(Gate.contact_column(largest, receipt, q) for q in monomials)
    Gate.flattened_raw_column.cache_clear()
    all_rows = tuple(sorted(set().union(*(set(c) for c in columns)), key=repr))
    row_degree = {row: Gate.passive_degree(row) for row in all_rows}
    return monomials, source_degree, columns, all_rows, row_degree


def source_margin(profile, cap: int) -> int:
    p = replace(profile, L=cap)
    return len(Old.K0.support(p)) - profile.n * Old.relaxed_rank_bound(
        profile.m, cap, profile.B, profile.s, profile.U)


def boundary_at_cap(profile, receipt, cap: int, label: str):
    monomials, _, columns, rows, _ = build_columns(profile, receipt, cap)
    rank_contact = exact_rank(columns, rows, f"{label} endpoint C{cap}")
    boundaries = tuple(Flat.formal_boundary_gradient(
        q, receipt, profile.n, 101) for q in monomials)
    rank_augmented = contact_plus_boundary_rank(
        columns, rows, boundaries, f"{label} endpoint C{cap}+boundary")
    result = {
        "cap": cap,
        "source_columns_contact_rows": (len(columns), len(rows)),
        "source_margin_against_nominal_local_rank": source_margin(profile, cap),
        "contact_rank": rank_contact,
        "contact_nullity": len(columns) - rank_contact,
        "contact_plus_boundary_rank": rank_augmented,
        "boundary_image_rank_on_contact_kernel": rank_augmented - rank_contact,
        "computed": True,
    }
    del columns
    gc.collect()
    return result


def endpoint_caps(profile, receipt, label: str, initial_boundary):
    """Check U,U+1, first positive-margin cap, +1,+4, until rank four."""
    first_positive = profile.U
    while source_margin(profile, first_positive) <= 0:
        first_positive += 1
    initial = []
    for cap, rank in zip(
            (profile.U, profile.U + 1),
            initial_boundary["boundary_image_rank_on_contact_kernel_old_full"]):
        initial.append({
            "cap": cap,
            "source_margin_against_nominal_local_rank":
                source_margin(profile, cap),
            "boundary_image_rank_on_contact_kernel": rank,
            "computed": True,
            "reused_from_initial_transition": True,
        })

    requested = {first_positive, first_positive + 1, first_positive + 4}
    rows = list(initial)
    known_rank_four = next((row["cap"] for row in rows
                            if row["boundary_image_rank_on_contact_kernel"] == 4),
                           None)
    cap = first_positive
    final_cap = first_positive + 4
    while cap <= final_cap:
        if any(row["cap"] == cap for row in rows):
            cap += 1
            continue
        if known_rank_four is not None:
            if cap in requested:
                rows.append({
                    "cap": cap,
                    "source_margin_against_nominal_local_rank":
                        source_margin(profile, cap),
                    "boundary_image_rank_on_contact_kernel": 4,
                    "computed": False,
                    "inferred_from_source_inclusion_since_cap": known_rank_four,
                })
            cap += 1
            continue
        row = boundary_at_cap(profile, receipt, cap, label)
        rows.append(row)
        if row["boundary_image_rank_on_contact_kernel"] == 4:
            known_rank_four = cap
        cap += 1

    # If the requested window did not reach rank four, keep going, but cap
    # this finite diagnostic at eight further layers to protect the lane.
    cap = final_cap + 1
    while known_rank_four is None and cap <= first_positive + 8:
        row = boundary_at_cap(profile, receipt, cap, label)
        rows.append(row)
        if row["boundary_image_rank_on_contact_kernel"] == 4:
            known_rank_four = cap
        cap += 1
    return {
        "first_positive_margin_cap": first_positive,
        "first_boundary_rank_four_cap": known_rank_four,
        "cases": tuple(sorted(rows, key=lambda row: row["cap"])),
        "censored_without_rank_four": known_rank_four is None,
    }


def analyze(profile, receipt, label: str, max_extra: int,
            run_endpoint: bool = False, endpoint_only: bool = False):
    """Return consecutive obstruction ranks, stopping at the first zero.

    Rank(C_cap) is computed only once for each cap.  The block-triangular
    identity

      rank(delta_L) = rank(C_{L+1}) - rank(C_L) - rank(A_{L+1})

    then avoids the three largely duplicate matrices used by older sweeps.
    """
    assert profile.L == profile.U
    # First build only one successor.  A polynomial-module rank witness can
    # often prove that strictness never occurs, avoiding a long cap sweep.
    (monomials, source_degree, columns, all_rows,
     row_degree) = build_columns(profile, receipt, profile.U + 1)

    def cap_rank(cap: int) -> int:
        selected_columns = tuple(
            c for c, degree in zip(columns, source_degree) if degree <= cap)
        selected_rows = tuple(row for row in all_rows if row_degree[row] <= cap)
        return exact_rank(selected_columns, selected_rows, f"{label} C{cap}")

    rank_old = cap_rank(profile.U)
    new_cap = profile.U + 1
    face_columns = tuple(
        c for c, degree in zip(columns, source_degree) if degree == new_cap)
    top_rows = tuple(row for row in all_rows if row_degree[row] == new_cap)
    rank_top = exact_rank(face_columns, top_rows, f"{label} A{new_cap}")
    rank_new = cap_rank(new_cap)
    obstruction = rank_new - rank_old - rank_top
    assert obstruction >= 0
    steps = [{
        "old_new_cap": (profile.U, new_cap),
        "ranks_old_top_new": (rank_old, rank_top, rank_new),
        "face_columns_top_rows": (len(face_columns), len(top_rows)),
        "top_kernel": len(face_columns) - rank_top,
        "obstruction_rank": obstruction,
    }]

    old_pairs = tuple(
        (q, c) for q, c, degree in zip(monomials, columns, source_degree)
        if degree <= profile.U)
    old_monomials = tuple(pair[0] for pair in old_pairs)
    old_columns = tuple(pair[1] for pair in old_pairs)
    old_rows = tuple(row for row in all_rows if row_degree[row] <= profile.U)
    old_boundaries = tuple(Flat.formal_boundary_gradient(
        q, receipt, profile.n, 101) for q in old_monomials)
    full_boundaries = tuple(Flat.formal_boundary_gradient(
        q, receipt, profile.n, 101) for q in monomials)
    rank_old_augmented = contact_plus_boundary_rank(
        old_columns, old_rows, old_boundaries, f"{label} C{profile.U}+boundary")
    rank_full_augmented = contact_plus_boundary_rank(
        columns, all_rows, full_boundaries, f"{label} C{new_cap}+boundary")
    boundary = {
        "boundary_x": profile.n,
        "convention": "(Y,R,S,Z)=(P,P',Hasse2(P)=P''/2,gamma)",
        "rank_contact_plus_boundary_old_full":
            (rank_old_augmented, rank_full_augmented),
        "boundary_image_rank_on_contact_kernel_old_full":
            (rank_old_augmented - rank_old, rank_full_augmented - rank_new),
    }
    endpoint = (endpoint_caps(profile, receipt, label, boundary)
                if run_endpoint else None)

    if endpoint_only:
        specializations = ()
        generic_rank_lower_bound = None
        persistent_defect_lower_bound = None
    else:
        specializations = polynomial_module_specializations(
            monomials, columns, label)
        generic_rank_lower_bound = max(row["rank"] for row in specializations)
        persistent_defect_lower_bound = generic_rank_lower_bound - rank_top
        assert persistent_defect_lower_bound >= 0

    # Over K[Z], the eventual increment of the truncated image dimension is
    # its module rank.  Thus rank_K(Z)>rank(A) proves that no later connecting
    # obstruction can vanish.  Conversely, an initial zero propagates by Z.
    proved_never = (persistent_defect_lower_bound is not None and
                    persistent_defect_lower_bound > 0)
    first_zero = profile.U if obstruction == 0 else None

    if not endpoint_only and not proved_never and first_zero is None:
        # The specialization test is inconclusive.  Build the requested
        # largest cap once, then continue the exact finite sweep.
        del monomials, source_degree, columns, all_rows, row_degree
        gc.collect()
        max_cap = profile.U + max_extra + 1
        (monomials, source_degree, columns, all_rows,
         row_degree) = build_columns(profile, receipt, max_cap)

        def cap_rank_large(cap: int) -> int:
            selected_columns = tuple(
                c for c, degree in zip(columns, source_degree)
                if degree <= cap)
            selected_rows = tuple(
                row for row in all_rows if row_degree[row] <= cap)
            return exact_rank(
                selected_columns, selected_rows, f"{label} C{cap}")

        rank_old = cap_rank_large(profile.U + 1)
        for extra in range(1, max_extra + 1):
            old_cap = profile.U + extra
            new_cap = old_cap + 1
            face_columns = tuple(
                c for c, degree in zip(columns, source_degree)
                if degree == new_cap)
            top_rows = tuple(
                row for row in all_rows if row_degree[row] == new_cap)
            rank_top_later = exact_rank(
                face_columns, top_rows, f"{label} A{new_cap}")
            assert rank_top_later == rank_top
            rank_new = cap_rank_large(new_cap)
            obstruction = rank_new - rank_old - rank_top
            assert obstruction >= 0
            steps.append({
                "old_new_cap": (old_cap, new_cap),
                "ranks_old_top_new": (rank_old, rank_top, rank_new),
                "face_columns_top_rows": (len(face_columns), len(top_rows)),
                "top_kernel": len(face_columns) - rank_top,
                "obstruction_rank": obstruction,
            })
            if obstruction == 0:
                first_zero = old_cap
                break
            rank_old = rank_new

    if endpoint_only:
        verdict = "ENDPOINT_ONLY"
    elif proved_never:
        verdict = "PROVED_NON_EVENTUAL_BY_SPECIALIZED_MODULE_RANK"
    elif first_zero is not None:
        verdict = "STRICT_FROM_REPORTED_CAP_BY_Z_PROPAGATION"
    else:
        verdict = "CENSORED_SPECIALIZATION_INCONCLUSIVE"

    del columns
    gc.collect()
    return {
        "name": label,
        "profile_n_w_g_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "errors": profile.n - profile.agreements,
        "target_sign_gap_n_minus_2g_plus_w":
            profile.n - (2 * profile.agreements - profile.w),
        "target_ratio_chamber_2e_lt_g_lt_e_plus_w": (
            2 * (profile.n - profile.agreements) < profile.agreements <
            profile.n - profile.agreements + profile.w),
        "target_parameter_relations": {
            "m_eq_3B_minus_1": profile.m == 3 * profile.B - 1,
            "two_s_eq_B": 2 * profile.s == profile.B,
            "U_eq_4B": profile.U == 4 * profile.B,
        },
        "candidate_degree": Old.degree(receipt.polynomial, 101),
        "agreement_tangent_degree": Old.degree(receipt.tangent, 101),
        "retained_bad_direction": (
            profile.w < Old.degree(receipt.tangent, 101) <
            profile.agreements),
        "nominal_face_local_rank_increment": (
            Old.relaxed_rank_bound(
                profile.m, profile.U + 1, profile.B, profile.s, profile.U) -
            Old.relaxed_rank_bound(
                profile.m, profile.U, profile.B, profile.s, profile.U)),
        "nominal_associated_face_surplus": (
            len(face_columns) - profile.n * (
                Old.relaxed_rank_bound(
                    profile.m, profile.U + 1, profile.B, profile.s,
                    profile.U) -
                Old.relaxed_rank_bound(
                    profile.m, profile.U, profile.B, profile.s,
                    profile.U))),
        "steps": steps,
        "boundary": boundary,
        "endpoint_caps": endpoint,
        "polynomial_module_specializations":
            specializations,
        "generic_module_rank_lower_bound": generic_rank_lower_bound,
        "leading_face_rank": rank_top,
        "persistent_defect_lower_bound": persistent_defect_lower_bound,
        "eventual_verdict": verdict,
        "first_strict_old_cap": first_zero,
        "extra_layers_before_strictness": (
            None if first_zero is None else first_zero - profile.U),
        "censored_after_extra_layers": first_zero is None and not proved_never,
    }


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--profile", action="append", default=[],
        help="profile name to run; may be repeated (default: all)")
    parser.add_argument(
        "--family", action="append", default=[],
        help="family name to run; may be repeated (default: all)")
    parser.add_argument(
        "--max-extra", type=int,
        help="override every profile's maximum extra-layer count")
    parser.add_argument(
        "--endpoint", action="store_true",
        help="also check boundary ranks through the first positive-margin cap")
    parser.add_argument(
        "--endpoint-only", action="store_true",
        help="skip polynomial-module/successive-face work after endpoint caps")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    started = time.monotonic()
    profiles = tuple(row for row in PROFILES
                     if not args.profile or row[0] in args.profile)
    families = tuple(row for row in FAMILIES
                     if not args.family or row[0] in args.family)
    if not profiles or not families:
        raise SystemExit("selected no cases")

    cases = []
    for profile_name, profile, default_extra in profiles:
        assert profile.L == profile.U
        for (family_name, agreement, candidate, tangent, off, errors,
             tag) in families:
            if family_name == "locator_square":
                receipt = locator_square_receipt(profile)
            else:
                receipt = Old.make_custom_receipt(
                    profile, 101, 0, agreement, candidate, tangent, off,
                    errors, tag)
            maximum = default_extra if args.max_extra is None else args.max_extra
            cases.append(analyze(
                profile, receipt, f"{profile_name}_{family_name}", maximum,
                args.endpoint or args.endpoint_only, args.endpoint_only))

    observed = tuple(case["extra_layers_before_strictness"] for case in cases
                     if case["extra_layers_before_strictness"] is not None)
    censored = tuple(case["name"] for case in cases
                     if case["censored_after_extra_layers"])
    payload = {
        "scope": "literal complete-face eventual-strictness sweep over F_101",
        "cases": cases,
        "maximum_observed_extra_layers": max(observed) if observed else None,
        "censored_cases": censored,
        "guard": (
            "Finite exact controls only. Once-zero propagation follows from "
            "Z-equivariance for complete faces at L>=U, but no finite sweep "
            "proves a uniform target regularity bound."
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    payload["runtime"] = {
        "seconds": round(time.monotonic() - started, 3),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "address_space_cap_bytes": CAP,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
