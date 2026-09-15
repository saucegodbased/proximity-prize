#!/usr/bin/env python3
"""Re-audit the k=0 passive-cap sweep against the formal flattened contact.

An earlier experiment accidentally used the compressed second-jet oracle
with an independent contact-error coordinate.  The actual k=0 formal map is

    X -> x + eps,
    Y -> u0 + u1*Z + eps*R - eps^2*S + eps^3*T,

truncated only by ``eps^m=0``.  This script rebuilds the broad transition
sweep, every earlier one-layer defect control, the deep-passive controls, and
the projected head using that literal map.  The head is now selected directly
as epsilon exponent at least three.

All ranks use deterministic sparse Gaussian elimination over the stated
prime fields under a 4 GiB address-space cap.  This is finite exact evidence,
not a target-size theorem.
"""

from __future__ import annotations

from dataclasses import asdict
from functools import lru_cache
import gc
import hashlib
import json
from math import comb, factorial
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import k0_first_positive_passive_universal_falsifier_6900 as Old  # noqa: E402
import k0_one_spare_passive_layer_discriminator_6900 as Spare  # noqa: E402
from higher_jet_literal_matrix import translated_column  # noqa: E402


K0 = Old.K0
FOUR_GIB = 4 * 1024**3
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
if soft < 0 or soft > FOUR_GIB:
    resource.setrlimit(resource.RLIMIT_AS, (FOUR_GIB, hard))


def add_entry(vector, row, value, p):
    value %= p
    if not value:
        return
    updated = (vector.get(row, 0) + value) % p
    if updated:
        vector[row] = updated
    else:
        vector.pop(row, None)


@lru_cache(maxsize=None)
def multinomial5(a, b, c, d, e):
    total = a + b + c + d + e
    return (factorial(total) //
            (factorial(a) * factorial(b) * factorial(c) * factorial(d) *
             factorial(e)))


def flattened_column(profile, receipt, monomial, p, minimum_epsilon=0):
    """Literal column with local rows (node,eps,S,T,R,Z)."""
    xp, yp, rp, sp, zp = monomial
    answer = {}
    for node in receipt.nodes:
        u0 = receipt.u0[node] % p
        u1 = receipt.u1[node] % p
        # Counts of u0, u1*Z, eps*R, -eps^2*S, eps^3*T in Y^yp.
        for nz in range(yp + 1):
            for nr in range(yp - nz + 1):
                for ns in range(yp - nz - nr + 1):
                    for nt in range(yp - nz - nr - ns + 1):
                        n0 = yp - nz - nr - ns - nt
                        epsilon_from_y = nr + 2 * ns + 3 * nt
                        if epsilon_from_y >= profile.m:
                            continue
                        coefficient = multinomial5(n0, nz, nr, ns, nt)
                        coefficient *= pow(u0, n0, p) * pow(u1, nz, p)
                        if ns & 1:
                            coefficient = -coefficient
                        for hx in range(min(xp, profile.m - 1 -
                                            epsilon_from_y) + 1):
                            epsilon = epsilon_from_y + hx
                            if epsilon < minimum_epsilon:
                                continue
                            value = (coefficient * comb(xp, hx) *
                                     pow(node, xp - hx, p))
                            row = (node, epsilon, sp + ns, nt,
                                   rp + nr, zp + nz)
                            add_entry(answer, row, value, p)
    return answer


def formal_boundary_gradient(monomial, receipt, x, p):
    """Boundary gradient at (P,P',Hasse2(P),gamma)."""
    xp, yp, rp, sp, zp = monomial
    point = (
        Old.evaluate(receipt.polynomial, x, p),
        Old.evaluate(receipt.polynomial, x, p, 1),
        Old.evaluate(receipt.polynomial, x, p, 2) * pow(2, -1, p) % p,
        receipt.seed % p,
    )
    exponents = (yp, rp, sp, zp)
    answer = []
    for coordinate in range(4):
        if exponents[coordinate] == 0:
            answer.append(0)
            continue
        value = pow(x, xp, p) * exponents[coordinate] % p
        for axis, (base, exponent) in enumerate(zip(point, exponents)):
            value = value * pow(
                base, exponent - (axis == coordinate), p) % p
        answer.append(value)
    return tuple(answer)


def oracle_conjugacy_receipt():
    """Check the exact compressed-to-formal row/column normalization."""
    p, n, w, g, m, b, s, u, cap = Old.PROFILES[-1]
    profile = K0.Profile(n, w, g, m, b, s, u, cap, 0, 1)
    receipt = Old.make_receipt(profile, p, 2, 0)
    source = K0.support(profile)
    tested_node_columns = 0
    for monomial in source:
        xp, yp, rp, sp, zp = monomial
        formal = flattened_column(profile, receipt, monomial, p)
        mapped = {}
        for node in receipt.nodes:
            compressed = translated_column(
                xp, (yp, rp, sp), zp, node, receipt.u0[node],
                receipt.u1[node], profile.m, 2, p)
            for (q, error_power, v1, v2, z), value in compressed.items():
                # V2=2*S.  Moving the raw-S column normalization to the
                # source side leaves the row multiplier 2^v2.
                row = (node, q + 3 * error_power, v2, error_power, v1, z)
                add_entry(mapped, row,
                          value * pow(2, v2 - sp, p), p)
            tested_node_columns += 1
        assert mapped == formal

        compressed_boundary = Old.gradient_vector(
            monomial, receipt, profile.n, p)
        formal_boundary = formal_boundary_gradient(
            monomial, receipt, profile.n, p)
        column_scale = pow(pow(2, sp, p), -1, p)
        expected = tuple(
            compressed_boundary[coordinate] * column_scale *
            (2 if coordinate == 2 else 1) % p
            for coordinate in range(4))
        assert formal_boundary == expected
    return {
        "field_and_profile": (p, tuple(asdict(profile).values())),
        "tested_source_columns_and_node_columns": (
            len(source), tested_node_columns),
        "compressed_row_to_formal_row": (
            "(q,E,V1,V2,Z) -> (eps=q+3E,S=V2,T=E,R=V1,Z)"),
        "contact_coefficient_relation": (
            "formal(row,column)=2^(localS-rawS)*compressed(row,column)"),
        "boundary_relation": (
            "after raw-column scale 2^(-rawS), Y/R/Z boundary rows agree; "
            "formal Hasse2-S boundary row is twice the compressed S row"),
        "full_and_boundary_augmented_rank_conjugacy": True,
        "correct_compressed_head_filter": "q+3*E >= 3",
    }


class SparseRank:
    def __init__(self, p):
        self.p = p
        self.pivots = {}

    @property
    def rank(self):
        return len(self.pivots)

    def add(self, source):
        vector = {row: value % self.p for row, value in source.items()
                  if value % self.p}
        while vector:
            pivot = max(vector, key=repr)
            coefficient = vector[pivot]
            old = self.pivots.get(pivot)
            if old is None:
                inverse = pow(coefficient, -1, self.p)
                self.pivots[pivot] = {
                    row: value * inverse % self.p
                    for row, value in vector.items()
                    if value * inverse % self.p}
                return True
            for row, value in old.items():
                add_entry(vector, row, -coefficient * value, self.p)
        return False


def run_source(profile, receipt, monomials, p, minimum_epsilon=0):
    if len(monomials) > 2000:
        return run_source_dense(
            profile, receipt, monomials, p, minimum_epsilon)
    contact_rank = SparseRank(p)
    augmented_rank = SparseRank(p)
    rows = set()
    for index, monomial in enumerate(monomials, start=1):
        column = flattened_column(
            profile, receipt, monomial, p, minimum_epsilon)
        rows.update(column)
        contact_rank.add(column)
        augmented = dict(column)
        boundary = formal_boundary_gradient(
            monomial, receipt, profile.n, p)
        for coordinate, value in enumerate(boundary):
            if value:
                augmented[("boundary", coordinate)] = value
        augmented_rank.add(augmented)
        if index % 1000 == 0:
            print(f"  columns {index}/{len(monomials)}",
                  file=sys.stderr, flush=True)
    return {
        "columns_rows_contact_rank_nullity": (
            len(monomials), len(rows), contact_rank.rank,
            len(monomials) - contact_rank.rank),
        "boundary_Xn_gain": augmented_rank.rank - contact_rank.rank,
    }


def run_source_dense(profile, receipt, monomials, p, minimum_epsilon=0):
    """FLINT path for large sources where sparse elimination fills in."""
    columns = []
    rows = set()
    boundaries = []
    for index, monomial in enumerate(monomials, start=1):
        column = flattened_column(
            profile, receipt, monomial, p, minimum_epsilon)
        columns.append(column)
        rows.update(column)
        boundaries.append(formal_boundary_gradient(
            monomial, receipt, profile.n, p))
        if index % 1000 == 0:
            print(f"  generate {index}/{len(monomials)}",
                  file=sys.stderr, flush=True)
    row_tuple = tuple(sorted(rows, key=repr))
    row_index = {row: index for index, row in enumerate(row_tuple)}

    contact = nmod_mat(len(row_tuple), len(monomials), p)
    for column_index, column in enumerate(columns):
        for row, value in column.items():
            contact[row_index[row], column_index] = value
    contact_rank = contact.rank()
    del contact
    gc.collect()

    augmented = nmod_mat(len(row_tuple) + 4, len(monomials), p)
    for column_index, column in enumerate(columns):
        for row, value in column.items():
            augmented[row_index[row], column_index] = value
        for coordinate, value in enumerate(boundaries[column_index]):
            augmented[len(row_tuple) + coordinate, column_index] = value
    augmented_rank = augmented.rank()
    del augmented
    del columns
    gc.collect()
    return {
        "columns_rows_contact_rank_nullity": (
            len(monomials), len(row_tuple), contact_rank,
            len(monomials) - contact_rank),
        "boundary_Xn_gain": augmented_rank - contact_rank,
        "rank_engine": "FLINT nmod_mat dense",
    }


def derivative_shape_attribution(profile, receipt, monomials, p):
    """Nested raw, +R, +S, +R2 attribution for B=2 controls."""
    assert profile.B == 2 and profile.s == 1
    groups = (
        ("raw_(R,S)=(0,0)", lambda mon: mon[2] == 0 and mon[3] == 0),
        ("plus_R", lambda mon: mon[2] == 1 and mon[3] == 0),
        ("plus_S", lambda mon: mon[3] == 1),
        ("plus_R2", lambda mon: mon[2] >= 2 and mon[3] == 0),
    )
    remaining = set(monomials)
    contact = SparseRank(p)
    augmented = SparseRank(p)
    count = 0
    stages = []
    for label, predicate in groups:
        group = tuple(mon for mon in monomials if predicate(mon))
        assert set(group) <= remaining
        remaining.difference_update(group)
        for monomial in group:
            column = flattened_column(profile, receipt, monomial, p)
            contact.add(column)
            augmented_column = dict(column)
            boundary = formal_boundary_gradient(
                monomial, receipt, profile.n, p)
            for coordinate, value in enumerate(boundary):
                if value:
                    augmented_column[("boundary", coordinate)] = value
            augmented.add(augmented_column)
        count += len(group)
        stages.append({
            "stage": label,
            "new_and_cumulative_columns": (len(group), count),
            "contact_rank_nullity_boundary_gain": (
                contact.rank, count - contact.rank,
                augmented.rank - contact.rank),
        })
    assert not remaining
    kernel_stages = tuple(
        row["stage"] for row in stages
        if row["contact_rank_nullity_boundary_gain"][1] > 0)
    return {
        "nested_stages": tuple(stages),
        "first_stage_with_kernel": kernel_stages[0] if kernel_stages else None,
        "kernel_first_appears_at_highest_R_block": (
            bool(kernel_stages) and kernel_stages[0] == "plus_R2"),
    }


def broad_transition_rows():
    rows = []
    for profile_index, spec in enumerate(Old.PROFILES, start=1):
        p, n, w, g, m, b, s, u, cap = spec
        profile = K0.Profile(n, w, g, m, b, s, u, cap, 0, 1)
        previous = K0.Profile(n, w, g, m, b, s, u, cap - 1, 0, 1)
        complete = K0.support(profile)
        old = K0.support(previous)
        old_set = set(old)
        new_passive = tuple(mon for mon in complete
                            if mon not in old_set and mon[4] > 0)
        passive_extension = old + new_passive
        for family_index, family in enumerate(Old.DATA_FAMILIES):
            for gamma in (0, 5 % p):
                print((f"broad {profile_index}/{len(Old.PROFILES)} "
                       f"{family[0]} gamma={gamma}"),
                      file=sys.stderr, flush=True)
                receipt = Old.make_receipt(profile, p, family_index, gamma)
                row = {
                    "field_profile_family_seed": (
                        p, tuple(asdict(profile).values()), family[0], gamma),
                    "passive_extension": run_source(
                        profile, receipt, passive_extension, p),
                    "complete_transition_cap": run_source(
                        profile, receipt, complete, p),
                }
                if gamma == 0:
                    row["complete_derivative_shape_attribution"] = (
                        derivative_shape_attribution(
                            profile, receipt, complete, p))
                    final = row["complete_derivative_shape_attribution"][
                        "nested_stages"][-1][
                            "contact_rank_nullity_boundary_gain"]
                    complete_result = row["complete_transition_cap"]
                    assert final == (
                        complete_result[
                            "columns_rows_contact_rank_nullity"][2],
                        complete_result[
                            "columns_rows_contact_rank_nullity"][3],
                        complete_result["boundary_Xn_gain"])
                rows.append(row)
    return tuple(rows)


def one_spare_rows():
    rows = []
    for index, (label, spec, tangent_kind) in enumerate(
            Spare.DEFECT_CASES, start=1):
        print(f"spare {index}/{len(Spare.DEFECT_CASES)} {label}",
              file=sys.stderr, flush=True)
        p, profile = Spare.unpack(spec)
        receipt = Spare.arbitrary_receipt(profile, p, tangent_kind)
        base = K0.support(profile)
        base_set = set(base)
        successor = Spare.passive_successor(profile)
        successor_source = K0.support(successor)
        new_passive = tuple(mon for mon in successor_source
                            if mon not in base_set and mon[4] > 0)
        preceding = K0.Profile(
            profile.n, profile.w, profile.agreements, profile.m, profile.B,
            profile.s, profile.U, profile.L - 1, profile.k, profile.n0)
        preceding_source = K0.support(preceding)
        rows.append({
            "label": label,
            "field": p,
            "profile_n_w_g_m_B_s_U_L_k_n0":
                tuple(asdict(profile).values()),
            "base_complete": run_source(profile, receipt, base, p),
            "successor_old_plus_positive_Z_only": run_source(
                successor, receipt, base + new_passive, p),
            "preceding_cap_eps_ge_3_head": run_source(
                preceding, receipt, preceding_source, p, 3),
        })
    return tuple(rows)


def deep_rows():
    rows = []
    for index, (label, spec, tangent_kind, gamma) in enumerate(
            Spare.DEEP_PASSIVE_CONTROLS, start=1):
        print(f"deep {index}/{len(Spare.DEEP_PASSIVE_CONTROLS)} {label}",
              file=sys.stderr, flush=True)
        p, profile = Spare.unpack(spec)
        receipt = Spare.arbitrary_receipt(profile, p, tangent_kind, gamma)
        rows.append({
            "label": label,
            "field": p,
            "profile_n_w_g_m_B_s_U_L_k_n0":
                tuple(asdict(profile).values()),
            "complete_cap": run_source(
                profile, receipt, K0.support(profile), p),
        })
    return tuple(rows)


def gain_counts(rows, key):
    gains = tuple(row[key]["boundary_Xn_gain"] for row in rows)
    return {
        "rank4_and_total": (sum(gain == 4 for gain in gains), len(gains)),
        "gain_histogram": tuple(sorted(
            (gain, gains.count(gain)) for gain in set(gains))),
    }


def attribution_summary(rows):
    attributions = tuple(
        row["complete_derivative_shape_attribution"] for row in rows
        if "complete_derivative_shape_attribution" in row)
    first = tuple(row["first_stage_with_kernel"] for row in attributions)
    return {
        "gamma_zero_cases": len(attributions),
        "first_kernel_stage_histogram": tuple(sorted(
            (str(stage), first.count(stage)) for stage in set(first))),
        "kernel_first_at_highest_R_block_cases": (
            sum(row["kernel_first_appears_at_highest_R_block"]
                for row in attributions), len(attributions)),
    }


def main():
    started = time.monotonic()
    conjugacy = oracle_conjugacy_receipt()
    broad = broad_transition_rows()
    spare = one_spare_rows()
    deep = deep_rows()
    payload = {
        "scope": (
            "exact regression audit of all prior k0 transition/passive/head "
            "finite controls under the actual flattened formal contact map"),
        "literal_contact": (
            "X=x+eps; Y=u0+u1*Z+eps*R-eps^2*S+eps^3*T; "
            "rows=(node,eps,S,T,R,Z); truncate eps exponent at m; boundary "
            "uses S=Hasse2(P)=P''/2"),
        "compressed_formal_conjugacy": conjugacy,
        "actual_oracle_defect": (
            "The compressed E coordinate is a valid encoding of eps^3*T "
            "and preserves full/augmented ranks after the S normalization. "
            "The earlier projected-head code filtered only q; it had to "
            "filter by q+3*E>=3. Thus full/passive conclusions are replayed "
            "as controls, while old head conclusions are invalidated."),
        "broad_transition_cases": broad,
        "broad_actual_passive_summary": gain_counts(
            broad, "passive_extension"),
        "broad_actual_complete_summary": gain_counts(
            broad, "complete_transition_cap"),
        "broad_complete_derivative_shape_summary": attribution_summary(broad),
        "earlier_compressed_reported_summaries": {
            "passive_rank4": (6, 36),
            "complete_rank4": (30, 36),
        },
        "one_spare_cases": spare,
        "one_spare_actual_base_summary": gain_counts(spare, "base_complete"),
        "one_spare_actual_repaired_summary": gain_counts(
            spare, "successor_old_plus_positive_Z_only"),
        "one_spare_actual_preceding_head_summary": gain_counts(
            spare, "preceding_cap_eps_ge_3_head"),
        "earlier_compressed_one_spare_claims": {
            "successor_repaired_rank4": (7, 7),
            "nonempty_preceding_head_rank4": (4, 4),
        },
        "deep_passive_controls": deep,
        "deep_actual_summary": gain_counts(deep, "complete_cap"),
        "earlier_compressed_deep_claim": {"rank4": (3, 3)},
        "scope_guard": (
            "These exact small controls can falsify universal mechanisms but "
            "cannot prove target-size rank. Boundary gain is measured only "
            "at the deterministic off-domain point X=n."),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    payload["runtime"] = {
        "seconds": round(time.monotonic() - started, 3),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "address_space_cap_bytes": FOUR_GIB,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
