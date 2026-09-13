#!/usr/bin/env python3
"""Exact low/high relay minimizer in the faithful F101 Full187 control.

The high-only source (boundary degree at least two) fails all three exact
locator borders, while the complete source succeeds.  This script keeps the
high block fixed and groups every omitted low column by

    (boundary degree, passive-seed exponent, R exponent, S exponent).

It then computes exact quotient defects with the repository's sparse column
echelon and delta-deletes low groups until the retained relay is
inclusion-minimal.  The result is a mechanism discriminator, not a target
theorem: only a node-independent pattern in the surviving groups is worth
lifting to the 60/21/10/82 target.
"""

from __future__ import annotations

import hashlib
import json
import resource
import sys
from collections import Counter

sys.path.insert(0, ".experiments")
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402


def boundary_degree(monomial):
    return sum(monomial[1:4])


def relay_label(monomial):
    _x, y, r, s, z = monomial
    return (y + r + s, z, r, s)


def quotient_defect(echelon, targets):
    remainders = [echelon.reduce(target) for target in targets]
    return {
        "individual": tuple(0 if not remainder else 1
                            for remainder in remainders),
        "joint": M.modular_rank_sparse(remainders),
        "remainder_supports": tuple(len(remainder)
                                    for remainder in remainders),
    }


def partition(sequence, pieces):
    return [sequence[i::pieces] for i in range(pieces) if sequence[i::pieces]]


def main():
    compact = "--compact" in sys.argv
    M.T.PRIME = M.F.PRIME = M.PRIME
    literal = M.build_case(
        "primary_n11", (11, 5, 8, 4, 32, 1, 1, 6, 10), 8, 8, 3)

    high_indices = [i for i, monomial in enumerate(literal.monomials)
                    if boundary_degree(monomial) >= 2]
    grouped = {}
    for i, monomial in enumerate(literal.monomials):
        if boundary_degree(monomial) >= 2:
            continue
        grouped.setdefault(relay_label(monomial), []).append(i)
    labels = sorted(grouped)

    print("building fixed high-block echelon", file=sys.stderr, flush=True)
    high = M.ColumnEchelon()
    for i in high_indices:
        high.add(literal.columns[i], i)

    # Project the low relay and the three borders into the high-block
    # cokernel once.  Re-eliminating the 1,515-pivot high block in every
    # delta-debugging test is mathematically redundant and about two orders
    # of magnitude slower.
    low_indices = [i for indices in grouped.values() for i in indices]
    reduced_columns = {i: high.reduce(literal.columns[i])
                       for i in low_indices}
    reduced_targets = tuple(high.reduce(target)
                            for target in literal.targets)

    cache = {}

    def test(selected_labels):
        key = tuple(sorted(selected_labels))
        if key in cache:
            return cache[key]
        columns = []
        for label in key:
            for i in grouped[label]:
                columns.append(reduced_columns[i])
        quotient_rank = M.T.dense_matrix(columns).rank()
        bordered_rank = M.T.dense_matrix(
            columns + list(reduced_targets)).rank()
        result = {
            "joint": bordered_rank - quotient_rank,
            "quotient_rank": quotient_rank,
            "rank": high.rank + quotient_rank,
        }
        result["relay_columns"] = sum(len(grouped[label]) for label in key)
        cache[key] = result
        if not compact:
            print(
                f"test groups={len(key)} cols={result['relay_columns']} "
                f"rank={result['rank']} joint={result['joint']}",
                file=sys.stderr, flush=True)
        return result

    baseline = test(())
    complete = test(labels)
    assert baseline["joint"] > 0
    assert complete["joint"] == 0

    def minimize(order):
        current = list(order)
        pieces = 2
        while len(current) >= 2:
            removed = False
            for chunk in partition(current, min(pieces, len(current))):
                chunk_set = set(chunk)
                candidate = [label for label in current
                             if label not in chunk_set]
                if test(candidate)["joint"] == 0:
                    current = candidate
                    pieces = max(2, pieces - 1)
                    removed = True
                    break
            if removed:
                continue
            if pieces >= len(current):
                break
            pieces = min(len(current), 2 * pieces)

        # Certify one-deletion minimality in this grouping.
        changed = True
        while changed:
            changed = False
            for label in tuple(current):
                candidate = [other for other in current if other != label]
                if test(candidate)["joint"] == 0:
                    current = candidate
                    changed = True
                    break
        assert test(current)["joint"] == 0
        deletion_defects = {
            str(label): test([other for other in current if other != label])
            for label in current
        }
        assert all(receipt["joint"] > 0
                   for receipt in deletion_defects.values())
        return {
            "labels": tuple(current),
            "groups": tuple({
                "label_boundary_seed_R_S": label,
                "Y_exponent": label[0] - label[2] - label[3],
                "columns": len(grouped[label]),
                "X_exponents": tuple(
                    literal.monomials[i][0] for i in grouped[label]),
            } for label in current),
            "receipt": test(current),
            "one_group_deletion_defects": deletion_defects,
        }

    orderings = {
        "lexicographic": labels,
        "reverse_lexicographic": list(reversed(labels)),
        "small_groups_first": sorted(labels,
                                     key=lambda label: (len(grouped[label]), label)),
        "large_groups_first": sorted(labels,
                                     key=lambda label: (-len(grouped[label]), label)),
    }
    minima = {}
    for name, order in orderings.items():
        print(f"minimizing {name}", file=sys.stderr, flush=True)
        minima[name] = minimize(order)

    # Independent invariant starting set from the already certified first
    # closing filtration shell.  The whole source of centered total grade at
    # most J+1=7 is contained in the fixed high block together with exactly
    # these low groups.  Starting only from this set guards against confusing
    # a deletion-local minimum from the complete 41 groups with a global
    # cardinality lower bound.
    grade_seven_low = [label for label in labels if label[0] + label[1] <= 7]
    grade_seven_receipt = test(grade_seven_low)
    assert grade_seven_receipt["joint"] == 0
    print("minimizing invariant grade-seven low shell",
          file=sys.stderr, flush=True)
    grade_seven_minimum = minimize(grade_seven_low)

    payload = {
        "scope": (
            "exact faithful F101 low/high relay group minimization; "
            "not a target theorem"
        ),
        "field": M.PRIME,
        "parameters_n_w_A_m_D_s_t_J_L": literal.parameters,
        "high_block_predicate": "boundary degree Y+R+S >= 2",
        "high_columns": len(high_indices),
        "high_rank": high.rank,
        "low_grouping": "(boundary degree, passive seed, R exponent, S exponent)",
        "low_groups": len(labels),
        "low_columns": sum(map(len, grouped.values())),
        "high_only_defect": baseline,
        "complete_defect": complete,
        "inclusion_minimal_relays": minima,
        "grade_seven_low_start": {
            "labels": tuple(grade_seven_low),
            "receipt": grade_seven_receipt,
        },
        "grade_seven_low_minimum": grade_seven_minimum,
        "distinct_rank_tests": len(cache),
        "maximum_rss_KiB": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    if compact:
        selected_sets = {
            name: set(minimum["labels"])
            for name, minimum in minima.items()
        }
        common = set.intersection(*selected_sets.values())
        union = set.union(*selected_sets.values())

        def label_histogram(selected):
            return {
                "by_boundary_degree": dict(sorted(Counter(
                    label[0] for label in selected).items())),
                "by_seed": dict(sorted(Counter(
                    label[1] for label in selected).items())),
                "by_R_S": {
                    str(pair): count for pair, count in sorted(Counter(
                        (label[2], label[3]) for label in selected).items())
                },
            }

        compact_minima = {}
        for name, minimum in minima.items():
            deletion_joints = Counter(
                result["joint"]
                for result in minimum["one_group_deletion_defects"].values())
            compact_minima[name] = {
                "labels_boundary_seed_R_S": minimum["labels"],
                "groups": len(minimum["labels"]),
                "relay_columns": minimum["receipt"]["relay_columns"],
                "rank": minimum["receipt"]["rank"],
                "joint_defect": minimum["receipt"]["joint"],
                "one_group_deletion_joint_histogram": {
                    str(joint): count
                    for joint, count in sorted(deletion_joints.items())
                },
                "histogram": label_histogram(minimum["labels"]),
            }
        compact_payload = {
            "scope": payload["scope"],
            "field": payload["field"],
            "parameters_n_w_A_m_D_s_t_J_L": payload[
                "parameters_n_w_A_m_D_s_t_J_L"],
            "high_block_predicate": payload["high_block_predicate"],
            "high_columns": payload["high_columns"],
            "high_rank": payload["high_rank"],
            "low_grouping": payload["low_grouping"],
            "low_groups": payload["low_groups"],
            "low_columns": payload["low_columns"],
            "high_only_defect": payload["high_only_defect"],
            "complete_defect": payload["complete_defect"],
            "inclusion_minimal_relays": compact_minima,
            "grade_seven_low_start": {
                "labels_boundary_seed_R_S": tuple(grade_seven_low),
                "groups": len(grade_seven_low),
                **grade_seven_receipt,
            },
            "grade_seven_low_minimum": {
                "labels_boundary_seed_R_S": grade_seven_minimum["labels"],
                "groups": len(grade_seven_minimum["labels"]),
                **grade_seven_minimum["receipt"],
                "one_group_deletion_joint_histogram": {
                    str(joint): count
                    for joint, count in sorted(Counter(
                        result["joint"] for result in
                        grade_seven_minimum[
                            "one_group_deletion_defects"].values()).items())
                },
                "histogram": label_histogram(grade_seven_minimum["labels"]),
            },
            "groups_common_to_all_minima": tuple(sorted(common)),
            "groups_in_union_of_minima": tuple(sorted(union)),
            "common_group_count": len(common),
            "union_group_count": len(union),
            "common_histogram": label_histogram(common),
            "distinct_rank_tests": payload["distinct_rank_tests"],
            "maximum_rss_KiB": payload["maximum_rss_KiB"],
        }
        canonical = json.dumps(
            compact_payload, sort_keys=True, separators=(",", ":"))
        compact_payload["canonical_sha256"] = hashlib.sha256(
            canonical.encode()).hexdigest()
        print(json.dumps(compact_payload, indent=2, sort_keys=True))
    else:
        canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
        payload["canonical_sha256"] = hashlib.sha256(
            canonical.encode()).hexdigest()
        print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
