#!/usr/bin/env python3
"""K0 literal-LGV/path-support falsifier on the exact-ratio control.

This is intentionally a discriminator, not a target proof.  It uses the
actual relaxed K0 source and literal order-two contact expansion for

    (n,w,g,m,B,s,U,L) = (11,5,8,5,2,1,8,8)

with the deterministic constant-T receipt.  The frozen exact computation for
this same matrix has contact rank 3418 on 3604 columns and bordered gain four.
Here we compute its *support* matching rank.  If support matching saturates all
columns, a raw LGV/support-path argument sees nullity zero and hence cannot see
the exact 186-dimensional kernel or the four boundary directions.

Two tiny coefficient witnesses also audit the proposed path uniqueness:

* X^4,X^5 against the scalar/T rows at node 1 has two equal-contact-weight
  matching families and determinant one;
* X^4,X^8 against scalar rows at nodes 1,10 has the same two path products but
  determinant zero in F_101;
* Y^2 at node 6 reaches T*R*Z by two equal-weight factor-order paths.

The last two facts prevent an edge-order tie-break from becoming a proof.
"""

from __future__ import annotations

from collections import deque
import hashlib
import json
from pathlib import Path
import resource
import sys
import time


TWO_GIB = 2 * 1024**3
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
new_hard = TWO_GIB if hard == resource.RLIM_INFINITY else min(hard, TWO_GIB)
resource.setrlimit(resource.RLIMIT_AS, (min(TWO_GIB, new_hard), new_hard))

sys.path.insert(0, ".experiments")
import secondjet_candidate_major_function_field_rank_gate_6900 as K0  # noqa: E402
from higher_jet_literal_matrix import translated_column  # noqa: E402
import k0_target_ratio_constant_t_gate_6900 as Gate  # noqa: E402


P = K0.PRIME
PROFILE = Gate.EXACT
FROZEN_EXACT_CONTACT_RANK = 3418
FROZEN_EXACT_NULLITY = 186
FROZEN_EXACT_BORDERED_GAIN = 4
TARGET_P = 2_130_706_433
TARGET_D = 47 * 180_413
TARGET_ROOT_NODE = 183
TARGET_ROOT_ORDER = 2**23


def build_columns():
    receipt = Gate.constant_t_receipt(PROFILE)
    monomials = K0.support(PROFILE)
    columns = []
    for xp, yp, rp, sp, zp in monomials:
        column = {}
        for node in receipt.nodes:
            for local, coefficient in translated_column(
                    xp, (yp, rp, sp), zp, node, receipt.u0[node],
                    receipt.u1[node], PROFILE.m, 2, P).items():
                value = coefficient % P
                if value:
                    column[(node, local)] = value
        columns.append(column)
    return receipt, monomials, tuple(columns)


def indexed_support(columns):
    rows = tuple(sorted({row for column in columns for row in column}, key=repr))
    index = {row: i for i, row in enumerate(rows)}
    support = tuple(tuple(sorted(index[row] for row in column))
                    for column in columns)
    return rows, support


def hopcroft_karp(adjacency, row_count):
    """Deterministic maximum matching, with source columns on the left."""
    column_count = len(adjacency)
    pair_column = [-1] * column_count
    pair_row = [-1] * row_count
    distance = [0] * column_count
    infinity = column_count + row_count + 1

    def bfs():
        queue = deque()
        terminal = infinity
        for column in range(column_count):
            if pair_column[column] == -1:
                distance[column] = 0
                queue.append(column)
            else:
                distance[column] = infinity
        while queue:
            column = queue.popleft()
            if distance[column] >= terminal:
                continue
            for row in adjacency[column]:
                owner = pair_row[row]
                if owner == -1:
                    terminal = distance[column] + 1
                elif distance[owner] == infinity:
                    distance[owner] = distance[column] + 1
                    queue.append(owner)
        return terminal != infinity

    sys.setrecursionlimit(max(100_000, 4 * column_count + 100))

    def dfs(column):
        for row in adjacency[column]:
            owner = pair_row[row]
            if owner == -1 or (
                    distance[owner] == distance[column] + 1 and dfs(owner)):
                pair_column[column] = row
                pair_row[row] = column
                return True
        distance[column] = infinity
        return False

    cardinality = 0
    while bfs():
        for column in range(column_count):
            if pair_column[column] == -1 and dfs(column):
                cardinality += 1
    return cardinality


def coefficient(receipt, monomial, node, local):
    xp, yp, rp, sp, zp = monomial
    return translated_column(
        xp, (yp, rp, sp), zp, node, receipt.u0[node], receipt.u1[node],
        PROFILE.m, 2, P).get(local, 0) % P


def two_by_two(receipt, columns, rows):
    matrix = tuple(tuple(coefficient(receipt, column, node, local)
                         for column in columns)
                   for node, local in rows)
    diagonal = matrix[0][0] * matrix[1][1] % P
    alternate = matrix[0][1] * matrix[1][0] % P
    return {
        "columns_X_Y_R_S_Z": columns,
        "rows_node_local_T_E_R_S_Z": rows,
        "matrix_rows_by_columns": matrix,
        "two_matching_products": (diagonal, alternate),
        "determinant": (diagonal - alternate) % P,
        "equal_total_contact_weight": True,
    }


def main():
    started = time.monotonic()
    receipt, monomials, columns = build_columns()
    rows, support = indexed_support(columns)
    structural_rank = hopcroft_karp(support, len(rows))

    scalar = (0, 0, 0, 0, 0)
    outer_t = (1, 0, 0, 0, 0)
    equal_weight_nonzero = two_by_two(
        receipt,
        ((4, 0, 0, 0, 0), (5, 0, 0, 0, 0)),
        ((1, scalar), (1, outer_t)),
    )
    exact_cancellation = two_by_two(
        receipt,
        ((4, 0, 0, 0, 0), (8, 0, 0, 0, 0)),
        ((1, scalar), (10, scalar)),
    )

    # At agreement node 6, u0=0 and u1=C(6,6)=1.  In Y^2, choosing
    # (u1*Z, T*R) in either factor order gives the same local T*R*Z sink.
    y2_sink = (1, 0, 1, 0, 1)
    y2_coefficient = coefficient(receipt, (0, 2, 0, 0, 0), 6, y2_sink)
    y2_path_product = receipt.u1[6] % P

    assert len(monomials) == 3604
    assert len(rows) == 4191
    assert structural_rank == len(monomials)
    assert equal_weight_nonzero["matrix_rows_by_columns"] == ((1, 1), (4, 5))
    assert equal_weight_nonzero["determinant"] == 1
    assert exact_cancellation["matrix_rows_by_columns"] == ((1, 1), (1, 1))
    assert exact_cancellation["determinant"] == 0
    assert receipt.u1[6] == 1
    assert y2_coefficient == 2 * y2_path_product % P == 2

    # A cancellation in the *actual* benchmark field, not just F_101.
    # p-1 = 127*2^24 and 183 has exact order 2^23.  Since 2^23 < 47g,
    # both pure-X columns below obey the target's strict X cutoff.
    assert TARGET_P - 1 == 127 * 2**24
    assert pow(TARGET_ROOT_NODE, TARGET_ROOT_ORDER, TARGET_P) == 1
    assert pow(TARGET_ROOT_NODE, TARGET_ROOT_ORDER // 2, TARGET_P) != 1
    assert TARGET_ROOT_ORDER < TARGET_D
    assert all(k % TARGET_P for k in range(1, 65))

    result = {
        "scope": (
            "faithful small K0 control; falsifies literal raw-support LGV, "
            "not every possible coefficient-aware quotient network"
        ),
        "field": P,
        "profile_n_w_g_m_B_s_U_L_k_n0": tuple(PROFILE.__dict__.values()),
        "source_columns_contact_rows": (len(monomials), len(rows)),
        "support_structural_rank_nullity": (
            structural_rank, len(monomials) - structural_rank),
        "frozen_same_matrix_exact_rank_nullity": (
            FROZEN_EXACT_CONTACT_RANK, FROZEN_EXACT_NULLITY),
        "structural_bordered_gain_once_source_is_saturated": 0,
        "frozen_same_matrix_exact_bordered_gain": FROZEN_EXACT_BORDERED_GAIN,
        "equal_weight_nonzero_minor": equal_weight_nonzero,
        "equal_weight_exact_cancellation": exact_cancellation,
        "two_equal_stage_paths_inside_Y_squared": {
            "node": 6,
            "source_X_Y_R_S_Z": (0, 2, 0, 0, 0),
            "sink_local_T_E_R_S_Z": y2_sink,
            "path_choices": (("u1*Z", "T*R"), ("T*R", "u1*Z")),
            "each_path_product": y2_path_product,
            "summed_literal_coefficient": y2_coefficient,
        },
        "actual_target_field_zero_minor": {
            "field": TARGET_P,
            "factorization_p_minus_one": "127*2^24",
            "node_183_exact_multiplicative_order": TARGET_ROOT_ORDER,
            "strict_X_cutoff_D": TARGET_D,
            "columns_X_exponents": (0, TARGET_ROOT_ORDER),
            "rows_scalar_at_nodes": (1, TARGET_ROOT_NODE),
            "matrix_rows_by_columns": ((1, 1), (1, 1)),
            "determinant": 0,
            "both_columns_legal": True,
        },
        "factorial_unit_audit": {
            "largest_Y_multinomial_factorial": 64,
            "largest_outer_Hasse_factorial": 46,
            "all_1_through_64_units_mod_target_prime": True,
            "note": (
                "local coefficient loss is not caused by factorial torsion; "
                "node specialization and sums of equal-weight paths remain"
            ),
        },
        "acyclicity_audit": (
            "factor-stage expansion is a DAG because every edge increments "
            "the processed-factor counter; this does not imply a unique "
            "path family after equal monomial states are merged"
        ),
        "binary_verdict": "RED for literal raw contact support LGV",
    }
    canonical = json.dumps(result, sort_keys=True, separators=(",", ":"))
    result["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    result["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    result["runtime"] = {
        "seconds": round(time.monotonic() - started, 3),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
