#!/usr/bin/env python3
"""Adversarial exact sweep for the four-row fresh-node low-head route.

This deliberately distinguishes two statements:

* the whole fresh low-head contact image is independent of the old heads;
* only its four boundary-readout rows are independent of the old heads.

The latter is the actual terminal-detector premise and can hold even if the
former, much stronger CRT claim fails.  Every case has a retained-bad
agreement tangent and a positive low-head dimension margin.  Exact ranks are
over F_101 under a hard 4.2 GB address-space cap.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
import gc
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import k0_corrected_terminal_connecting_transpose_gate_6900 as Gate  # noqa: E402
import k0_first_positive_passive_universal_falsifier_6900 as Old  # noqa: E402
import k0_low_head_extra_probe_gate_6900 as Probe  # noqa: E402
from higher6810_secondjet_retarget_exact import relaxed_rank_bound  # noqa: E402


P = 101
CAP = 4_200_000_000
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
if soft < 0 or soft > CAP:
    resource.setrlimit(resource.RLIMIT_AS, (CAP, hard))


@dataclass(frozen=True)
class Case:
    name: str
    n: int
    w: int
    g: int
    m: int
    B: int
    s: int
    U: int
    L: int
    gamma: int
    agreement: str
    candidate: str
    tangent: str
    off_direction: str
    errors: str
    tag: int


CASES = (
    Case("structured_seed0_m7", 5, 2, 4, 7, 2, 1, 8, 8, 0,
         "prefix", "max", "minimal", "poly", "same", 0),
    Case("structured_seed2_m7", 5, 2, 4, 7, 2, 1, 8, 8, 2,
         "prefix", "max", "minimal", "poly", "same", 0),
    Case("spread_zero_top_m7", 6, 2, 4, 7, 2, 1, 8, 8, 2,
         "spread", "zero", "top", "arbitrary", "varying", 1),
    Case("random_mid_spike_m7", 6, 2, 4, 7, 2, 1, 8, 8, 2,
         "random", "mid", "spike", "arbitrary", "alternating", 2),
    Case("structured_seed2_m8", 5, 2, 4, 8, 2, 1, 8, 8, 2,
         "prefix", "max", "minimal", "poly", "same", 0),
    Case("random_mid_spike_m8", 6, 2, 4, 8, 2, 1, 8, 8, 2,
         "random", "mid", "spike", "arbitrary", "alternating", 2),
    # Near-capacity controls.  Whole-probe independence is dimensionally
    # impossible here, while a four-row gain still has enough nominal room.
    Case("near_capacity_structured_m7", 15, 2, 4, 7, 2, 1, 8, 8, 2,
         "prefix", "max", "minimal", "poly", "same", 0),
    Case("near_capacity_random_m7", 15, 2, 4, 7, 2, 1, 8, 8, 2,
         "random", "mid", "spike", "arbitrary", "alternating", 2),
    Case("near_capacity_structured_m8", 12, 2, 4, 8, 2, 1, 8, 8, 2,
         "prefix", "max", "minimal", "poly", "same", 0),
    Case("near_capacity_random_m8", 12, 2, 4, 8, 2, 1, 8, 8, 2,
         "random", "mid", "spike", "arbitrary", "alternating", 2),
)


# Load-bearing exact receipts.  These are intentionally near source capacity:
# they refute the tempting whole-probe CRT target while preserving the four
# rows that the terminal detector actually consumes.
EXPECTED_NEAR_CAPACITY = {
    "near_capacity_structured_m7": {
        "old_probe_joint_ranks": (2870, 213, 3005),
        "whole_probe_independence_gain_defect": (135, 78),
        "old_plus_four_boundary_rank_and_gain": (2874, 4),
    },
    "near_capacity_random_m7": {
        "old_probe_joint_ranks": (3195, 213, 3280),
        "whole_probe_independence_gain_defect": (85, 128),
        "old_plus_four_boundary_rank_and_gain": (3199, 4),
    },
    "near_capacity_structured_m8": {
        "old_probe_joint_ranks": (3530, 313, 3698),
        "whole_probe_independence_gain_defect": (168, 145),
        "old_plus_four_boundary_rank_and_gain": (3534, 4),
    },
    "near_capacity_random_m8": {
        "old_probe_joint_ranks": (3756, 313, 3860),
        "whole_probe_independence_gain_defect": (104, 209),
        "old_plus_four_boundary_rank_and_gain": (3760, 4),
    },
}


def make(case):
    profile = Old.K0.Profile(
        case.n, case.w, case.g, case.m, case.B, case.s, case.U, case.L,
        0, 1)
    receipt = Old.make_custom_receipt(
        profile, P, case.gamma, case.agreement, case.candidate,
        case.tangent, case.off_direction, case.errors, case.tag)
    return profile, receipt


def rank_matrix(columns, rows):
    index = {row: i for i, row in enumerate(rows)}
    matrix = nmod_mat(len(rows), len(columns), P)
    for j, column in enumerate(columns):
        for row, value in column.items():
            matrix[index[row], j] = value
    rank = matrix.rank()
    del matrix
    gc.collect()
    return rank


def analyze(case):
    started = time.monotonic()
    profile, receipt = make(case)
    monomials = tuple(Old.K0.support(profile))
    cutoff = profile.m - 3
    assert cutoff > 3
    extra_x = profile.n
    gamma = receipt.seed % P
    candidate = Old.evaluate(receipt.polynomial, extra_x, P)
    u1 = Old.evaluate(receipt.tangent, extra_x, P)
    u0 = (candidate - gamma * u1) % P
    r0 = Old.evaluate(receipt.polynomial, extra_x, P, 1)
    s0 = (Old.evaluate(receipt.polynomial, extra_x, P, 2) *
          pow(2, -1, P)) % P

    old_columns = []
    probe_columns = []
    boundaries = []
    old_rows_set = set()
    probe_rows_set = set()
    for monomial in monomials:
        old = {row: value for row, value in
               Gate.formal_column(profile, receipt, monomial).items()
               if row[1] < cutoff}
        probe = Probe.local_probe_column(
            monomial, extra_x, u0, u1, profile.m, cutoff)
        boundary = Gate.formal_boundary(profile, receipt, monomial)
        assert Probe.probe_readout(probe, u1, s0, r0, gamma) == boundary
        old_columns.append(old)
        probe_columns.append(probe)
        boundaries.append(boundary)
        old_rows_set.update(old)
        probe_rows_set.update(probe)

    old_rows = tuple(sorted(old_rows_set, key=repr))
    probe_rows = tuple(sorted(probe_rows_set, key=repr))
    old_rank = rank_matrix(old_columns, old_rows)
    probe_rank = rank_matrix(probe_columns, probe_rows)

    full_rows = tuple(("old", row) for row in old_rows) + tuple(
        ("probe", row) for row in probe_rows)
    full_columns = tuple({
        **{("old", row): value for row, value in old.items()},
        **{("probe", row): value for row, value in probe.items()},
    } for old, probe in zip(old_columns, probe_columns))
    full_joint_rank = rank_matrix(full_columns, full_rows)

    four_rows = tuple(("old", row) for row in old_rows) + tuple(
        ("boundary", i) for i in range(4))
    four_columns = tuple({
        **{("old", row): value for row, value in old.items()},
        **{("boundary", i): value for i, value in enumerate(boundary)
           if value},
    } for old, boundary in zip(old_columns, boundaries))
    four_joint_rank = rank_matrix(four_columns, four_rows)

    low_cap = relaxed_rank_bound(
        cutoff, profile.L, profile.B, profile.s, profile.U)
    margin = len(monomials) - profile.n * low_cap
    full_gain = full_joint_rank - old_rank
    four_gain = four_joint_rank - old_rank
    return {
        "case": asdict(case),
        "profile": tuple(asdict(profile).values()),
        "agreement_set": receipt.agreement,
        "candidate_and_tangent_degrees": (
            Old.degree(receipt.polynomial, P),
            Old.degree(receipt.tangent, P)),
        "source_columns": len(monomials),
        "low_head_cutoff_and_rank_cap": (cutoff, low_cap),
        "nominal_low_head_margin": margin,
        "old_and_probe_row_counts": (len(old_rows), len(probe_rows)),
        "old_probe_joint_ranks": (old_rank, probe_rank, full_joint_rank),
        "whole_probe_independence_gain_defect": (
            full_gain, probe_rank - full_gain),
        "old_plus_four_boundary_rank_and_gain": (
            four_joint_rank, four_gain),
        "whole_probe_independent": full_gain == probe_rank,
        "four_boundary_rows_independent": four_gain == 4,
        "factorization_checked_columns": len(monomials),
        "runtime_seconds": round(time.monotonic() - started, 3),
    }


def main():
    started = time.monotonic()
    cases = []
    for i, case in enumerate(CASES, start=1):
        print(f"case {i}/{len(CASES)} {case.name}", file=sys.stderr,
              flush=True)
        cases.append(analyze(case))
    by_name = {row["case"]["name"]: row for row in cases}
    for name, expected in EXPECTED_NEAR_CAPACITY.items():
        for key, value in expected.items():
            assert by_name[name][key] == value, (name, key, by_name[name][key])
        assert not by_name[name]["whole_probe_independent"]
        assert by_name[name]["four_boundary_rows_independent"]
    assert any(not row["whole_probe_independent"] for row in cases)
    stable = {
        "scope": (
            "adversarial distinction between whole extra low-head image "
            "independence and the actual four-row boundary premise"),
        "field": P,
        "cases": tuple({k: v for k, v in row.items()
                        if k != "runtime_seconds"} for row in cases),
        "all_have_positive_nominal_margin": all(
            row["nominal_low_head_margin"] >= 4 for row in cases),
        "all_four_row_gates_green": all(
            row["four_boundary_rows_independent"] for row in cases),
        "scope_guard": (
            "Finite exact evidence only. Positive margin is not used as a "
            "surjectivity proof, and no target-uniform rank is claimed."),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    payload = {
        **stable,
        "case_runtimes_seconds": tuple(
            row["runtime_seconds"] for row in cases),
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(
            Path(__file__).read_bytes()).hexdigest(),
        "runtime": {
            "seconds": round(time.monotonic() - started, 3),
            "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            "hard_address_space_cap_bytes": CAP,
        },
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
