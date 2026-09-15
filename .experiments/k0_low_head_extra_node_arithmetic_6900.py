#!/usr/bin/env python3
"""Exact arithmetic gate for an eps < m-3 extra-node K0 route.

The source keeps the original multiplicity-m agreement cutoff ``m*g``.  Only
the local contact codomain is shortened from order ``m`` to order ``m-3``.
We compare its global surplus with one additional low or full local block and
with four boundary constraints.  This is capacity arithmetic only; it does
not assert that the corresponding evaluation map is surjective.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

sys.path.insert(0, ".experiments")
import higher6810_secondjet_retarget_exact as Count  # noqa: E402
import secondjet_candidate_major_function_field_rank_gate_6900 as K0  # noqa: E402


CAP = 4_200_000_000
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
if soft < 0 or soft > CAP:
    resource.setrlimit(resource.RLIMIT_AS, (CAP, hard))


@dataclass(frozen=True)
class Profile:
    name: str
    n: int
    w: int
    agreements: int
    m: int
    B: int
    s: int
    U: int
    L: int
    k: int = 0
    n0: int = 1


PROFILES = (
    Profile("target", 262_144, 131_071, 180_413, 47, 16, 8, 64, 3757),
    Profile("scaled_B2_structured", 12, 5, 8, 5, 2, 1, 8, 11),
    Profile("scaled_B2_faithful", 16, 7, 11, 5, 2, 1, 8, 11),
    Profile("scaled_B4_minimal_faithful", 10, 5, 7, 11, 4, 2, 16, 26),
)


def source_count(profile: Profile) -> int:
    if profile.name == "target":
        assert profile.w == Count.W
        return Count.coefficient_count(
            profile.agreements, profile.m, profile.L, profile.B, profile.s,
            profile.U, profile.k, profile.n0)
    literal = K0.Profile(
        profile.n, profile.w, profile.agreements, profile.m, profile.B,
        profile.s, profile.U, profile.L, profile.k, profile.n0)
    return len(K0.support(literal))


def analyze(profile: Profile):
    source = source_count(profile)
    full = Count.relaxed_rank_bound(
        profile.m, profile.L, profile.B, profile.s, profile.U)
    low_order = profile.m - 3
    low = Count.relaxed_rank_bound(
        low_order, profile.L, profile.B, profile.s, profile.U)
    full_margin = source - profile.n * full
    low_margin = source - profile.n * low
    assert low <= full
    assert low_margin == full_margin + profile.n * (full - low)
    return {
        "profile": asdict(profile),
        "errors": profile.n - profile.agreements,
        "target_parameter_relations": {
            "m_eq_3B_minus_1": profile.m == 3 * profile.B - 1,
            "two_s_eq_B": 2 * profile.s == profile.B,
            "U_eq_4B": profile.U == 4 * profile.B,
        },
        "target_ratio_chamber_2e_lt_g_lt_e_plus_w": (
            2 * (profile.n - profile.agreements) < profile.agreements <
            profile.n - profile.agreements + profile.w),
        "source_count_with_unchanged_mg_cutoff": source,
        "full_and_low_local_rank": (full, low),
        "omitted_last_three_epsilon_rank_per_node": full - low,
        "full_global_margin": full_margin,
        "low_global_margin": low_margin,
        "low_margin_after_one_extra_low_local_block": low_margin - low,
        "low_margin_after_one_extra_full_local_block": low_margin - full,
        "low_margin_after_four_boundary_rows": low_margin - 4,
        "whole_extra_low_blocks_covered": low_margin // low,
        "covers_one_extra_low_block": low_margin >= low,
        "covers_one_extra_full_block": low_margin >= full,
        "covers_four_boundary_rows": low_margin >= 4,
    }


def main() -> None:
    started = time.monotonic()
    cases = tuple(analyze(profile) for profile in PROFILES)
    assert tuple(case["full_global_margin"] for case in cases) == (
        2_371_080, 1, 14, 186)
    assert tuple(case["low_global_margin"] for case in cases) == (
        9_030_892_006_920, 4_129, 5_518, 45_816)
    assert all(case["covers_one_extra_full_block"] for case in cases)
    payload = {
        "scope": (
            "exact source-versus-low-head capacity; source cutoff remains "
            "m*g while local contact order is m-3"),
        "cases": cases,
        "guard": (
            "Positive margin does not prove CRT/evaluation surjectivity or "
            "boundary rank. It only removes capacity as an obstruction."),
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
