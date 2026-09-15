#!/usr/bin/env python3
"""Exact small-profile falsifier for the proposed ``old L >= U`` chamber.

For each profile this uses the literal formal contact and computes the rank of
the connecting obstruction for the complete face ``L -> L+1`` at ``L=U``.
All arithmetic is over F_101 and all off-agreement directions in the two
arbitrary families are retained.  A zero obstruction with zero top kernel is
reported as vacuous rather than evidence for strictness.
"""

from __future__ import annotations

from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

sys.path.insert(0, ".experiments")
import k0_filtered_obstruction_stability_sweep_6900 as Sweep  # noqa: E402
import k0_first_positive_passive_universal_falsifier_6900 as Old  # noqa: E402


CAP = 4_200_000_000
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
if soft < 0 or soft > CAP:
    resource.setrlimit(resource.RLIMIT_AS, (CAP, hard))


def main() -> None:
    started = time.monotonic()
    # These include every earlier profile shape, plus the m4 and m6 controls
    # that first exposed the chamber.  The prime is deliberately held fixed
    # because the literal rank helper is parameterized over F_101.
    profiles = (
        Old.K0.Profile(6, 2, 4, 3, 2, 1, 5, 5, 0, 1),
        Old.K0.Profile(9, 2, 6, 3, 2, 1, 5, 5, 0, 1),
        Old.K0.Profile(7, 3, 5, 3, 2, 1, 5, 5, 0, 1),
        Old.K0.Profile(10, 3, 7, 3, 2, 1, 5, 5, 0, 1),
        Old.K0.Profile(11, 4, 8, 3, 2, 1, 5, 5, 0, 1),
        Old.K0.Profile(6, 2, 4, 4, 2, 1, 6, 6, 0, 1),
        Old.K0.Profile(11, 5, 8, 6, 2, 1, 8, 8, 0, 1),
    )
    families = (
        ("structured", "prefix", "max", "minimal", "poly", "same", 0),
        ("arbitrary_varying", "spread", "zero", "top", "arbitrary",
         "varying", 1),
        ("arbitrary_alternating", "random", "mid", "spike", "arbitrary",
         "alternating", 2),
    )
    cases = []
    for profile in profiles:
        assert profile.L == profile.U
        for (family, agreement, candidate, tangent, off, errors, tag) in families:
            receipt = Old.make_custom_receipt(
                profile, 101, 0, agreement, candidate, tangent, off, errors,
                tag)
            label = (f"n{profile.n}_g{profile.agreements}_m{profile.m}_"
                     f"U{profile.U}_{family}")
            result = Sweep.analyze(profile, receipt, label)
            result["profile"] = asdict(profile)
            result["family"] = family
            result["informative"] = result["top_kernel"] > 0
            cases.append(result)

    informative = tuple(case for case in cases if case["informative"])
    counterexamples = tuple(case["name"] for case in informative
                            if not case["all_top_kernel_lifts"])
    payload = {
        "scope": "literal complete-face obstruction at old cap L=U over F_101",
        "cases": cases,
        "informative_case_count": len(informative),
        "informative_counterexamples": counterexamples,
        "verdict": ("RED" if counterexamples else
                    "GREEN finite controls only; theorem still open"),
        "guard": ("A zero obstruction is evidence only when top_kernel>0; "
                  "finite ranks do not establish target strictness."),
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
