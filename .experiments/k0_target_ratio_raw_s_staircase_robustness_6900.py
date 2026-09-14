#!/usr/bin/env python3
"""Focused robustness gate for the first raw-S staircase closure.

The constant-T/equal-error receipt exposed the first active curvature band,
but could have been an artefact of those two special choices.  This script
repeats exactly the same three-step filtration

  raw {1,R};
  + all legal raw S columns of Y-degree < m;
  + the seed-zero raw X^j Y^m S band

on a fixed, small list of deterministic receipts.  Two have genuinely high
agreement tangents and nonconstant anchor quotients; two are low-tangent
countercontrols for which rank four is mathematically impossible.  A pair of
ceiling-profile cases checks that the conclusion is not tied to m=5.

There is no random search: ``make_receipt`` is invoked only with the listed
trial/kind pairs, whose RNG seeds and prescribed tangent polynomials are fixed.
Independent worker processes bound wall time while keeping aggregate live RSS
well below 8 GiB.
"""

from __future__ import annotations

from concurrent.futures import ProcessPoolExecutor
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

sys.path.insert(0, ".experiments")
import k0_target_ratio_constant_t_gate_6900 as Gate  # noqa: E402
import k0_target_ratio_raw_1rs_layer_gate_6900 as Shape  # noqa: E402
import k0_target_ratio_raw_s_active_filtration_6900 as Active  # noqa: E402


K0 = Gate.K0
P = Gate.P


CASES = (
    ("exact_high_top_monomial", Gate.EXACT, 401, "top_monomial"),
    ("exact_high_top_dense", Gate.EXACT, 402, "top_dense"),
    ("exact_low_constant", Gate.EXACT, 403, "low_constant"),
    ("exact_low_quadratic", Gate.EXACT, 404, "low_quadratic"),
    ("ceiling_high_top_monomial", Gate.CEILING, 405, "top_monomial"),
    ("ceiling_low_constant", Gate.CEILING, 406, "low_constant"),
)


def filtration_columns(profile: K0.Profile, monomials):
    base = tuple(j for j, (_, _, rp, sp, _) in enumerate(monomials)
                 if (rp, sp) in {(0, 0), (1, 0)})
    subcritical = tuple(
        j for j, (_, yp, rp, sp, _) in enumerate(monomials)
        if (rp, sp) == (0, 1) and yp < profile.m)
    critical_seed_zero = tuple(
        j for j, (_, yp, rp, sp, zp) in enumerate(monomials)
        if (rp, sp, yp, zp) == (0, 1, profile.m, 0))
    assert critical_seed_zero
    return base, subcritical, critical_seed_zero


def rank_tuple(contact, boundary, monomials, columns):
    return Active.analyze(contact, boundary, monomials, columns)[
        "columns_contact_rank_kernel_boundary_gain"]


def run_case(spec):
    name, profile, trial, tangent_kind = spec
    started = time.monotonic()
    receipt = K0.make_receipt(profile, trial, tangent_kind)
    monomials = K0.support(profile)
    contact = Shape.full_contact(profile, receipt, monomials)
    boundary = Shape.full_boundary(receipt, monomials, profile.n)
    base, subcritical, critical = filtration_columns(profile, monomials)
    base_result = rank_tuple(contact, boundary, monomials, base)
    precritical_result = rank_tuple(
        contact, boundary, monomials, base + subcritical)
    critical_result = rank_tuple(
        contact, boundary, monomials, base + subcritical + critical)

    tangent_degree = K0.poly_degree(receipt.tangent)
    high = tangent_degree > profile.w
    if not high:
        # The legal pencil f+t*h has the same agreements, so its tangent
        # (h,h',h'',1) annihilates the boundary image of every source family.
        assert critical_result[-1] <= 3

    deltas_epsilons = tuple(
        ((receipt.u0[x] + receipt.seed * receipt.u1[x] -
          K0.evaluate(receipt.polynomial, x)) % P,
         (receipt.u1[x] - K0.evaluate(receipt.tangent, x)) % P)
        for x in receipt.nodes if x not in receipt.agreement)
    return {
        "case": name,
        "profile_n_w_A_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "trial_and_tangent_kind": (trial, tangent_kind),
        "agreement_set": receipt.agreement,
        "seed": receipt.seed,
        "candidate_and_tangent_degrees": (
            K0.poly_degree(receipt.polynomial), tangent_degree),
        "off_agreement_delta_epsilon": deltas_epsilons,
        "band_sizes_base_subcritical_critical_seed_zero": (
            len(base), len(subcritical), len(critical)),
        "base_columns_contact_rank_kernel_gain": base_result,
        "after_subcritical_S_columns_contact_rank_kernel_gain":
            precritical_result,
        "after_critical_seed_zero_columns_contact_rank_kernel_gain":
            critical_result,
        "expected_boundary_ceiling": 4 if high else 3,
        "critical_closes_rank_four": critical_result[-1] == 4,
        "runtime_seconds": round(time.monotonic() - started, 3),
        "worker_peak_rss_kib": resource.getrusage(
            resource.RUSAGE_SELF).ru_maxrss,
    }


def main() -> None:
    started = time.monotonic()
    # Three simultaneous matrices stayed below 4.5 GiB in the earlier exact
    # gates; keeping one slot free also avoids competing with a Lean build.
    with ProcessPoolExecutor(max_workers=3) as pool:
        cases = tuple(pool.map(run_case, CASES))
    payload = {
        "scope": (
            "fixed deterministic robustness controls for exactly the raw-S "
            "subcritical staircase plus first critical seed-zero band"
        ),
        "field": "F_101",
        "cases": cases,
    }
    high_cases = tuple(case for case in cases
                       if case["expected_boundary_ceiling"] == 4)
    low_cases = tuple(case for case in cases
                      if case["expected_boundary_ceiling"] == 3)
    payload["verdict"] = {
        "high_cases_closing_over_total": (
            sum(case["critical_closes_rank_four"] for case in high_cases),
            len(high_cases)),
        "low_cases_staying_at_most_three_over_total": (
            sum(not case["critical_closes_rank_four"] for case in low_cases),
            len(low_cases)),
        "interpretation": (
            "a high tangent is necessary for rank four but this exact finite "
            "gate tests, rather than assumes, whether the constant-T "
            "staircase is sufficient on nonconstant receipts"
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(
        canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    payload["runtime_seconds"] = round(time.monotonic() - started, 3)
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
