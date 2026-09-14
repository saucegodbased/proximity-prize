#!/usr/bin/env python3
"""Find the first closing raw-S (Y,Z) band on one fixed high receipt.

The constant-T closure at ``Y=m,Z=0`` is not universal.  This focused gate
starts with the complete subcritical S staircase and then admits the remaining
S bands lexicographically by Y degree and seed degree until boundary rank four
first appears.  It also records the degrees of the Newton quotients of the
agreement tangent by every size-(w+1) anchor locator; this directly tests the
hypothesis that nonconstant quotient degree delays the closing Y grade.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict
import hashlib
from itertools import combinations
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_poly

sys.path.insert(0, ".experiments")
import k0_target_ratio_constant_t_gate_6900 as Gate  # noqa: E402
import k0_target_ratio_raw_1rs_layer_gate_6900 as Shape  # noqa: E402
import k0_target_ratio_raw_s_active_filtration_6900 as Active  # noqa: E402


K0 = Gate.K0
P = Gate.P


def make_receipt(profile, trial: int, tangent_kind: str):
    if tangent_kind != "anchor_constant":
        return K0.make_receipt(profile, trial, tangent_kind)
    # Start from a fully generic deterministic candidate/error receipt, then
    # prescribe Q=X^(w+1) on the agreement coordinates.  Thus Q is still a
    # bad/high tangent, while division by every degree-(w+1) anchor locator
    # has a constant quotient.  Off-agreement mismatches remain unequal.
    old = K0.make_receipt(profile, trial, "top_monomial")
    prescribed = (0,) * (profile.w + 1) + (1,)
    u1 = list(old.u1)
    u0 = list(old.u0)
    for x in old.agreement:
        u1[x] = K0.evaluate(prescribed, x)
        u0[x] = (K0.evaluate(old.polynomial, x) - old.seed * u1[x]) % P
    for x in old.nodes:
        if x not in old.agreement:
            forbidden = (K0.evaluate(old.polynomial, x) -
                         old.seed * u1[x]) % P
            if u0[x] == forbidden:
                u0[x] = (u0[x] + 1) % P
    tangent = K0.interpolate(tuple(u1[x] for x in old.agreement),
                             old.agreement)
    assert K0.poly_degree(tangent) == profile.w + 1
    return K0.Receipt(old.nodes, old.agreement, old.seed, old.polynomial,
                      tuple(u0), tuple(u1), tangent)


def anchor_quotient_degrees(receipt, width: int):
    q = K0.as_poly(receipt.tangent)
    answer = []
    for anchor in combinations(receipt.agreement, width):
        locator = nmod_poly([1], P)
        for x in anchor:
            locator *= nmod_poly([(-x) % P, 1], P)
        answer.append(K0.poly_degree(tuple(int((q // locator)[i])
                                           for i in range(len(q // locator)))))
    return tuple(answer)


def run(profile, trial: int, tangent_kind: str):
    started = time.monotonic()
    receipt = make_receipt(profile, trial, tangent_kind)
    assert K0.poly_degree(receipt.tangent) > profile.w
    monomials = K0.support(profile)
    contact = Shape.full_contact(profile, receipt, monomials)
    boundary = Shape.full_boundary(receipt, monomials, profile.n)
    base = tuple(j for j, (_, _, rp, sp, _) in enumerate(monomials)
                 if (rp, sp) in {(0, 0), (1, 0)})
    admitted_s = tuple(
        j for j, (_, yp, rp, sp, _) in enumerate(monomials)
        if (rp, sp) == (0, 1) and yp < profile.m)
    initial = Active.analyze(
        contact, boundary, monomials, base + admitted_s)[
            "columns_contact_rank_kernel_boundary_gain"]
    precritical_s = admitted_s
    prefixes = []
    first_gain4 = None
    for y in range(profile.m, min(profile.U, profile.L)):
        for z in range(profile.L - (y + 1) + 1):
            band = tuple(
                j for j, (_, yp, rp, sp, zp) in enumerate(monomials)
                if (rp, sp, yp, zp) == (0, 1, y, z))
            assert band
            admitted_s += band
            result = Active.analyze(
                contact, boundary, monomials, base + admitted_s)[
                    "columns_contact_rank_kernel_boundary_gain"]
            row = {
                "new_band_Y_Z_width": (y, z, len(band)),
                "columns_contact_rank_kernel_gain": result,
            }
            prefixes.append(row)
            if result[-1] == 4:
                first_gain4 = row
                break
        if first_gain4 is not None:
            break

    quotient_degrees = anchor_quotient_degrees(receipt, profile.w + 1)

    # A direct two-axis discriminator on the same matrix: determine whether
    # the observed z=1 closure really needs the z=0 predecessor, and whether
    # one higher Y grade at z=0 can replace it.
    def band_at(y, z):
        return tuple(
            j for j, (_, yp, rp, sp, zp) in enumerate(monomials)
            if (rp, sp, yp, zp) == (0, 1, y, z))

    z0 = band_at(profile.m, 0)
    z1 = band_at(profile.m, 1)
    y_next_z0 = band_at(profile.m + 1, 0)
    alternatives = {}
    for label, extra in (
            ("critical_z1_without_z0", z1),
            ("critical_z0_then_next_Y_z0", z0 + y_next_z0),
            ("next_Y_z0_without_critical", y_next_z0)):
        if extra:
            alternatives[label] = Active.analyze(
                contact, boundary, monomials, base + precritical_s + extra)[
                    "columns_contact_rank_kernel_boundary_gain"]
    return {
        "profile_n_w_A_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "trial_and_tangent_kind": (trial, tangent_kind),
        "agreement_set": receipt.agreement,
        "candidate_and_tangent_degrees": (
            K0.poly_degree(receipt.polynomial),
            K0.poly_degree(receipt.tangent)),
        "tangent_second_derivative_degree": K0.poly_degree(
            K0.derivative_coefficients(receipt.tangent, 2)),
        "anchor_quotient_degrees_over_all_w_plus_1_subsets":
            quotient_degrees,
        "anchor_quotient_degree_counts": tuple(sorted(
            {degree: quotient_degrees.count(degree)
             for degree in set(quotient_degrees)}.items())),
        "initial_after_all_S_Y_less_than_m": initial,
        "successive_S_bands": tuple(prefixes),
        "first_gain4": first_gain4,
        "axis_trade_controls": alternatives,
        "runtime": {
            "seconds": round(time.monotonic() - started, 3),
            "peak_rss_kib": resource.getrusage(
                resource.RUSAGE_SELF).ru_maxrss,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--profile", choices=("exact", "ceiling"),
                        default="exact")
    parser.add_argument("--trial", type=int, default=401)
    parser.add_argument("--kind", choices=(
        "anchor_constant", "top_monomial", "top_dense"),
                        default="top_monomial")
    args = parser.parse_args()
    profile = Gate.EXACT if args.profile == "exact" else Gate.CEILING
    payload = {
        "scope": "one fixed high-tangent raw-S grade/seed extension",
        "field": "F_101",
        "case": run(profile, args.trial, args.kind),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(
        canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
