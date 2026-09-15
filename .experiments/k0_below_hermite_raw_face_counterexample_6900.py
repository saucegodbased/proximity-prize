#!/usr/bin/env python3
"""Below-Hermite-cap counterexample to universal one-raw-face repair.

The profile was selected by a bounded exact search for a base with boundary
gain three whose next raw positive-Z face has fewer columns than the
bivariate-Hermite row cap.  The fixed receipt below verifies that one raw
face is injective modulo the base and leaves gain three.  It also records two
repairs: all positive-Z derivative shapes at that layer, or two cumulative
raw faces.
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
import k0_flattened_contact_sweep_regression_6900 as Flat  # noqa: E402


K0 = Flat.K0
P = 101
BASE = K0.Profile(10, 2, 7, 3, 2, 1, 5, 2, 0, 1)
FOUR_GIB = 4 * 1024**3
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
if soft < 0 or soft > FOUR_GIB:
    resource.setrlimit(resource.RLIMIT_AS, (FOUR_GIB, hard))


def at_cap(cap):
    return K0.Profile(
        BASE.n, BASE.w, BASE.agreements, BASE.m, BASE.B, BASE.s,
        BASE.U, cap, BASE.k, BASE.n0)


def new_positive(source, cap, raw_only):
    source_set = set(source)
    return tuple(
        monomial for monomial in K0.support(at_cap(cap))
        if monomial not in source_set and monomial[4] > 0 and
        (not raw_only or (monomial[2] == 0 and monomial[3] == 0)))


def cumulative_raw(source, cap):
    source_set = set(source)
    return tuple(
        monomial for monomial in K0.support(at_cap(cap))
        if monomial not in source_set and monomial[2] == 0 and
        monomial[3] == 0 and monomial[4] > 0)


def main():
    started = time.monotonic()
    receipt = Flat.Old.make_receipt(BASE, P, 0, 0)
    source = K0.support(BASE)
    raw_l3 = new_positive(source, 3, True)
    all_positive_l3 = new_positive(source, 3, False)
    complete_l3 = K0.support(at_cap(3))
    raw_through_l4 = cumulative_raw(source, 4)

    cases = {
        "base_L2": Flat.run_source_dense(BASE, receipt, source, P),
        "base_plus_one_raw_face_L3": Flat.run_source_dense(
            at_cap(3), receipt, source + raw_l3, P),
        "base_plus_all_positive_Z_L3": Flat.run_source_dense(
            at_cap(3), receipt, source + all_positive_l3, P),
        "complete_L3": Flat.run_source_dense(
            at_cap(3), receipt, complete_l3, P),
        "base_plus_cumulative_raw_faces_through_L4": Flat.run_source_dense(
            at_cap(4), receipt, source + raw_through_l4, P),
    }
    hermite_cap = BASE.n * BASE.m * (BASE.m + 1) // 2
    assert (len(source), len(raw_l3), hermite_cap) == (256, 57, 60)
    assert cases["base_L2"]["boundary_Xn_gain"] == 3
    assert cases["base_plus_one_raw_face_L3"]["boundary_Xn_gain"] == 3
    base_rank = cases["base_L2"]["columns_rows_contact_rank_nullity"][2]
    raw_rank = cases["base_plus_one_raw_face_L3"][
        "columns_rows_contact_rank_nullity"][2]
    assert raw_rank - base_rank == len(raw_l3)
    assert cases["base_plus_all_positive_Z_L3"]["boundary_Xn_gain"] == 4
    assert cases["complete_L3"]["boundary_Xn_gain"] == 4
    assert cases["base_plus_cumulative_raw_faces_through_L4"][
        "boundary_Xn_gain"] == 4

    payload = {
        "scope": (
            "one fixed exact below-associated-Hermite-cap counterexample "
            "and two finite repair discriminators"),
        "field": P,
        "profile_n_w_g_m_B_s_U_L_k_n0": tuple(asdict(BASE).values()),
        "datum": "prefix agreement, max candidate, minimal bad tangent, "
                 "globally polynomial direction, same nonzero error",
        "contact_and_boundary_semantics": (
            "X=x+eps; Y=u0+u1Z+epsR-eps^2S+eps^3T; eps^m=0; "
            "boundary S=Hasse2(P)"),
        "raw_L3_face_columns_and_bivariate_Hermite_cap": (
            len(raw_l3), hermite_cap),
        "cases": cases,
        "one_raw_face_relative_contact_rank": raw_rank - base_rank,
        "one_raw_face_injective_modulo_base": (
            raw_rank - base_rank == len(raw_l3)),
        "one_raw_face_verdict": (
            "RED: below the Hermite cap, the entire next raw positive-Z "
            "face is injective modulo base contact and gain remains three"),
        "repair_discriminator": (
            "GREEN in this fixed case after either admitting all positive-Z "
            "R/S shapes at L3, or admitting two cumulative raw faces through "
            "L4; neither finite repair is a uniform target theorem"),
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
