#!/usr/bin/env python3
"""Test the minimal raw positive-Z successor face on all seven defects.

The corrected flattened sweep showed that every old defect repairs after
adjoining all newly legal positive-Z columns.  This sharper discriminator
keeps only the new columns with raw derivative exponents ``R=S=0`` and asks
whether that smaller face already raises the complete boundary gain to four.
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
import k0_one_spare_passive_layer_discriminator_6900 as Spare  # noqa: E402


K0 = Flat.K0
FOUR_GIB = 4 * 1024**3
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
if soft < 0 or soft > FOUR_GIB:
    resource.setrlimit(resource.RLIMIT_AS, (FOUR_GIB, hard))


BASE_GAINS = (3, 3, 3, 3, 3, 1, 3)


def run_case(case, base_gain):
    label, spec, tangent_kind = case
    p, profile = Spare.unpack(spec)
    receipt = Spare.arbitrary_receipt(profile, p, tangent_kind)
    base = K0.support(profile)
    base_set = set(base)
    successor = Spare.passive_successor(profile)
    successor_source = K0.support(successor)
    raw_face = tuple(
        monomial for monomial in successor_source
        if monomial not in base_set and monomial[2] == 0 and
        monomial[3] == 0 and monomial[4] > 0)
    assert raw_face
    result = Flat.run_source_dense(
        successor, receipt, base + raw_face, p)
    return {
        "label": label,
        "field": p,
        "profile_n_w_g_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "base_boundary_gain_from_corrected_receipt": base_gain,
        "new_raw_positive_Z_face_columns": len(raw_face),
        "base_plus_raw_face": result,
        "repaired_to_gain4": result["boundary_Xn_gain"] == 4,
    }


def main():
    started = time.monotonic()
    rows = []
    for index, (case, base_gain) in enumerate(
            zip(Spare.DEFECT_CASES, BASE_GAINS), start=1):
        print(f"raw face {index}/{len(Spare.DEFECT_CASES)} {case[0]}",
              file=sys.stderr, flush=True)
        rows.append(run_case(case, base_gain))
    payload = {
        "scope": (
            "exact accepted flattened-contact repair by only the new raw "
            "R=S=0 positive-Z successor face on all prior defects"),
        "contact_and_boundary_semantics": (
            "X=x+eps; Y=u0+u1Z+epsR-eps^2S+eps^3T; eps^m=0; "
            "boundary S=Hasse2(P)"),
        "cases": tuple(rows),
        "repaired_cases_and_total": (
            sum(row["repaired_to_gain4"] for row in rows), len(rows)),
        "scope_guard": (
            "Finite exact simultaneous ranks at X=n do not prove target "
            "uniformity or identify an explicit symbolic correction."),
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
