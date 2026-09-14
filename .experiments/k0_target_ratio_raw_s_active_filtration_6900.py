#!/usr/bin/env python3
"""Critical raw-S active/seed filtration in target-ratio controls.

The aggregate shape gate shows that raw ``{1,R}`` leaves exactly the pure-S
conormal and raw ``S`` kills it.  This focused audit asks for the first
theorem-sized S layer.  It compares

* all subcritical S monomials with Y-degree < m;
* the critical layer ``Y^m S Z^z`` one seed band at a time; and
* the critical layer without the subcritical S prefix.

At the first gain-four prefix it extracts an exact contact-kernel vector with
nonzero S boundary coordinate.  There is no random or parameter search.
"""

from __future__ import annotations

from collections import Counter
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import k0_target_ratio_constant_t_gate_6900 as Gate  # noqa: E402
import k0_target_ratio_raw_1rs_layer_gate_6900 as Shape  # noqa: E402


P = Gate.P
K0 = Gate.K0


def analyze(contact: nmod_mat, boundary: nmod_mat, monomials,
            columns: tuple[int, ...], extract_witness: bool = False):
    cmat = Shape.select_columns(contact, columns)
    bmat = Shape.select_columns(boundary, columns)
    kernel, nullity = cmat.nullspace()
    contact_rank = len(columns) - nullity
    image = bmat * kernel
    gain = image.rank()
    receipt: dict[str, object] = {
        "columns_contact_rank_kernel_boundary_gain": (
            len(columns), contact_rank, nullity, gain),
    }
    if extract_witness:
        witness_column = next(j for j in range(nullity) if int(image[2, j]))
        inverse = pow(int(image[2, witness_column]), -1, P)
        coefficients = tuple(
            (monomials[source_column],
             int(kernel[row, witness_column]) * inverse % P)
            for row, source_column in enumerate(columns)
            if int(kernel[row, witness_column])
        )
        vector = nmod_mat(len(columns), 1, [
            int(kernel[row, witness_column]) * inverse % P
            for row in range(len(columns))], P)
        assert not any(int(x) for x in cmat * vector)
        boundary_value = tuple(int((bmat * vector)[i, 0]) for i in range(4))
        assert boundary_value[2] == 1
        canonical = json.dumps(
            (coefficients, boundary_value), separators=(",", ":"))
        receipt["normalized_kernel_witness"] = {
            "nonzero_coefficient_count": len(coefficients),
            "support_counts_by_R_S": tuple(sorted(Counter(
                (monomial[2], monomial[3])
                for monomial, _ in coefficients).items())),
            "support_counts_by_S_Y_degree": tuple(sorted(Counter(
                monomial[1] for monomial, _ in coefficients
                if monomial[3] == 1).items())),
            "boundary_Y_R_S_Z": boundary_value,
            # The canonical Flint nullspace vector is dense (thousands of
            # terms), so retain its exact hash and support statistics rather
            # than flooding the receipt with a non-theorem-sized basis artifact.
            "coefficient_list_and_boundary_sha256": hashlib.sha256(
                canonical.encode()).hexdigest(),
        }
    return receipt


def run(profile: K0.Profile) -> dict[str, object]:
    receipt = Gate.constant_t_receipt(profile)
    monomials = K0.support(profile)
    contact = Shape.full_contact(profile, receipt, monomials)
    boundary = Shape.full_boundary(receipt, monomials, profile.n)
    base = tuple(j for j, (_, _, rp, sp, _) in enumerate(monomials)
                 if (rp, sp) in {(0, 0), (1, 0)})
    subcritical_s = tuple(
        j for j, (_, yp, rp, sp, _) in enumerate(monomials)
        if (rp, sp) == (0, 1) and yp < profile.m)
    critical_by_z = {
        z: tuple(j for j, (_, yp, rp, sp, zp) in enumerate(monomials)
                 if (rp, sp) == (0, 1) and yp == profile.m and zp == z)
        for z in range(profile.L - (profile.m + 1) + 1)
    }
    assert critical_by_z and all(critical_by_z.values())

    base_result = analyze(contact, boundary, monomials, base)
    precritical_columns = base + subcritical_s
    precritical_result = analyze(
        contact, boundary, monomials, precritical_columns)
    seed_prefixes = []
    admitted: tuple[int, ...] = ()
    first_gain4 = None
    for z, band in sorted(critical_by_z.items()):
        admitted += band
        trial_columns = precritical_columns + admitted
        preliminary = analyze(contact, boundary, monomials, trial_columns)
        if (first_gain4 is None and
                preliminary["columns_contact_rank_kernel_boundary_gain"][-1] == 4):
            detailed = analyze(
                contact, boundary, monomials, trial_columns, True)
            first_gain4 = {"maximum_critical_seed_Z_degree": z} | detailed
            preliminary = detailed
        seed_prefixes.append({
            "maximum_critical_seed_Z_degree": z,
            "new_critical_band_columns": len(band),
        } | preliminary)
    assert first_gain4 is not None

    critical_all = tuple(j for band in critical_by_z.values() for j in band)
    critical_without_subcritical = analyze(
        contact, boundary, monomials, base + critical_all)
    return {
        "profile_n_w_g_m_B_s_U_L_k_n0": tuple(profile.__dict__.values()),
        "base_raw_1_R": base_result,
        "subcritical_S_Y_less_than_m": {
            "S_columns": len(subcritical_s),
        } | precritical_result,
        "critical_layer": {
            "monomial_form": "X^j Y^m S Z^z",
            "Y_degree": profile.m,
            "band_widths_by_Z": tuple(
                len(critical_by_z[z]) for z in sorted(critical_by_z)),
            "base_plus_whole_critical_without_subcritical_S":
                critical_without_subcritical,
            "seed_prefixes_after_subcritical_S": tuple(seed_prefixes),
            "first_gain4_seed_prefix": first_gain4,
        },
    }


def main() -> None:
    started = time.monotonic()
    cases = (run(Gate.EXACT), run(Gate.CEILING))
    assert all(
        case["base_raw_1_R"][
            "columns_contact_rank_kernel_boundary_gain"][-1] == 3
        for case in cases)
    assert all(
        case["subcritical_S_Y_less_than_m"][
            "columns_contact_rank_kernel_boundary_gain"][-1] == 3
        for case in cases)
    assert all(
        case["critical_layer"][
            "base_plus_whole_critical_without_subcritical_S"][
                "columns_contact_rank_kernel_boundary_gain"][-1] == 3
        for case in cases)
    assert tuple(
        case["critical_layer"]["first_gain4_seed_prefix"][
            "maximum_critical_seed_Z_degree"] for case in cases) == (0, 0)
    payload = {
        "scope": (
            "deterministic critical raw-S Y/seed filtration over raw {1,R} "
            "in two target-ratio controls"
        ),
        "field": "F_101",
        "coordinate_scaling_warning": (
            "the oracle curvature variable is V2=P'', whereas LowerGeometry "
            "uses Hasse-scaled S=P''/2; ranks/filtration are invariant under "
            "this nonzero diagonal rescaling, but witness coefficients are "
            "not literal LowerGeometry coefficients"
        ),
        "cases": cases,
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    payload["runtime"] = {
        "seconds": round(time.monotonic() - started, 3),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
