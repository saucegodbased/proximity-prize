#!/usr/bin/env python3
"""Exact narrow correction gate for the k=0 direct-Y head witness.

This deliberately uses the *formal flattened* contact model

    Y |-> u0 + u1*Z + eps*R - eps^2*S + eps^3*T

and retains the literal ordinary-epsilon orders ``3 <= e < m``.  It does
not use the older ``higher_jet_literal_matrix`` oracle, whose divided-power
``E`` coordinate and missing ``T`` channel are inappropriate for this gate.

For the direct witness

    C1 = Lambda_G^(m-1) A,
    A  = Y-P-(Z-gamma)Q,

we test whether its simultaneous error-head trace is in the span of every
source-legal X/passive-seed shift of the four smallest automatically
zero-boundary companions

    C2, (Z-gamma)C1, RG*C1, SG*C1,

where ``RG`` and ``SG`` are centered only for the literal boundary map.
Every generated column is checked for source membership, zero boundary, and
complete contact zero on agreements before it is admitted.  The m6 and m8
instances are exact F_101 controls, not a target-uniform interpolation
theorem.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import asdict, replace
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

sys.path.insert(0, ".experiments")
import k0_centered_head_y_correction_gate_6900 as Flat  # noqa: E402
import k0_degree4_degree5_full_sr_attribution_6900 as Degree  # noqa: E402
import k0_target_ratio_constant_t_gate_6900 as Ratio  # noqa: E402


P = 101
FOUR_GIB = 4 * 1024**3
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
if soft < 0 or soft > FOUR_GIB:
    resource.setrlimit(resource.RLIMIT_AS, (FOUR_GIB, hard))


def build_data(profile, receipt):
    source = set(Degree.K0.support(profile))
    agreement = tuple(receipt.agreement)
    errors = tuple(node for node in receipt.nodes if node not in set(agreement))
    lam_coefficients = Flat.locator(agreement)
    lam = Flat.raw_xpoly(lam_coefficients)
    p_raw = Flat.raw_xpoly(tuple(receipt.polynomial))
    q_raw = Flat.raw_xpoly(tuple(receipt.tangent))
    w_raw = Flat.raw_add(
        Flat.RAW_Z, Flat.raw_scale(Flat.RAW_ONE, -receipt.seed))
    a_raw = Flat.raw_add(
        Flat.raw_add(Flat.RAW_Y, p_raw, -1),
        Flat.raw_mul(w_raw, q_raw), -1)
    rg_raw = Flat.raw_add(
        Flat.raw_add(
            Flat.RAW_R,
            Flat.raw_xpoly(Flat.poly_derivative(tuple(receipt.polynomial))),
            -1),
        Flat.raw_mul(
            w_raw,
            Flat.raw_xpoly(Flat.poly_derivative(tuple(receipt.tangent)))),
        -1)
    sg_raw = Flat.raw_add(
        Flat.raw_add(
            Flat.RAW_S,
            Flat.raw_xpoly(
                Flat.poly_derivative(tuple(receipt.polynomial), 2)), -1),
        Flat.raw_mul(
            w_raw,
            Flat.raw_xpoly(
                Flat.poly_derivative(tuple(receipt.tangent), 2))), -1)
    c1 = Flat.raw_mul(
        Flat.raw_pow(lam, profile.m - 1), a_raw)
    c2 = Flat.raw_mul(
        Flat.raw_pow(lam, profile.m - 2), Flat.raw_pow(a_raw, 2))
    bases = (
        ("C2", c2),
        ("W_C1", Flat.raw_mul(w_raw, c1)),
        ("R_C1", Flat.raw_mul(rg_raw, c1)),
        ("S_C1", Flat.raw_mul(sg_raw, c1)),
    )
    return source, agreement, errors, w_raw, c1, bases


def legal_shifts(profile, source, w_raw, bases):
    rows = []
    counts = defaultdict(int)
    seen = set()
    for family, base in bases:
        for z_shift in range(profile.L + 1):
            seeded = Flat.raw_mul(base, Flat.raw_pow(w_raw, z_shift))
            for x_shift in range(profile.m * profile.agreements):
                shifted = Flat.source_shift(seeded, x_shift)
                if not set(shifted) <= source:
                    break
                canonical = tuple(sorted(shifted.items()))
                if canonical in seen:
                    continue
                seen.add(canonical)
                rows.append((family, x_shift, z_shift, shifted))
                counts[family] += 1
    return tuple(rows), counts


def scope_receipt(columns, target, errors):
    rows = []
    for name, nodes in (
            ("all_errors", errors),
            *((f"error_{node}", (node,)) for node in errors)):
        echelon = Flat.SparseEchelon()
        for column in columns:
            echelon.add(Flat.vector_for_nodes(column, nodes))
        residual = echelon.reduce(Flat.vector_for_nodes(target, nodes))
        rows.append({
            "scope": name,
            "family_rank": echelon.rank,
            "C1_error_head_in_span": not residual,
            "residual_support": len(residual),
        })
    return tuple(rows)


def run_case(label, profile, receipt):
    source, agreement, errors, w_raw, c1, bases = build_data(
        profile, receipt)
    boundary_x = profile.n
    c1_boundary = Flat.raw_boundary(c1, receipt, boundary_x)
    c1_contact = Flat.raw_contact(c1, receipt, profile.m, receipt.nodes)
    assert c1_boundary[0] != 0
    assert not Flat.vector_for_nodes(c1_contact, agreement, 0)
    target = Flat.vector_for_nodes(c1_contact, errors)
    assert target

    shifted, counts = legal_shifts(profile, source, w_raw, bases)
    columns_by_family = defaultdict(list)
    for family, x_shift, z_shift, polynomial in shifted:
        boundary = Flat.raw_boundary(polynomial, receipt, boundary_x)
        assert boundary == (0, 0, 0, 0), (
            family, x_shift, z_shift, boundary)
        contact = Flat.raw_contact(
            polynomial, receipt, profile.m, receipt.nodes)
        assert not Flat.vector_for_nodes(contact, agreement, 0), (
            family, x_shift, z_shift)
        columns_by_family[family].append(contact)

    stages = (
        ("C2", ("C2",)),
        ("C2_plus_W_C1", ("C2", "W_C1")),
        ("plus_literal_R_C1", ("C2", "W_C1", "R_C1")),
        ("plus_literal_R_S_C1",
         ("C2", "W_C1", "R_C1", "S_C1")),
    )
    stage_rows = []
    for stage, families in stages:
        columns = tuple(
            column for family in families
            for column in columns_by_family[family])
        stage_rows.append({
            "stage": stage,
            "families": families,
            "columns": len(columns),
            "membership": scope_receipt(columns, c1_contact, errors),
        })

    return {
        "label": label,
        "profile_n_w_g_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "agreement_set": agreement,
        "error_set": errors,
        "candidate_and_direction_degrees": (
            Degree.K0.poly_degree(receipt.polynomial),
            Degree.K0.poly_degree(receipt.tangent)),
        "direct_C1": {
            "raw_support": len(c1),
            "boundary_Y_R_S_Z": c1_boundary,
            "error_head_rows": len(target),
        },
        "legal_unique_columns_by_family": tuple(sorted(counts.items())),
        "all_columns_source_legal_zero_boundary_and_agreement_contact_zero":
            True,
        "stages": tuple(stage_rows),
    }


def main():
    started = time.monotonic()
    m6_profile = Ratio.CEILING
    m6_receipt = Ratio.constant_t_receipt(m6_profile)
    m8_profile = replace(Degree.PROFILE, L=10)
    m8_receipt = Degree.Full.M8.monomial_tangent_receipt(
        m8_profile, Degree.TRIAL, 0)
    cases = (
        run_case("target_ratio_constant_T_m6", m6_profile, m6_receipt),
        run_case("positive_margin_degree4_m8", m8_profile, m8_receipt),
    )
    payload = {
        "scope": (
            "correct flattened all-error ordinary-epsilon>=3 correction of "
            "the direct C1 witness by C2/WC1/literal centered R,S companions; "
            "finite F101 evidence only"),
        "field": "F_101",
        "contact_semantics": (
            "Y=u0+u1*Z+eps*R-eps^2*S+eps^3*T modulo eps^m"),
        "head_semantics": "literal ordinary epsilon exponent 3..m-1",
        "cases": cases,
        "scope_guard": (
            "Per-error membership is weaker than simultaneous membership. "
            "Even simultaneous finite membership does not prove a bounded-"
            "degree target interpolation/confluence theorem."),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(
        canonical.encode()).hexdigest()
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
