#!/usr/bin/env python3
"""Small exact discriminator for the cubic R2 carrier and pure-S tail.

The formal flattened contact is used throughout.  On the corrected m6,L8
receipt this script constructs

    C3 = 2 H RG^2 - 2 H' A RG - H A SG + H'' A^2,
    carrier = H^(m-3) C3,

with SG = 2*(S-Hasse2(P)-W*Hasse2(Q)).  It verifies the exact osculating
syzygy, source legality, zero formal-Hasse boundary, and complete agreement
vanishing.  It then tests every legal X/W shift against the literal eps0
local-S trace.  This is intentionally the smallest gate: it distinguishes
agreement-local order from a global full-contact correction before any large
source matrix is built.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

sys.path.insert(0, ".experiments")
import k0_centered_head_y_correction_gate_6900 as Flat  # noqa: E402
import k0_first_positive_passive_universal_falsifier_6900 as Old  # noqa: E402


P = 101
FOUR_GIB = 4 * 1024**3
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
if soft < 0 or soft > FOUR_GIB:
    resource.setrlimit(resource.RLIMIT_AS, (FOUR_GIB, hard))


def formal_boundary(poly, receipt, boundary_x):
    answer = [0, 0, 0, 0]
    for monomial, coefficient in poly.items():
        gradient = Flat.raw_monomial_boundary(
            monomial, receipt, boundary_x)
        for coordinate, value in enumerate(gradient):
            answer[coordinate] = (
                answer[coordinate] + coefficient * value) % P
    return tuple(answer)


def build(profile, receipt):
    agreement = tuple(receipt.agreement)
    h_coefficients = Flat.locator(agreement)
    h = Flat.raw_xpoly(h_coefficients)
    h1 = Flat.raw_xpoly(Flat.poly_derivative(h_coefficients))
    h2 = Flat.raw_xpoly(Flat.poly_derivative(h_coefficients, 2))
    p = tuple(receipt.polynomial)
    q = tuple(receipt.tangent)
    p_raw = Flat.raw_xpoly(p)
    q_raw = Flat.raw_xpoly(q)
    w_raw = Flat.raw_add(
        Flat.RAW_Z, Flat.raw_scale(Flat.RAW_ONE, -receipt.seed))
    a = Flat.raw_add(
        Flat.raw_add(Flat.RAW_Y, p_raw, -1),
        Flat.raw_mul(w_raw, q_raw), -1)
    rg = Flat.raw_add(
        Flat.raw_add(
            Flat.RAW_R,
            Flat.raw_xpoly(Flat.poly_derivative(p)), -1),
        Flat.raw_mul(
            w_raw, Flat.raw_xpoly(Flat.poly_derivative(q))), -1)
    # Twice the centered Hasse-two residual; this is the ordinary-second-
    # derivative expression but raw S itself remains the Hasse coordinate.
    sg = Flat.raw_add(
        Flat.raw_add(
            Flat.raw_scale(Flat.RAW_S, 2),
            Flat.raw_xpoly(Flat.poly_derivative(p, 2)), -1),
        Flat.raw_mul(
            w_raw, Flat.raw_xpoly(Flat.poly_derivative(q, 2))), -1)

    b1 = Flat.raw_add(
        Flat.raw_mul(h, rg), Flat.raw_mul(h1, a), -1)
    b2 = Flat.raw_add(
        Flat.raw_add(
            Flat.raw_mul(Flat.raw_pow(h, 2), sg),
            Flat.raw_mul(Flat.raw_mul(h, h1), rg), -2),
        Flat.raw_mul(
            Flat.raw_add(
                Flat.raw_scale(Flat.raw_pow(h1, 2), 2),
                Flat.raw_mul(h, h2), -1),
            a))
    c3 = Flat.raw_add(
        Flat.raw_add(
            Flat.raw_scale(Flat.raw_mul(h, Flat.raw_pow(rg, 2)), 2),
            Flat.raw_mul(Flat.raw_mul(h1, a), rg), -2),
        Flat.raw_add(
            Flat.raw_mul(Flat.raw_mul(h, a), sg),
            Flat.raw_mul(h2, Flat.raw_pow(a, 2)), -1), -1)

    numerator = Flat.raw_add(
        Flat.raw_scale(Flat.raw_pow(b1, 2), 2),
        Flat.raw_mul(a, b2), -1)
    assert numerator == Flat.raw_mul(h, c3)
    carriers = {
        "C3": Flat.raw_mul(Flat.raw_pow(h, profile.m - 3), c3),
        "B1_sq": Flat.raw_mul(
            Flat.raw_pow(h, profile.m - 4), Flat.raw_pow(b1, 2)),
        "A_B2": Flat.raw_mul(
            Flat.raw_pow(h, profile.m - 4), Flat.raw_mul(a, b2)),
    }
    assert Flat.raw_add(
        Flat.raw_scale(carriers["B1_sq"], 2),
        carriers["A_B2"], -1) == carriers["C3"]
    return agreement, w_raw, carriers, {
        "H": h, "A": a, "RG": rg, "SG": sg,
        "B1": b1, "B2": b2, "C3": c3,
    }


def legal_shifts(profile, source, w_raw, carrier):
    answer = []
    counts = defaultdict(int)
    for z_shift in range(profile.L + 1):
        seeded = Flat.raw_mul(carrier, Flat.raw_pow(w_raw, z_shift))
        for x_shift in range(profile.m * profile.agreements):
            shifted = Flat.source_shift(seeded, x_shift)
            if not set(shifted) <= source:
                break
            answer.append((x_shift, z_shift, shifted))
            counts[z_shift] += 1
    return tuple(answer), tuple(sorted(counts.items()))


def project(contact, nodes, epsilon_orders=None):
    selected = set(nodes)
    return {
        row: value for row, value in contact.items()
        if row[0] in selected and
        (epsilon_orders is None or row[1][0] in epsilon_orders)
    }


def membership(columns, target):
    echelon = Flat.SparseEchelon()
    for column in columns:
        echelon.add(column)
    residual = echelon.reduce(target)
    return echelon.rank, not residual, len(residual)


def main():
    started = time.monotonic()
    profile = Old.K0.Profile(11, 5, 8, 6, 2, 1, 8, 8, 0, 1)
    receipt = Old.make_custom_receipt(
        profile, P, 0, "random", "mid", "minimal", "arbitrary",
        "alternating", 2)
    source = set(Old.K0.support(profile))
    agreement, w_raw, carriers, pieces = build(profile, receipt)
    errors = tuple(node for node in receipt.nodes if node not in set(agreement))
    boundary_x = profile.n

    contacts_by_family = {}
    shifts_by_family = {}
    for family, carrier in carriers.items():
        assert set(carrier) <= source
        assert formal_boundary(carrier, receipt, boundary_x) == (0, 0, 0, 0)
        carrier_agreement = Flat.raw_contact(
            carrier, receipt, profile.m, agreement)
        assert not carrier_agreement
        carrier_all = Flat.raw_contact(
            carrier, receipt, profile.m, receipt.nodes)
        assert carrier_all

        shifts, shifts_by_z = legal_shifts(profile, source, w_raw, carrier)
        assert shifts
        contacts = []
        for _x_shift, _z_shift, polynomial in shifts:
            assert formal_boundary(
                polynomial, receipt, boundary_x) == (0, 0, 0, 0)
            contact = Flat.raw_contact(
                polynomial, receipt, profile.m, receipt.nodes)
            assert not project(contact, agreement)
            contacts.append(contact)
        contacts_by_family[family] = tuple(contacts)
        shifts_by_family[family] = {
            "columns": len(shifts),
            "X_shifts_by_external_W_power": shifts_by_z,
        }

    pure_s_contact = Flat.raw_contact(
        Flat.RAW_S, receipt, profile.m, receipt.nodes)
    assert formal_boundary(Flat.RAW_S, receipt, boundary_x) == (0, 0, 1, 0)
    scopes = []
    stages = (
        ("C3_only", ("C3",)),
        ("B1_sq_plus_A_B2", ("B1_sq", "A_B2")),
        ("all_equivalent_presentations", ("C3", "B1_sq", "A_B2")),
    )
    for stage, families in stages:
        for name, nodes in (
                ("all_nodes", receipt.nodes),
                ("agreements", agreement),
                ("errors", errors)):
            for label, orders in (("complete", None), ("eps0", {0})):
                cols = tuple(
                    project(column, nodes, orders)
                    for family in families
                    for column in contacts_by_family[family])
                target = project(pure_s_contact, nodes, orders)
                rank, contained, residual = membership(cols, target)
                scopes.append({
                    "stage": stage,
                    "scope": name,
                    "orders": label,
                    "carrier_rank": rank,
                    "pure_S_trace_in_carrier_span": contained,
                    "residual_support": residual,
                })

    assert not next(row for row in scopes
                    if row["stage"] == "all_equivalent_presentations" and
                    row["scope"] == "agreements" and
                    row["orders"] == "eps0")["pure_S_trace_in_carrier_span"]
    stable = {
        "scope": "literal formal m6 cubic-R2 carrier versus pure-S tail",
        "field": P,
        "profile_n_w_g_m_B_s_U_L_k_n0": tuple(asdict(profile).values()),
        "agreement_set": agreement,
        "error_set": errors,
        "contact_semantics": (
            "rows(eps,S,T,R,Z); Y=u0+u1Z+epsR-eps^2S+eps^3T"),
        "boundary_semantics": "(Y,R,S,Z)=(P,P',Hasse2(P),gamma)",
        "identity": "2*B1^2-A*B2=H*C3",
        "C3": "2H*RG^2-2H'*A*RG-H*A*SG+H''*A^2",
        "raw_support_sizes_H_A_RG_SG_B1_B2_C3": tuple(
            len(pieces[key]) for key in
            ("H", "A", "RG", "SG", "B1", "B2", "C3")),
        "carrier_raw_support_sizes": tuple(
            (family, len(carrier)) for family, carrier in carriers.items()),
        "legal_shifts_by_family": shifts_by_family,
        "all_carriers_source_legal_zero_boundary_and_agreement_contact": True,
        "span_results": tuple(scopes),
        "complete_source_context": (
            "the committed corrected full-source receipt has complete "
            "boundary gain 3 and annihilator ell=(1,74,26,77); C3-only "
            "failure here is the smaller agreement-local discriminator"),
        "verdict": (
            "RED_OSCULATING_CARRIERS: neither C3 nor the larger independent "
            "B1^2/A*B2 span cancels the pure-S eps0 trace, even on the three "
            "errors alone; adding the complete lower prefix is separately "
            "blocked on this finite receipt by the exact complete-source "
            "annihilator"),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    payload = {
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "runtime": {
            "seconds": round(time.monotonic() - started, 3),
            "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            "address_space_cap_bytes": FOUR_GIB,
        },
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
