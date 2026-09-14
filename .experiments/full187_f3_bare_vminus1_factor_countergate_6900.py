#!/usr/bin/env python3
"""Exact target countergate for the bare F3 ``(V-1)^60`` factor.

The outer seed displacement Z is passive in the literal O2 contact map.
For ``V=Y-Z*q_H`` and an error node x, setting all genuine contact
coordinates T,E,R,S to zero gives

    V = 1 + Z*(U1(x)-q_H(x)).

Consequently ``B*V*(V-1)^60`` has contact-order-zero coefficients
``B*d^60`` and ``B*d^61`` in passive degrees Z^60 and Z^61.  The frozen
target's first error node has B,d both nonzero, so this attractive unbounded
factor is not in the complete contact kernel even before checking the source
taper.  A valid factorized F3 construction must use the full error graph
``V-(1+Z*(U1-q_H))`` (or cancel its passive terms by another exact identity).
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import resource

import full187_target_charge13_transposed_four_residue_gate_6900 as T


def main() -> None:
    instance = T.build_target_instance()
    qh_values = instance.qh_coefficients + [
        0] * (T.N - len(instance.qh_coefficients))
    T.ntt(qh_values)

    node_index = T.G
    node = instance.omega_powers[node_index]
    difference = (
        instance.u1_values[node_index] - qh_values[node_index]) % T.P
    b_value = instance.f3_selected_error_syndrome[0]
    z60 = b_value * pow(difference, T.M, T.P) % T.P
    z61 = z60 * difference % T.P
    assert difference != 0
    assert b_value != 0
    assert z60 != 0 and z61 != 0

    stable = {
        "scope": (
            "exact frozen-target contact falsifier for the bare "
            "B*V*(V-1)^60 factor; no source-taper or production claim"
        ),
        "target_p_N_G_M": (T.P, T.N, T.G, T.M),
        "first_error_node_index_and_value": (node_index, node),
        "U1_minus_qH_at_first_error": difference,
        "partial_locator_B_at_first_error": b_value,
        "contact_order_zero_Z60_Z61_coefficients": (z60, z61),
        "literal_contact_weights": "wt(T)=1, wt(E)=3; Z is passive",
        "specialization": (
            "T=E=R=S=0 gives V=1+Z*(U1-qH), hence "
            "B*V*(V-1)^60=B*d^60*Z^60+B*d^61*Z^61"
        ),
        "decision": (
            "RED_BARE_VMINUS1_FACTOR__REQUIRE_FULL_ERROR_GRAPH_FACTOR"
        ),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    print(json.dumps({
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
