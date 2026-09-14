#!/usr/bin/env python3
"""Exact four-high-contact gate for the literal m69 two-row chain.

For `(r,s,q)=(0,0,26)`, deficient outputs are y=41,42.  In the branch
`W=1/E`, clear the denominator using the terminal exponent T=94.  At high
source contacts k=41+2j, j=0,1,2,3, the normalized source-facing dual is

    E^(53-2j) * (lambda_41 + (j/21)*lambda_42) = x*G_j.

After multiplication by E^(2j), the left side is affine in j.  Exact second
differences give two short polynomial identities.  Each makes G_0 or G_1
divisible by E^2, impossible because deg(E^2)>=4302 while the dual caps are
3302 and 3300.  Thus every source annihilator is zero and these four contacts
already span the complete two-row cyclic output.

The calculation applies to every root-free E in the m69 interval when N0=1,
including the minimal nondividing example E=X^2151-2.  It does not handle a
nonconstant numerator.
"""

from __future__ import annotations

from math import comb, gcd
import hashlib
import json
from pathlib import Path
import resource
import sys


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import m69_reciprocal_all_defect_interval_gate_6900 as profile


P = 2_130_706_433
N = profile.N
E_MIN = 2_151
E_MAX = 18_414
OUTPUTS = (41, 42)
CONTACTS = (41, 43, 45, 47)
TERMINAL = 94
Q = 26
PROFILE_SHA256 = "9417a5797aa188cb6a1381b7c11e54f3df0ecf46908ad452d6dee925e1ae5069"


def main():
    profile_path = Path(profile.__file__)
    assert hashlib.sha256(profile_path.read_bytes()).hexdigest() == PROFILE_SHA256
    _defects, _shapes, coefficients = profile.defect_census()
    chain = tuple(y for y, r, s, q in coefficients
                  if (r, s, q) == (0, 0, Q))
    assert chain == OUTPUTS

    records = []
    inverse_21 = pow(21, -1, P)
    for j, k in enumerate(CONTACTS):
        width = profile.width(k, 0, 0)
        depth, cap = divmod(width, N)
        complement = N - cap
        first = comb(k, 41) % P
        second = comb(k, 42) % P
        assert first != 0
        normalized_direction = (1, second * pow(first, -1, P) % P)
        assert normalized_direction == (1, j * inverse_21 % P)
        assert TERMINAL - k == 53 - 2 * j
        records.append((
            j, k, depth, cap, complement,
            (first, second), normalized_direction, TERMINAL - k,
        ))

    assert tuple(record[3] for record in records) == (
        258842, 258844, 258846, 258848)
    assert tuple(record[4] for record in records) == (3302, 3300, 3298, 3296)

    # The aligned normalized Pascal directions are affine in j, so both
    # vector-valued second differences vanish exactly in the target field.
    directions = [record[6] for record in records]
    for start in (0, 1):
        second_difference = tuple(
            (directions[start + 2][coordinate]
             - 2 * directions[start + 1][coordinate]
             + directions[start][coordinate]) % P
            for coordinate in range(2)
        )
        assert second_difference == (0, 0)

    degree_gates = {
        "minimum_E_squared_degree": 2 * E_MIN,
        "maximum_G0_degree": 3302 - 1,
        "maximum_G1_degree": 3300 - 1,
        "maximum_first_recurrence_degree": max(
            4 * E_MAX + (3298 - 1),
            2 * E_MAX + (3300 - 1),
            3302 - 1),
        "maximum_second_recurrence_degree": max(
            4 * E_MAX + (3296 - 1),
            2 * E_MAX + (3298 - 1),
            3300 - 1),
    }
    assert degree_gates == {
        "minimum_E_squared_degree": 4302,
        "maximum_G0_degree": 3301,
        "maximum_G1_degree": 3299,
        "maximum_first_recurrence_degree": 76953,
        "maximum_second_recurrence_degree": 76951,
    }
    assert degree_gates["minimum_E_squared_degree"] > 3302
    assert degree_gates["maximum_first_recurrence_degree"] < N
    assert degree_gates["maximum_second_recurrence_degree"] < N

    # Exact minimal-degree, nondividing binomial example.
    exponent = E_MIN
    alpha = 2
    assert gcd(exponent, N) == 1
    alpha_to_N = pow(alpha, N, P)
    assert alpha_to_N == 2_042_248_820
    assert alpha_to_N != 1

    stable = {
        "field_prime_N": (P, N),
        "literal_chain_r_s_q_Y_T": ((0, 0, Q), chain, TERMINAL),
        "four_high_contact_records": tuple(records),
        "normalized_direction_formula": (
            "at k=41+2j: (1,j/21), j=0,1,2,3"),
        "cleared_dual_encoding": (
            "E^(53-2j)*(lambda41+(j/21)lambda42)=x*G_j"),
        "honest_second_differences": (
            "E^4G2-2E^2G1+G0=0",
            "E^4G3-2E^2G2+G1=0"),
        "degree_gates": degree_gates,
        "divisibility_conclusion": (
            "E^2|G0 and E^2|G1; short caps force G0=G1=0"),
        "source_conclusion": (
            "four high contacts have full rank on the complete two-row output "
            "for every root-free E of degree 2151..18414 when N0=1"),
        "minimal_nondividing_example": {
            "E": "X^2151-2",
            "gcd_2151_N": gcd(exponent, N),
            "two_pow_N_mod_p": alpha_to_N,
            "rootfree_on_NTT_domain": True,
        },
        "decision": "GREEN_MINIMAL_NONDIVIDING_DENOMINATOR_ONE_NUMERATOR",
        "scope": (
            "literal chain (0,0,26), numerator N0=1; no nonconstant-"
            "numerator or all-chain claim"),
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
