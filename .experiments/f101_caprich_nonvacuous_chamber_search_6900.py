#!/usr/bin/env python3
"""Search fixed cap-rich chambers for a nonvacuous terminal RHS quotient.

The original n=10,s=t=1 controls are nonvacuous but do not exercise the
J1^2/J2-capable source.  Simply raising the slope cap to two makes the known
n=10,w=4 chamber vacuous.  This exact finite search therefore changes only
the small field geometry (e,g,w) across a short predeclared list while using

    D=m*g, s=2, t=1, J=m+s+t, L=J+4, Q=Xi_E^2.

Only the grade-at-most-J source and the actual F0/F1/F2 locator normals are
tested here.  Carrier modules are deliberately deferred until a genuinely
nonzero quotient is found.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, ".experiments")
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402


P = 101
M_VALUE = 5
SLOPE = 2
CURVATURE = 1

# (n,w,g).  Then e=n-g and the required locator inequalities are
# w < 2e < g.  These cases are fixed before observing any rank.
GEOMETRIES = (
    (7, 3, 5),
    (10, 5, 7),
    (11, 5, 8),
    (13, 7, 9),
    (14, 7, 10),
)


def one_geometry(n, w, g):
    error_count = n - g
    assert w < 2 * error_count < g
    j = M_VALUE + SLOPE + CURVATURE
    case = (n, w, g, M_VALUE, M_VALUE * g,
            SLOPE, CURVATURE, j, j + 4)
    offsets = (3, 5, 7, 11)[:error_count]
    literal = M.build_case(
        f"caprich_n{n}_w{w}_g{g}", case,
        actual_agreement_count=g, anchor_count=g, normal_coordinates=3,
        error_direction_offsets=offsets)
    base = [
        literal.columns[index]
        for index, monomial in enumerate(literal.monomials)
        if sum(monomial[1:]) <= j
    ]
    echelon = M.ColumnEchelon()
    for index, column in enumerate(base):
        echelon.add(column, index)
    remainders = tuple(echelon.reduce(target) for target in literal.targets)
    joint = M.modular_rank_sparse(remainders)
    result = {
        "parameters_n_w_g_m_D_s_t_J_L": case,
        "error_count_and_offsets": (error_count, offsets),
        "literal_columns": len(literal.monomials),
        "base_columns_rank": (len(base), echelon.rank),
        "individual_F0_F1_F2_defects": tuple(1 if row else 0
                                               for row in remainders),
        "joint_F0_F1_F2_defect": joint,
        "remainder_supports": tuple(len(row) for row in remainders),
        "remainders_sha256": hashlib.sha256(repr(tuple(
            tuple(sorted(row.items())) for row in remainders)).encode()).hexdigest(),
    }
    print("finished", case, "joint defect", joint, file=sys.stderr, flush=True)
    return result


def main():
    M.PRIME = M.T.PRIME = M.F.PRIME = F.PRIME = P
    payload = {
        "scope": (
            "fixed cap-rich F101 chamber search for a nonvacuous exact "
            "locator-normal quotient; carrier-free preflight"
        ),
        "field": P,
        "geometries": tuple(one_geometry(*geometry)
                            for geometry in GEOMETRIES),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
