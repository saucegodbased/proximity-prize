#!/usr/bin/env python3
"""Exact passive-seed module audit for the order-four covariants.

The one-layer eight-carrier block is not a convolutional state: carrier
births occur at different passive Z exponents, so adjacent Z shifts overlap.
This script keeps every literal one-node contact row and regards passive Z
as the variable of a polynomial matrix over F_101[Z].  Singular computes its
Smith form, a reduced Groebner/Popov basis for the image, and a reduced basis
for the right kernel.  Direct finite-prefix ranks independently check the
resulting right minimal indices.

The three nested carrier sets are the old eight Lambda/V/J1 carriers, those
eight plus the two J2 carriers, and the complete eleven weighted-order-four
monomials.  The calculation is repeated in two predeclared arbitrary-offset
chambers and at all three error nodes.

This is an exact m=4 local-module discriminator, not a Full187 theorem.  A
separate multiplicity check at the end is deliberately adversarial: after
multiplication by V^(m-4), the raw complete-contact rank becomes 33 already
at m=5.  Thus the attractive rank-22 result can be used at m=60 only after a
proved quotient by lower grades (or a proved restriction on forced heads).
"""

from __future__ import annotations

from collections import Counter
import hashlib
import json
import re
import subprocess
import sys

sys.path.insert(0, ".experiments")
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import f101_order4_eight_carrier_local_jet_block_6900 as E  # noqa: E402
import f101_order4_osculating_covariant_basis_gate_6900 as O  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402


P = 101
CHAMBERS = (
    ((3, 5, 7), (1, 9, 17)),
    ((11, 19, 23), (2, 13, 29)),
)

# Indices in O.weighted_order_four_families.  The order here is irrelevant
# to Smith data but makes the nesting explicit.
EIGHT = (3, 2, 6, 5, 8, 7, 9, 10)
TEN = EIGHT + (1, 4)
ELEVEN = tuple(range(11))
SUBSETS = (("eight", EIGHT), ("ten", TEN), ("eleven", ELEVEN))


def shifted_z(column, amount):
    return {
        row[:-1] + (row[-1] + amount,): coefficient
        for row, coefficient in column.items()
    }


def matrix_data(literal, node, offset, delta, family_indices, m=4,
                v_prefactor=0):
    families = O.weighted_order_four_families(literal)
    received_direction = (F.poly_eval(literal.q, node) + offset) % P
    v = O.make_generators(literal)["V"]
    prefactor = F.sparse_pow(v, v_prefactor)
    columns = []
    labels = []
    for family_index in family_indices:
        label, _exponents, _active, _seed, source = families[family_index]
        source = F.sparse_mul(source, prefactor)
        for jet in range(3):
            multiple = E.scale_by_poly(source, E.local_x_power(node, jet))
            columns.append(E.local_contact(
                multiple, node, delta, received_direction, m))
            labels.append((label, jet))
    row_types = tuple(sorted({
        row[:-1] for column in columns for row in column
    }))
    return row_types, tuple(columns), tuple(labels)


def polynomial_string(column, row_type):
    coefficients = {
        row[-1]: coefficient % P
        for row, coefficient in column.items() if row[:-1] == row_type
    }
    terms = []
    for exponent, coefficient in sorted(coefficients.items(), reverse=True):
        if not coefficient:
            continue
        if exponent == 0:
            monomial = str(coefficient)
        elif exponent == 1:
            monomial = f"{coefficient}*z"
        else:
            monomial = f"{coefficient}*z^{exponent}"
        terms.append(monomial)
    return "+".join(terms) or "0"


def matrix_payload(row_types, columns):
    return tuple(
        tuple(
            tuple(sorted(
                (row[-1], coefficient % P)
                for row, coefficient in column.items()
                if row[:-1] == row_type and coefficient % P
            ))
            for column in columns
        )
        for row_type in row_types
    )


def exponent_of_singular_monomial(polynomial):
    """Degree of a nonzero monomial printed as z, z3, -z6, or a unit."""
    polynomial = polynomial.strip()
    if "z" not in polynomial:
        return 0
    match = re.search(r"z(\d*)", polynomial)
    assert match, polynomial
    return int(match.group(1) or "1")


def singular_invariants(row_types, columns):
    entries = [
        polynomial_string(column, row_type)
        for row_type in row_types for column in columns
    ]
    diagonal_bound = min(len(row_types), len(columns))
    program = f"""
ring r=101,(z),(dp,C);
LIB \"jacobson.lib\";
option(redSB);
matrix A[{len(row_types)}][{len(columns)}]={','.join(entries)};
matrix S=smith(A);
int i;
for(i=1;i<={diagonal_bound};i++){{
  if(S[i,i]!=0){{print(\"SMITH:\"+string(i)+\":\"+string(S[i,i]));}}
}}
module Im=A[1];
for(i=2;i<=ncols(A);i++){{Im=Im,A[i];}}
module ImG=std(Im);
matrix ImB=ImG;
for(i=1;i<=ncols(ImB);i++){{
  print(\"IMAGE:\"+string(i)+\":\"+string(deg(ImB[i]))+\":\"+string(lead(ImB[i])));
}}
module KerG=std(syz(Im));
matrix KerB=KerG;
for(i=1;i<=ncols(KerB);i++){{
  print(\"KERNEL:\"+string(i)+\":\"+string(deg(KerB[i]))+\":\"+string(lead(KerB[i])));
}}
"""
    completed = subprocess.run(
        ("Singular", "-q"), input=program, text=True,
        capture_output=True, check=True, timeout=1200)
    smith = []
    image = []
    kernel = []
    lead_pattern = re.compile(r"z\d*\*gen\((\d+)\)")
    for line in completed.stdout.splitlines():
        if line.startswith("SMITH:"):
            _tag, _index, polynomial = line.split(":", 2)
            smith.append(exponent_of_singular_monomial(polynomial))
        elif line.startswith("IMAGE:"):
            _tag, _index, degree, leading = line.split(":", 3)
            match = lead_pattern.fullmatch(leading.strip())
            assert match, leading
            image.append((int(degree), int(match.group(1))))
        elif line.startswith("KERNEL:"):
            _tag, _index, degree, leading = line.split(":", 3)
            match = lead_pattern.fullmatch(leading.strip())
            assert match, leading
            kernel.append((int(degree), int(match.group(1))))
    assert smith and image
    assert len({component for _degree, component in image}) == len(image)
    assert len({component for _degree, component in kernel}) == len(kernel)
    return tuple(smith), tuple(image), tuple(kernel)


def prefix_ranks(columns, prefix_count=5):
    ranks = []
    for count in range(1, prefix_count + 1):
        shifted = tuple(
            shifted_z(column, shift)
            for shift in range(count) for column in columns
        )
        ranks.append(M.modular_rank_sparse(shifted))
    return tuple(ranks)


def count_profile(values):
    return tuple(sorted(Counter(values).items()))


EXPECTED = {
    "eight": {
        "smith": ((3, 3), (4, 6), (5, 4), (6, 2)),
        "image": ((4, 9), (5, 4), (6, 2)),
        "kernel": ((2, 7), (3, 2)),
        "prefix": (24, 48, 65, 80, 95),
    },
    "ten": {
        "smith": ((3, 3), (4, 6), (5, 7), (6, 4)),
        "image": ((4, 9), (5, 7), (6, 4)),
        "kernel": ((2, 9), (3, 1)),
        "prefix": (30, 60, 81, 101, 121),
    },
    "eleven": {
        "smith": ((3, 3), (4, 6), (5, 9), (6, 4)),
        "image": ((4, 9), (5, 9), (6, 4)),
        "kernel": ((1, 1), (2, 10)),
        "prefix": (33, 65, 87, 109, 131),
    },
}


def one_subset(literal, node, offset, delta, name, indices):
    row_types, columns, labels = matrix_data(
        literal, node, offset, delta, indices)
    smith, image, kernel = singular_invariants(row_types, columns)
    prefix = prefix_ranks(columns)
    profiles = {
        "smith": count_profile(smith),
        "image": count_profile(degree for degree, _component in image),
        "kernel": count_profile(degree for degree, _component in kernel),
        "prefix": prefix,
    }
    assert profiles == EXPECTED[name], (name, profiles)
    matrix_hash = hashlib.sha256(json.dumps(
        matrix_payload(row_types, columns), separators=(",", ":")
    ).encode()).hexdigest()
    result = {
        "subset": name,
        "families": tuple(
            O.weighted_order_four_families(literal)[index][0]
            for index in indices
        ),
        "polynomial_matrix_shape": (len(row_types), len(columns)),
        "matrix_sha256": matrix_hash,
        "raw_smith_Z_valuation_multiplicities": profiles["smith"],
        "normalized_smith_delays_after_common_Z3": tuple(
            (degree - 3, multiplicity)
            for degree, multiplicity in profiles["smith"]
        ),
        "image_popov_degree_multiplicities": profiles["image"],
        "right_kernel_minimal_index_multiplicities": profiles["kernel"],
        "complete_prefix_ranks_K1_through_K5": prefix,
        "eventual_rank_increment": len(smith),
    }
    if name == "eleven":
        pivot_rows = tuple(
            (row_types[component - 1], degree)
            for degree, component in image
        )
        assert len(set(pivot_rows)) == len(pivot_rows) == 22
        result["image_popov_pivot_row_type_and_seed"] = pivot_rows
        result["nonoverlapping_pivot_rows_for_2621_shifts"] = 22 * 2621
        result["steady_state_starts_after_prefix_layers"] = 2
        result["steady_state_boundary_excess"] = prefix[1] - 2 * 22
    return result


def multiplicity_discriminator(literal):
    """Raw complete-contact rank is not the rank-22 m=4 profile at m>4."""
    receipts = []
    for m in (4, 5, 6, 8):
        _row_types, columns, _labels = matrix_data(
            literal, 7, CHAMBERS[0][0][0], CHAMBERS[0][1][0], ELEVEN,
            m=m, v_prefactor=m - 4)
        first_four = prefix_ranks(columns, 4)
        receipts.append({
            "multiplicity": m,
            "complete_prefix_ranks_K1_through_K4": first_four,
            "one_layer_columns": len(columns),
            "one_layer_is_injective": first_four[0] == len(columns),
        })
    assert tuple(r["complete_prefix_ranks_K1_through_K4"]
                 for r in receipts) == (
        (33, 65, 87, 109),
        (33, 66, 99, 128),
        (33, 66, 99, 132),
        (33, 66, 99, 132),
    )
    return tuple(receipts)


def main():
    M.PRIME = M.T.PRIME = M.F.PRIME = O.T.PRIME = O.F.PRIME = F.PRIME = P
    chambers = []
    first_literal = None
    for offsets, deltas in CHAMBERS:
        literal = M.build_case(
            "order4_banded_smith", O.CASE, 7, 7, 4,
            error_direction_offsets=offsets)
        if first_literal is None:
            first_literal = literal
        nodes = []
        for node, offset, delta in zip(range(7, 10), offsets, deltas):
            nodes.append({
                "node_offset_delta": (node, offset, delta),
                "subsets": tuple(
                    one_subset(literal, node, offset, delta, name, indices)
                    for name, indices in SUBSETS
                ),
            })
        chambers.append({"offsets": offsets, "deltas": deltas,
                         "nodes": tuple(nodes)})
    assert first_literal is not None
    payload = {
        "scope": (
            "exact m=4 one-node F101[Z] Smith/Popov/kernel audit; "
            "Full187 requires a separate lower-grade quotient theorem"
        ),
        "field": P,
        "case": O.CASE,
        "chambers": tuple(chambers),
        "multiplicity_discriminator": multiplicity_discriminator(
            first_literal),
        "verdict": (
            "the eight-carrier scalar-state claim is false (polynomial "
            "rank 15); the complete order-four module has an exact "
            "22-channel m=4 banded state with memory two and 21 startup "
            "modes, but its raw rank-22 profile does not persist to m>=5"
        ),
        "honest_remaining_gate": (
            "compute/prove the complete order-four module after quotienting "
            "by grades at most 82; only that quotient can justify using the "
            "m=4 22-channel state in the Full187 seed trellis"
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(
        canonical.encode()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
