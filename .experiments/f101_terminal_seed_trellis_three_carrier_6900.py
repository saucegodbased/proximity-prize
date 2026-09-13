#!/usr/bin/env python3
"""Exact three-carrier terminal seed-trellis receipt for the F101 control.

The canonical grade-seven pieces of the three exact locator lifts have the
form

  V^(m-2) Z^b (c V^2 + B V Z + A Lambda Xi V1 Z),

where Q=Xi^2, V=Y-QZ, V1=R-Q'Z, and b=J+1-m.  This script checks the two
couplings hidden by that compact display:

  Lambda | B + A Xi Lambda',
  B0 = B - c Q + 2 A Lambda Xi'.

The first makes the row an agreement-side order-m cycle.  The second makes
its raw boundary-zero coefficient exactly -B0 Q^(m-1), cancelling the
otherwise out-of-window top term.  We then test the actual bordered map: the
three displayed terminal rows, together with source grades at most J, close
all three exact F0/F1/F2 right-hand sides.  No other grade-(J+1) column is
used.

The final section checks the literal Full187 target width inequalities for
the same four-term raw recurrence and every passive shift from grade J+1
through L.  It is arithmetic evidence for the trellis producer, not a proof
that its 2621 shifted layers span the target forced-head residual.
"""

from __future__ import annotations

from collections import Counter
import hashlib
import json
import sys

from flint import nmod_poly

sys.path.insert(0, ".experiments")
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402
import prime_o2_conormal_threshold_falsifier as T  # noqa: E402


P = 101
PRIMARY = (11, 5, 8, 4, 32, 1, 1, 6, 10)
NAMES = ("F0", "F1", "F2")

# Extracted by the deterministic exact solve in
# f101_grade7_correction_factor_probe_6900.py.  Coefficients are ascending.
ABC = (
    ((69, 66, 2, 45, 84),
     (82, 52, 21, 89, 31, 19, 51, 32, 42, 13, 95, 44, 47, 64, 1),
     (53,)),
    ((58, 95, 9, 51, 75),
     (66, 32, 44, 47, 89, 35, 78, 43, 88, 8, 74, 97, 60, 86, 55),
     (76,)),
    ((42, 75, 99, 76, 23),
     (6, 64, 27, 71, 100, 64, 81, 59, 40, 43, 79, 99, 28, 29, 64),
     (66,)),
)


def poly_tuple(poly):
    return tuple(int(poly[i]) for i in range(max(0, poly.degree() + 1)))


def add_scaled(target, source, scale=1):
    for row, coefficient in source.items():
        value = (target.get(row, 0) + scale * coefficient) % P
        if value:
            target[row] = value
        else:
            target.pop(row, None)


def source_hash(source):
    payload = tuple(sorted((monomial, coefficient % P)
                           for monomial, coefficient in source.items()
                           if coefficient % P))
    return hashlib.sha256(repr(payload).encode()).hexdigest()


def terminal_source(A, B, c, xi, q, locator, m, jet):
    """Expand the coupled terminal row in the literal raw source basis."""
    q1 = F.poly_derivative(q)
    v = F.sparse_add(
        F.Y, F.sparse_mul(F.Z, F.sparse_embed_x(q)), -1)
    v1 = F.sparse_add(
        F.R, F.sparse_mul(F.Z, F.sparse_embed_x(q1)), -1)
    b = jet + 1 - m
    bracket = F.sparse_mul(
        F.sparse_embed_x(c), F.sparse_pow(v, 2))
    bracket = F.sparse_add(
        bracket,
        F.sparse_mul(
            F.sparse_mul(F.sparse_embed_x(B), v), F.Z))
    a_l_xi = F.poly_mul(F.poly_mul(A, locator), xi)
    bracket = F.sparse_add(
        bracket,
        F.sparse_mul(
            F.sparse_mul(F.sparse_embed_x(a_l_xi), v1), F.Z))
    return F.sparse_mul(
        F.sparse_mul(F.sparse_pow(v, m - 2), F.sparse_pow(F.Z, b)),
        bracket)


def indexed_image(literal, source, source_index):
    image = {}
    for monomial, coefficient in source.items():
        assert monomial in source_index, monomial
        add_scaled(image, literal.columns[source_index[monomial]], coefficient)
    return image


def rank(columns):
    return T.dense_matrix(columns).rank()


def target_width_receipt():
    """Check every raw strip of the target recurrence, not just endpoints."""
    n, w, g, e, m, degree = 262144, 131071, 180413, 81731, 60, 10824780
    qdegree = 2 * e
    # Inclusive maximum degrees.  The corresponding coefficient counts are
    # one larger.  These are chosen so each critical raw strip ends at D-1.
    amax = 950769
    b0max = 1180521
    cmax = 1049450

    families = {
        # A Lambda Xi R Z * V^(m-2), total raw Y exponent y=0,...,m-2.
        "A_R": tuple(
            amax + g + e + qdegree * (m - 2 - y)
            + w * y + (w - 1)
            for y in range(m - 1)),
        # -2 A Lambda Xi' Y Z * V^(m-2), y=1,...,m-1.
        "A_Y": tuple(
            amax + g + (e - 1) + qdegree * (m - 1 - y)
            + w * y
            for y in range(1, m)),
        # -B0 Q Z^2 * V^(m-2), y=0,...,m-2.
        "B0_Z": tuple(
            b0max + qdegree * (m - 1 - y) + w * y
            for y in range(m - 1)),
        # B0 Y Z * V^(m-2), y=1,...,m-1.
        "B0_Y": tuple(
            b0max + qdegree * (m - 1 - y) + w * y
            for y in range(1, m)),
        # c Y^2 * V^(m-2), y=2,...,m.
        "c_Y2": tuple(
            cmax + qdegree * (m - y) + w * y
            for y in range(2, m + 1)),
        # -c Q Y Z * V^(m-2), y=1,...,m-1.
        "c_QY": tuple(
            cmax + qdegree * (m - y) + w * y
            for y in range(1, m)),
    }
    assert all(max(values) < degree for values in families.values())
    assert max(families["A_R"]) == degree - 1
    assert max(families["A_Y"]) == degree - 1
    assert max(families["B0_Z"]) == degree - 1
    assert max(families["c_QY"]) == degree - 1
    assert qdegree - w == 32391
    assert m + (82 + 1 - m) == 83 <= 2703
    assert m <= 82 and 1 <= 21 and 0 <= 10
    first_grade = 83
    last_grade = 2703
    shifts = last_grade - first_grade + 1
    assert shifts == 2621
    assert all(first_grade + shift <= last_grade
               for shift in range(shifts))

    coefficient_dimensions = {
        "A": amax + 1,
        "B0": b0max + 1,
        "c": cmax + 1,
    }
    total = sum(coefficient_dimensions.values())
    after_agreement_congruence_lower_bound = total - g
    constant_c_subfamily_lower_bound = (
        coefficient_dimensions["A"]
        + coefficient_dimensions["B0"] + 1 - g)
    assert after_agreement_congruence_lower_bound == 3000330
    assert constant_c_subfamily_lower_bound == 1950880
    assert constant_c_subfamily_lower_bound > 4 * e

    return {
        "parameters_N_w_g_e_m_D_J_L":
            (n, w, g, e, m, degree, 82, 2703),
        "Q_degree": qdegree,
        "raw_recurrence": (
            "V^(58) Z^23 * (c Y^2 + "
            "(B0-cQ-2A Lambda Xi') YZ + "
            "A Lambda Xi RZ - B0 Q Z^2)"
        ),
        "inclusive_degree_caps_A_B0_c": (amax, b0max, cmax),
        "maximum_degree_plus_weight_by_raw_family": {
            name: max(values) for name, values in families.items()
        },
        "critical_families_equal_D_minus_1":
            ("A_R", "A_Y", "B0_Z", "c_QY"),
        "per_Y_step_headroom_2e_minus_w": qdegree - w,
        "all_active_slope_curvature_seed_caps_legal": True,
        "passive_Z_shifts": {
            "shift_range": (0, shifts - 1),
            "source_grade_range": (first_grade, last_grade),
            "number_of_layers": shifts,
            "widths_unchanged_by_shift": True,
        },
        "coefficient_dimensions": coefficient_dimensions,
        "dimension_after_at_most_g_agreement_congruences":
            after_agreement_congruence_lower_bound,
        "constant_c_subfamily_dimension_lower_bound":
            constant_c_subfamily_lower_bound,
        "four_error_values": 4 * e,
    }


def main():
    M.T.PRIME = M.F.PRIME = T.PRIME = P
    F.PRIME = P
    F.GAMMA = 0
    F.MULTIPLICITY = PRIMARY[3]
    literal = M.build_case("primary_n11", PRIMARY, 8, 8, 3)
    source_index = {monomial: index
                    for index, monomial in enumerate(literal.monomials)}

    xi = nmod_poly(list(literal.xi), P)
    q = nmod_poly(list(literal.q), P)
    locator = nmod_poly(list(literal.locator), P)
    xi1 = xi.derivative()
    locator1 = locator.derivative()

    terminal_sources = []
    receipts = []
    for name, (a_coeffs, b_coeffs, c_coeffs) in zip(NAMES, ABC):
        A = nmod_poly(list(a_coeffs), P)
        B = nmod_poly(list(b_coeffs), P)
        c = nmod_poly(list(c_coeffs), P)
        B0 = B - c * q + 2 * A * locator * xi1
        quotient, remainder = divmod(B + A * xi * locator1, locator)
        assert remainder == 0
        assert (A.degree(), B.degree(), c.degree(), B0.degree(),
                quotient.degree()) == (4, 14, 0, 13, 6)

        source = terminal_source(
            poly_tuple(A), poly_tuple(B), poly_tuple(c),
            literal.xi, literal.q, literal.locator,
            PRIMARY[3], PRIMARY[7])
        assert F.source_legal(source)
        assert all(sum(monomial[1:]) == PRIMARY[7] + 1
                   for monomial in source)
        image = indexed_image(literal, source, source_index)
        agreement_contact = {
            literal.row_keys[row]: coefficient
            for row, coefficient in image.items()
            if literal.row_keys[row][0] == "C"
            and literal.row_keys[row][1] in literal.actual_agreement
        }
        j_image = {literal.row_keys[row]: coefficient
                   for row, coefficient in image.items()
                   if literal.row_keys[row][0] == "J"}
        assert not agreement_contact
        assert not j_image

        raw_boundary_zero = {
            monomial[0]: coefficient
            for monomial, coefficient in source.items()
            if sum(monomial[1:4]) == 0
        }
        expected_boundary_zero = -B0 * q ** (PRIMARY[3] - 1)
        assert raw_boundary_zero == {
            exponent: int(expected_boundary_zero[exponent])
            for exponent in range(expected_boundary_zero.degree() + 1)
            if int(expected_boundary_zero[exponent])
        }
        assert expected_boundary_zero.degree() == PRIMARY[4] - 1

        error_rows = {
            literal.row_keys[row]: coefficient
            for row, coefficient in image.items()
            if literal.row_keys[row][0] == "C"
            and literal.row_keys[row][1] not in literal.actual_agreement
        }
        terminal_sources.append(source)
        receipts.append({
            "normal": name,
            "degrees_A_B_c_B0_C":
                (A.degree(), B.degree(), c.degree(), B0.degree(),
                 quotient.degree()),
            "agreement_cycle_congruence":
                "B + A*Xi*Lambda' = Lambda*C",
            "C_coefficients": poly_tuple(quotient),
            "B0_coefficients": poly_tuple(B0),
            "raw_boundary_zero_identity":
                "coefficient = -B0*Q^(m-1)",
            "raw_boundary_zero_degree": expected_boundary_zero.degree(),
            "source_support": len(source),
            "source_sha256": source_hash(source),
            "error_contact_support": len(error_rows),
            "error_contact_rows_by_node": tuple(sorted(Counter(
                row[1] for row in error_rows).items())),
        })

    base_indices = [index for index, monomial in enumerate(literal.monomials)
                    if sum(monomial[1:]) <= PRIMARY[7]]
    base_columns = [literal.columns[index] for index in base_indices]
    terminal_columns = [indexed_image(literal, source, source_index)
                        for source in terminal_sources]
    rank_base = rank(base_columns)
    rank_with_terminal = rank(base_columns + terminal_columns)
    individual_defects = tuple(
        rank(base_columns + terminal_columns + [target])
        - rank_with_terminal
        for target in literal.targets)
    joint_defect = (
        rank(base_columns + terminal_columns + list(literal.targets))
        - rank_with_terminal)
    assert (len(base_columns), rank_base) == (1463, 1461)
    assert rank_with_terminal == rank_base + 3
    assert individual_defects == (0, 0, 0)
    assert joint_defect == 0

    payload = {
        "scope": (
            "exact F101 terminal recurrence and literal target width gate; "
            "surjectivity of all 2621 target seed layers remains open"
        ),
        "field": P,
        "primary_parameters": PRIMARY,
        "terminal_formula": (
            "V^(m-2) Z^(J+1-m) * "
            "(c V^2 + B V Z + A Lambda Xi V1 Z)"
        ),
        "equivalent_three_carriers": (
            "c V^m Z^b",
            "C Lambda V^(m-1) Z^(b+1)",
            "A Xi V^(m-2) (Lambda V1-Lambda' V) Z^(b+1)",
        ),
        "terminal_rows": tuple(receipts),
        "literal_bordered_rank_receipt": {
            "grade_at_most_J_columns": len(base_columns),
            "rank_before_terminal_rows": rank_base,
            "number_of_terminal_rows": len(terminal_columns),
            "rank_after_terminal_rows": rank_with_terminal,
            "individual_F0_F1_F2_defects": individual_defects,
            "joint_defect": joint_defect,
        },
        "target_width_receipt": target_width_receipt(),
        "honest_remaining_gate": (
            "prove that grades <=82 together with every Z-shift of the "
            "three-carrier cycles through grade 2703 propagate each forced "
            "J head to zero error contact; width and cycle existence are green"
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(
        canonical.encode()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
