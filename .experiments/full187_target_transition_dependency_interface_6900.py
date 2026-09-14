#!/usr/bin/env python3
"""Exact target-side transition interface for the lower-6900 Full187 shell.

This is deliberately a compressed symbolic graph, not a finite-position rank
test.  It uses the literal passive/contact expansion

  Y^y R^r S^s Z^z
    -> u0^(y-f-h) u1^h Z^(z+h)
       (E + T R - T^2 S/2)^f R^r S^s

and the actual target constants.  A contact summand with ``aE`` copies of E,
``cS`` copies of ``-T^2 S/2``, and coefficient-Hasse order ``q`` has

  (T,E,R,S,Z) =
    (q+f-aE+cS, aE, f-aE-cS+r, s+cS, z+h)

and survives iff ``q + f + 2*aE + cS < m``.

The executable records physical source X widths and seed intervals, checks
the exact raw-diagonal inverse when it exists, and classifies the terminal
Hermite frontier.  It also tests the exact leading-pivot inequalities of the
existing ``Order2SourceBasisScaffold`` on every structured terminal row.
It does not turn support reachability into containment: the local pivots
still need a bounded global confluence/transpose theorem, and agreement-side
Hermite capacity is not error-side correction capacity.
"""

from __future__ import annotations

from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path


N = 262_144
W = 131_071
G = 180_413
ERRORS = N - G
M = 60
D = M * G
ACTIVE_CAP = 82
SLOPE_CAP = 21
CURVATURE_CAP = 10
SEED_CAP = 2703


def source_width(y: int, r: int, s: int) -> int:
    """Literal half-open X-coefficient interval has length this number."""
    return D - W * y - (W - 1) * r - (W - 2) * s


def source_cell_legal(y: int, r: int, s: int, z: int = 0) -> bool:
    return (
        min(y, r, s, z) >= 0
        and y + r + s <= ACTIVE_CAP
        and r + s <= SLOPE_CAP
        and s <= CURVATURE_CAP
        and z + y + r + s <= SEED_CAP
        and source_width(y, r, s) > 0
    )


def contact_weight(f: int, a_e: int, c_s: int, q: int = 0) -> int:
    return q + f + 2 * a_e + c_s


def ceil_div(a: int, b: int) -> int:
    assert a >= 0 and b > 0
    return (a + b - 1) // b


def contact_row(y: int, r: int, s: int, z: int,
                f: int, h: int, a_e: int, c_s: int, q: int = 0):
    """Literal row, with all syntactic and truncation guards checked."""
    assert 0 <= f <= y
    assert 0 <= h <= y - f
    assert 0 <= a_e and 0 <= c_s and a_e + c_s <= f
    assert contact_weight(f, a_e, c_s, q) < M
    return {
        "T": q + f - a_e + c_s,
        "E": a_e,
        "R": f - a_e - c_s + r,
        "S": s + c_s,
        "Z": z + h,
    }


def raw_diagonal_predecessor(y: int, r: int, s: int, z: int,
                             f: int, h: int, a_e: int, c_s: int,
                             q: int = 0):
    """Invert one Hasse row against a raw unit diagonal, when that is legal.

    The q=0 specialization is the whole-polynomial/basic transition used by
    the compressed graph.  Keeping q in this checker prevents the former
    mistake of drawing an edge which is killed by contact truncation.
    """
    row = contact_row(y, r, s, z, f, h, a_e, c_s, q)
    if a_e != 0:
        return None
    y2 = row["T"]
    r2 = row["R"] - row["T"]
    s2 = row["S"]
    z2 = row["Z"]
    if r2 < 0 or not source_cell_legal(y2, r2, s2, z2):
        return None
    return y2, r2, s2, z2


def derivative_pairs():
    return tuple(
        (r, s)
        for s in range(CURVATURE_CAP + 1)
        for r in range(SLOPE_CAP - s + 1)
    )


def source_census(pairs):
    active_cells = 0
    coefficient_blocks = 0
    columns = 0
    min_width = None
    min_width_cell = None
    for r, s in pairs:
        for y in range(ACTIVE_CAP - r - s + 1):
            width = source_width(y, r, s)
            assert width > 0
            z_count = SEED_CAP - y - r - s + 1
            active_cells += 1
            coefficient_blocks += z_count
            columns += z_count * width
            if min_width is None or width < min_width:
                min_width = width
                min_width_cell = (y, r, s)
    assert active_cells == 13_145
    assert coefficient_blocks == 34_924_329
    assert columns == 162_963_415_163_901
    assert (min_width, min_width_cell) == (76_958, (82, 0, 0))
    return {
        "derivative_pairs": len(pairs),
        "active_y_r_s_cells": active_cells,
        "seeded_coefficient_blocks": coefficient_blocks,
        "literal_source_columns": columns,
        "minimum_width_and_cell_y_r_s": (min_width, min_width_cell),
    }


def structured_heads():
    """Degree/interval receipt for the actual locator-normal packets.

    The displayed Y/R/S coefficients are the three compressed heads.  In
    centered coordinates V0=Y-P-(Z-gamma)Q and similarly for R,S, each packet
    also contains a scalar and Z tail.  With deg Q<=g-1 those tails have the
    listed sharp upper bounds and cannot be discarded on agreement nodes.
    """
    rows = (
        ("F0.Y", (1, 0, 0, 0), 59 * G, 59,
         "Lambda^59"),
        ("F1.Y", (1, 0, 0, 0), 59 * G - 1, 58,
         "-Lambda^58*Lambda'"),
        ("F1.R", (0, 1, 0, 0), 59 * G, 59,
         "Lambda^59"),
        ("F2.Y", (1, 0, 0, 0), 59 * G - 2, 57,
         "Lambda^57*(2*(Lambda')^2-Lambda*Lambda'')"),
        ("F2.R", (0, 1, 0, 0), 59 * G - 1, 58,
         "-2*Lambda^58*Lambda'"),
        ("F2.S", (0, 0, 1, 0), 59 * G, 59,
         "Lambda^59"),
    )
    out = []
    for name, (y, r, s, z), degree_bound, locator_order, formula in rows:
        width = source_width(y, r, s)
        assert source_cell_legal(y, r, s, z)
        assert degree_bound < width
        out.append({
            "name": name,
            "raw_cell_y_r_s_z": (y, r, s, z),
            "coefficient": formula,
            "degree_upper_bound": degree_bound,
            "locator_root_order_lower_bound": locator_order,
            "physical_X_interval": (0, width),
            "slack_below_max_allowed_degree": width - 1 - degree_bound,
            "physical_seed_interval": (0, SEED_CAP - y - r - s),
        })
    assert tuple(row["slack_below_max_allowed_degree"] for row in out) == (
        49_341, 49_342, 49_342, 49_343, 49_343, 49_343)

    tails = (
        ("F0.scalar/Z tail", D - 1, 0),
        ("F1.scalar/Z tail", D - 2, 1),
        ("F2.scalar/Z tail", D - 3, 2),
    )
    tail_rows = []
    for name, degree_bound, slack in tails:
        assert degree_bound < source_width(0, 0, 0)
        assert source_width(0, 0, 0) - 1 - degree_bound == slack
        tail_rows.append({
            "name": name,
            "degree_upper_bound": degree_bound,
            "scalar_or_Z_physical_X_interval": (0, D),
            "slack_below_max_allowed_degree": slack,
            "warning": "packet tail is required for agreement cancellation",
        })
    return {
        "centered_packet_formulas": (
            "F0=Lambda^59*V0",
            "F1=Lambda^59*V1-Lambda^58*Lambda'*V0",
            "F2=Lambda^57*((2Lambda'^2-Lambda Lambda'')*V0"
            "-2Lambda Lambda'*V1+Lambda^2*V2)",
            "Vj=(Y,R,S)_j-(P,Q derivatives)_j-(Z-gamma)*Q^[j]",
        ),
        "YRS_heads": tuple(out),
        "forced_scalar_and_Z_tails": tuple(tail_rows),
        "Z1_impulse": {
            "raw_cell_y_r_s_z": (0, 0, 0, 1),
            "coefficient_degree": 0,
            "physical_X_interval": (0, D),
            "physical_seed_interval": (0, SEED_CAP),
        },
    }


def raw_diagonal_projected_graph(pairs):
    """q=0 shape graph for the exact basic/second-jet raw inverse."""
    adjacency = defaultdict(set)
    edge_records = []
    for r, s in pairs:
        for c_s in range(min(r // 2, CURVATURE_CAP - s) + 1):
            # A universal low-active witness: y=f=cS, h=aE=q=0.
            f = c_s
            y = c_s
            assert contact_weight(f, 0, c_s, 0) == 2 * c_s < M
            predecessor = raw_diagonal_predecessor(
                y, r, s, 0, f, 0, 0, c_s, 0)
            assert predecessor is not None
            y2, r2, s2, z2 = predecessor
            assert (y2, r2, s2, z2) == (
                2 * c_s, r - 2 * c_s, s + c_s, 0)
            source_charge_without_y = (
                W * f + (W - 1) * r + (W - 2) * s)
            predecessor_charge = (
                W * y2 + (W - 1) * r2 + (W - 2) * s2)
            assert predecessor_charge == source_charge_without_y
            adjacency[(r, s)].add((r2, s2))
            edge_records.append(((r, s), (r2, s2), c_s))

    strict_edges = tuple(
        (u, v, c_s) for u, v, c_s in edge_records if u != v)
    assert len(edge_records) == 792
    assert len(strict_edges) == 605

    undirected = defaultdict(set)
    for u, v, _ in strict_edges:
        undirected[u].add(v)
        undirected[v].add(u)
    seen = set()
    components = []
    for vertex in pairs:
        if vertex in seen:
            continue
        stack = [vertex]
        seen.add(vertex)
        component = []
        while stack:
            current = stack.pop()
            component.append(current)
            for nxt in undirected[current]:
                if nxt not in seen:
                    seen.add(nxt)
                    stack.append(nxt)
        invariant_values = {r + 2 * s for r, s in component}
        assert len(invariant_values) == 1
        components.append((next(iter(invariant_values)), len(component)))
    assert len(components) == 32
    assert sum(size for _, size in components) == 187

    head_pairs = {(0, 0), (1, 0), (0, 1)}
    head_components = {
        pair for pair in pairs if pair[0] + 2 * pair[1] in (0, 1, 2)
    }
    assert head_components == {(0, 0), (1, 0), (2, 0), (0, 1)}
    return {
        "q0_projected_edge_count_including_self": len(edge_records),
        "q0_projected_strict_edge_count": len(strict_edges),
        "conserved_shape_charge": "r+2s",
        "undirected_component_count": len(components),
        "component_sizes_by_r_plus_2s": tuple(sorted(components)),
        "structured_head_pairs": tuple(sorted(head_pairs)),
        "q0_raw_diagonal_component_union_of_heads":
            tuple(sorted(head_components)),
        "scope_warning": (
            "This 4-of-187 cut is NOT a Full187 cut: positive coefficient-"
            "Hasse order q changes the projected charge by q, while E-positive "
            "basis packets can couple additional rows."
        ),
    }


def terminal_transition_census(pairs):
    """Classify every surviving q=0 PC/contact choice on active grade 82.

    These are the worst coefficient-Hasse layers for the scalar Hermite
    budget: positive q raises contact weight and lowers the required locator
    depth.  The counts here are therefore not counts of all literal q rows.
    """
    counts = Counter()
    unresolved_types = set()
    unresolved_f_extra_types = set()
    unresolved_extra_charge = Counter()
    projected_edges = set()
    minimum_lower_width = None
    minimum_lower_witness = None
    minimum_hermite_margin = None
    minimum_hermite_witness = None

    for r, s in pairs:
        y = ACTIVE_CAP - r - s
        assert 61 <= y <= 82
        top_width = source_width(y, r, s)
        assert top_width == D - W * ACTIVE_CAP + r + 2 * s
        for f in range(M):
            h = y - f
            assert h >= 2
            lower_width = source_width(f, r, s)
            for a_e in range(f + 1):
                for c_s in range(f - a_e + 1):
                    weight = contact_weight(f, a_e, c_s)
                    if weight >= M:
                        continue
                    depth = M - weight
                    margin = lower_width - G * depth
                    status = "unconditional_Hermite" if margin >= 0 \
                        else "structured_residue"
                    if a_e > 0:
                        inverse_class = "E-positive"
                    elif 2 * c_s > r:
                        inverse_class = "R-short"
                    elif s + c_s > CURVATURE_CAP:
                        inverse_class = "curvature-escape"
                    else:
                        inverse_class = "raw-diagonal"
                        pred = raw_diagonal_predecessor(
                            y, r, s, 0, f, h, 0, c_s, 0)
                        assert pred is not None
                        y2, r2, s2, z2 = pred
                        assert (y2, r2, s2, z2) == (
                            f + c_s, r - 2 * c_s, s + c_s, h)
                        # Exact cancellation of the cS weighted charge.
                        assert source_width(y2, r2, s2) == lower_width
                        assert z2 + y2 + r2 + s2 == ACTIVE_CAP
                        projected_edges.add(((r, s), (r2, s2), c_s))
                    counts[(status, inverse_class)] += 1
                    if status == "structured_residue":
                        unresolved_types.add((f, a_e, c_s))
                        unresolved_f_extra_types.add((f, 2 * a_e + c_s))
                        unresolved_extra_charge[2 * a_e + c_s] += 1
                    if (minimum_lower_width is None
                            or lower_width < minimum_lower_width):
                        minimum_lower_width = lower_width
                        minimum_lower_witness = (
                            r, s, y, f, a_e, c_s, h)
                    if (minimum_hermite_margin is None
                            or margin < minimum_hermite_margin):
                        minimum_hermite_margin = margin
                        minimum_hermite_witness = (
                            r, s, f, a_e, c_s, h, margin)

    total = sum(counts.values())
    unconditional = sum(value for (status, _), value in counts.items()
                        if status == "unconditional_Hermite")
    structured = total - unconditional
    assert (total, unconditional, structured) == (
        1_266_925, 1_194_075, 72_850)
    assert len(unresolved_types) == 1_056
    assert len(unresolved_f_extra_types) == 406
    assert max(unresolved_extra_charge) == 13
    assert (minimum_hermite_margin, minimum_hermite_witness) == (
        -2_752_470, (21, 0, 0, 0, 0, 61, -2_752_470))
    assert minimum_lower_width == 339_121
    assert minimum_lower_width > N

    # Regression: the old f=81,h=1 term is syntactically a PC summand but is
    # absent from the order-60 contact quotient, even at q=aE=cS=0.
    old_edge_weight = contact_weight(81, 0, 0, 0)
    assert old_edge_weight == 81 and not old_edge_weight < M

    # Exact surviving top-pure endpoint.
    top_pure = {
        "source_y_r_s_z": (82, 0, 0, 0),
        "largest_surviving_raw_diagonal_f_h_aE_cS_q": (59, 23, 0, 0, 0),
        "predecessor_y_r_s_z": (59, 0, 0, 23),
        "predecessor_width": source_width(59, 0, 0),
        "width_minus_all_nodes": source_width(59, 0, 0) - N,
        "seed_cap_slack": SEED_CAP - (59 + 23),
    }
    assert top_pure["predecessor_width"] == 3_091_591
    assert top_pure["width_minus_all_nodes"] == 2_829_447

    # The apparent one-degree product-form frontier.  Because these terms
    # have contact depth one and predecessor width>N, direct value
    # interpolation is green; only the unreduced product U*p misses.
    product_frontier = []
    for s in range(CURVATURE_CAP + 1):
        r = SLOPE_CAP - s
        y = ACTIVE_CAP - r - s
        assert y == 61
        f, h = 59, 2
        top = source_width(y, r, s)
        predecessor = source_width(f, r, s)
        unreduced_max_degree = (top - 1) + (N - 1)
        assert predecessor == top + 2 * W
        assert unreduced_max_degree == predecessor
        assert contact_weight(f, 0, 0) == 59
        assert predecessor > N
        product_frontier.append({
            "r_s": (r, s),
            "source_y_f_h": (y, f, h),
            "top_width": top,
            "predecessor_width": predecessor,
            "unreduced_product_max_degree": unreduced_max_degree,
            "strict_width_miss": 1,
            "contact_depth": 1,
            "direct_all_node_value_interpolation_fits": True,
        })
    assert len(product_frontier) == 11

    return {
        "terminal_source_seed_interval": (0, SEED_CAP - ACTIVE_CAP),
        "terminal_top_width_interval": (
            min(source_width(ACTIVE_CAP - r - s, r, s)
                for r, s in pairs),
            max(source_width(ACTIVE_CAP - r - s, r, s)
                for r, s in pairs),
        ),
        "choice_counts_by_Hermite_status_and_inverse_class": tuple(
            (status, inverse_class, value)
            for (status, inverse_class), value in sorted(counts.items())
        ),
        "contact_choice_totals": {
            "scope": (
                "q=0 leading coefficient-Hasse choices; q>0 is easier for "
                "the scalar agreement-Hermite budget but is not counted"
            ),
            "surviving_q0_f_aE_cS_choices": total,
            "unconditional_agreement_Hermite": unconditional,
            "structured_residue": structured,
            "structured_fraction": structured / total,
            "unique_structured_f_aE_cS_types": len(unresolved_types),
            "unique_structured_f_2aE_plus_cS_capacity_types":
                len(unresolved_f_extra_types),
            "structured_counts_by_extra_charge_2aE_plus_cS": tuple(
                sorted(unresolved_extra_charge.items())),
        },
        "raw_diagonal_terminal_projected_edges": len(projected_edges),
        "minimum_lower_width_witness_r_s_y_f_aE_cS_h":
            minimum_lower_witness,
        "minimum_lower_width": minimum_lower_width,
        "minimum_lower_width_minus_all_nodes": minimum_lower_width - N,
        "worst_Hermite_margin_witness_r_s_f_aE_cS_h_margin":
            minimum_hermite_witness,
        "old_Y82_to_Y81Z_edge": {
            "f_h_aE_cS_q": (81, 1, 0, 0, 0),
            "contact_weight": old_edge_weight,
            "survives_order_60": False,
        },
        "corrected_top_pure_edge": top_pure,
        "eleven_unreduced_product_only_frontiers": tuple(product_frontier),
    }


def structured_frontier_classification(pairs):
    """Reduce the low-contact agreement frontier using exact local pivots.

    For a terminal origin ``(r,s;f,aE,cS)`` its q=0 contact row is

      (T,E,R,S)=(f-aE+cS,aE,f-aE-cS+r,s+cS).

    The sharp basis in ``Order2SourceBasisScaffold`` can pivot this row with
    source indices

      d=E+R+S,
      a0 in [max(0,d-21), min(R,T-2*(E+S-10)_+)],
      qSource=d-a0, b=R-a0, e=E,
      k=T-a0-2*(E+S-10)_+.

    Every asserted edge below checks the contact survival inequality again,
    the derivative/curvature/active/passive caps, and its physical tapered
    multiplier width.  This is an associated-graded/local leading edge only;
    it is not the missing global confluence theorem.
    """
    capacity_counts = Counter()
    local_counts = Counter()
    local_deficit_histogram = Counter()
    structured_types = set()
    capacity_types = set()
    pivotable_states = set()
    corner_states = set()
    minimum_product_slack = None
    minimum_product_witness = None
    maximum_a_e = 0
    maximum_extra_charge = 0
    maximum_f_by_extra_charge = defaultdict(lambda: -1)

    for r, s in pairs:
        y = ACTIVE_CAP - r - s
        top_width = source_width(y, r, s)
        derivative_charge = (W - 1) * r + (W - 2) * s
        for f in range(M):
            h = y - f
            lower_width = source_width(f, r, s)
            for a_e in range(f + 1):
                for c_s in range(f - a_e + 1):
                    weight = contact_weight(f, a_e, c_s)
                    if weight >= M:
                        continue
                    depth = M - weight
                    agreement_margin = lower_width - G * depth
                    # An affine scalar CRT prescribing the complete
                    # agreement jet and one arbitrary value on every error
                    # needs G*depth+ERRORS coefficients.  This stronger test
                    # is not a claim about the coupled four-boundary map.
                    if agreement_margin < 0:
                        capacity = "structured_even_on_agreements"
                    elif agreement_margin < ERRORS:
                        capacity = "agreement_only_not_arbitrary_errors"
                    else:
                        capacity = "agreement_plus_arbitrary_error_values"
                    inverse_class = (
                        "E-positive" if a_e > 0 else
                        "R-short" if 2 * c_s > r else
                        "curvature-escape" if s + c_s > CURVATURE_CAP else
                        "raw-diagonal"
                    )
                    capacity_counts[(capacity, inverse_class)] += 1
                    if agreement_margin >= 0:
                        continue

                    extra_charge = 2 * a_e + c_s
                    structured_types.add((f, a_e, c_s))
                    capacity_types.add((f, extra_charge))
                    maximum_a_e = max(maximum_a_e, a_e)
                    maximum_extra_charge = max(
                        maximum_extra_charge, extra_charge)
                    maximum_f_by_extra_charge[extra_charge] = max(
                        maximum_f_by_extra_charge[extra_charge], f)

                    row = contact_row(
                        y, r, s, 0, f, h, a_e, c_s, q=0)
                    T, E, R, S = (
                        row["T"], row["E"], row["R"], row["S"])
                    assert T + 3 * E == weight < M
                    d = E + R + S
                    residual = max(E + S - CURVATURE_CAP, 0)
                    minimum_a0 = max(0, d - SLOPE_CAP)
                    maximum_a0 = min(R, T - 2 * residual)
                    state = (T, E, R, S, h)

                    if minimum_a0 <= maximum_a0:
                        a0 = minimum_a0
                        q_source = d - a0
                        b = R - a0
                        e = E
                        k = T - a0 - 2 * residual
                        assert 0 <= a0 <= R
                        assert 0 <= q_source <= SLOPE_CAP
                        assert 0 <= b <= q_source
                        assert e <= min(E + S, CURVATURE_CAP)
                        assert k >= 0
                        assert d <= ACTIVE_CAP
                        assert d + h == ACTIVE_CAP
                        # This is exactly the sharp leading contact weight of
                        # fullLayerPivot in Order2FullLayerLeading6900.
                        pivot_weight = k + a0 + 2 * residual + 3 * e
                        assert pivot_weight == T + 3 * E == weight < M

                        # sourceMultiplierBonus(E+S,10,b,e) is the exact
                        # external-X multiplier refund of the adapted basis.
                        bonus = b + 2 * (min(E + S, CURVATURE_CAP) - e)
                        multiplier_width = D - W * d + bonus
                        maximum_product_degree = (
                            (top_width - 1) + (N - 1))
                        assert maximum_product_degree < multiplier_width
                        product_slack = (
                            multiplier_width - 1 - maximum_product_degree)
                        if (minimum_product_slack is None or
                                product_slack < minimum_product_slack):
                            minimum_product_slack = product_slack
                            minimum_product_witness = (
                                r, s, f, a_e, c_s, h,
                                T, E, R, S, d, a0, q_source, b, e, k,
                                bonus, multiplier_width, product_slack)
                        pivotable_states.add(state)
                        local_counts[("sharp_local_basis_pivot", inverse_class)] += 1
                    else:
                        # In the structured chamber E<=6 and R never causes
                        # the failure.  The sole missing-pivot inequality is
                        # the displayed low-T corner cut.
                        assert a_e <= CURVATURE_CAP
                        assert R >= minimum_a0
                        assert T < minimum_a0 + 2 * residual
                        deficit = minimum_a0 + 2 * residual - T
                        assert 1 <= deficit <= 19
                        local_deficit_histogram[deficit] += 1
                        corner_states.add(state)
                        local_counts[("unpivoted_low_T_corner", inverse_class)] += 1

    total = sum(capacity_counts.values())
    agreement_only = sum(
        value for (capacity, _), value in capacity_counts.items()
        if capacity == "agreement_only_not_arbitrary_errors")
    arbitrary_errors = sum(
        value for (capacity, _), value in capacity_counts.items()
        if capacity == "agreement_plus_arbitrary_error_values")
    structured = sum(
        value for (capacity, _), value in capacity_counts.items()
        if capacity == "structured_even_on_agreements")
    pivotable = sum(
        value for (status, _), value in local_counts.items()
        if status == "sharp_local_basis_pivot")
    corner = sum(local_counts.values()) - pivotable

    assert (total, arbitrary_errors, agreement_only, structured) == (
        1_266_925, 1_186_372, 7_703, 72_850)
    assert (len(structured_types), len(capacity_types)) == (1_056, 406)
    assert (maximum_a_e, maximum_extra_charge) == (6, 13)
    assert dict(sorted(maximum_f_by_extra_charge.items())) == {
        0: 55, 1: 52, 2: 48, 3: 44, 4: 41, 5: 37, 6: 33,
        7: 30, 8: 26, 9: 22, 10: 19, 11: 15, 12: 11, 13: 8,
    }
    assert (pivotable, corner) == (57_512, 15_338)
    assert (len(pivotable_states), len(corner_states)) == (16_328, 7_726)
    assert minimum_product_slack == 524_283
    assert sum(local_deficit_histogram.values()) == corner
    assert dict(sorted(local_deficit_histogram.items())) == {
        1: 3606, 2: 2825, 3: 2094, 4: 1641, 5: 1246,
        6: 1002, 7: 773, 8: 613, 9: 474, 10: 352, 11: 250,
        12: 180, 13: 117, 14: 73, 15: 47, 16: 25, 17: 11,
        18: 7, 19: 2,
    }
    assert dict(local_counts) == {
        ("sharp_local_basis_pivot", "E-positive"): 28_599,
        ("sharp_local_basis_pivot", "R-short"): 3_873,
        ("sharp_local_basis_pivot", "curvature-escape"): 2_930,
        ("sharp_local_basis_pivot", "raw-diagonal"): 22_110,
        ("unpivoted_low_T_corner", "E-positive"): 13_413,
        ("unpivoted_low_T_corner", "R-short"): 1_120,
        ("unpivoted_low_T_corner", "curvature-escape"): 805,
    }

    return {
        "capacity_semantics": {
            "q_scope": (
                "q=0 is the worst scalar Hermite layer; these counts do "
                "not enumerate positive-q literal rows"
            ),
            "agreement_residue_condition":
                "width >= g*(60-contactWeight)",
            "agreement_and_arbitrary_error_values_condition":
                "width >= g*(60-contactWeight)+(n-g)",
            "warning": (
                "The 94.2499% agreement-residue count does not certify "
                "error correction or THREE-RHS containment."
            ),
            "counts_by_capacity_and_inverse_class": tuple(
                (capacity, inverse_class, value)
                for (capacity, inverse_class), value
                in sorted(capacity_counts.items())),
            "totals_surviving_arbitraryError_agreementOnly_structured":
                (total, arbitrary_errors, agreement_only, structured),
            "arbitrary_error_scalar_CRT_fraction": arbitrary_errors / total,
        },
        "structured_capacity_reduction": {
            "instances": structured,
            "unique_f_aE_cS_types": len(structured_types),
            "unique_f_extraCharge_types": len(capacity_types),
            "maximum_aE": maximum_a_e,
            "maximum_extraCharge_2aE_plus_cS": maximum_extra_charge,
            "maximum_f_by_extraCharge": tuple(
                sorted(maximum_f_by_extra_charge.items())),
        },
        "sharp_local_order2_basis_gate": {
            "contact_row": (
                "T=f-aE+cS", "E=aE", "R=f-aE-cS+r", "S=s+cS"),
            "pivot_interval_for_a0": (
                "max(0,E+R+S-21) <= a0 <= "
                "min(R,T-2*max(E+S-10,0))"
            ),
            "source_indices": (
                "d=E+R+S", "qSource=d-a0", "b=R-a0", "e=E",
                "k=T-a0-2*max(E+S-10,0)", "passiveSeed=h"),
            "survival_identity": (
                "k+a0+2*max(E+S-10,0)+3e="
                "T+3E=f+2aE+cS<60"
            ),
            "counts_by_status_and_origin_inverse_class": tuple(
                (status, inverse_class, value)
                for (status, inverse_class), value in sorted(local_counts.items())),
            "pivotable_instances_and_distinct_rows":
                (pivotable, len(pivotable_states)),
            "unpivoted_instances_and_distinct_rows":
                (corner, len(corner_states)),
            "unpivoted_exact_cut": (
                "T < max(0,E+R+S-21)+2*max(E+S-10,0)"
            ),
            "unpivoted_deficit_histogram": tuple(
                sorted(local_deficit_histogram.items())),
            "minimum_external_X_product_slack": minimum_product_slack,
            "minimum_slack_witness_r_s_f_aE_cS_h_T_E_R_S_d_a0_"
            "qSource_b_e_k_bonus_width_slack": minimum_product_witness,
            "scope_warning": (
                "A sharp local leading pivot only licenses a global "
                "triangular proof attempt; higher-contact tails, shared-X "
                "Hermite coupling, packet boundaries, and the four target "
                "residues remain to be oriented simultaneously."
            ),
        },
    }


def head_frontier_receipt():
    # F0's Y head contributes Lambda(a)^59*E at every error a.  Scalar/Z
    # packet tails cannot cancel an E-positive row, and a raw unit diagonal
    # always has E exponent zero.
    f0_e_weight = contact_weight(f=1, a_e=1, c_s=0, q=0)
    generic_width = source_width(1, 0, 0)
    hermite_depth = M - f0_e_weight
    hermite_margin = generic_width - G * hermite_depth
    assert f0_e_weight == 3 < M
    assert raw_diagonal_predecessor(1, 0, 0, 0, 1, 0, 1, 0, 0) is None
    assert hermite_margin == 410_168
    return {
        "F0_error_E_row": {
            "source_head": "Lambda^59*Y",
            "literal_choice_f_h_aE_cS_q": (1, 0, 1, 0, 0),
            "contact_row_T_E_R_S_Z": (0, 1, 0, 0, 0),
            "contact_weight": f0_e_weight,
            "coefficient_on_error_a": "Lambda(a)^59 != 0",
            "raw_diagonal_predecessor": None,
            "generic_layer_width": generic_width,
            "agreement_Hermite_depth": hermite_depth,
            "generic_Hermite_margin": hermite_margin,
        },
        "missing_typed_bridge": (
            "Promote the local order2Basis E-pivot to a globally bounded "
            "Full187 source packet with the exact tapered X interval, passive "
            "seed map, earlier-tail orientation, and controlled Y/R/S/Z "
            "boundary; local leading-term sharpness alone is insufficient."
        ),
    }


def main():
    pairs = derivative_pairs()
    assert len(pairs) == 187
    payload = {
        "scope": (
            "target-constant symbolic transition/interface audit; no tiny "
            "finite-position control, no rank inference, and no production "
            "or submission change"
        ),
        "target_N_w_g_e_m_D_J_slope_curvature_seed": (
            N, W, G, ERRORS, M, D, ACTIVE_CAP, SLOPE_CAP,
            CURVATURE_CAP, SEED_CAP),
        "literal_transition_rule": {
            "source": "X^a Y^y R^r S^s Z^z",
            "choices": "f<=y, h<=y-f, aE+cS<=f, q>=0",
            "row_T_E_R_S_Z": (
                "q+f-aE+cS", "aE", "f-aE-cS+r", "s+cS", "z+h"),
            "scalar": (
                "binom(y,f) binom(y-f,h) u0^(y-f-h) u1^h "
                "multinomial(f;aE,cS,f-aE-cS) (-1/2)^cS"
            ),
            "survival_inequality": "q+f+2*aE+cS < 60",
            "source_X_interval": (
                "0 <= a < 60g-wy-(w-1)r-(w-2)s"),
            "source_seed_interval": "0 <= z <= 2703-y-r-s",
            "output_seed_affine_map": "z_out=z+h",
            "raw_diagonal_inverse_when_q0": (
                "aE=0, 2cS<=r, s+cS<=10 => "
                "(y',r',s',z')=(f+cS,r-2cS,s+cS,z+h)"),
            "raw_diagonal_weight_identity_when_q0": (
                "w(f+cS)+(w-1)(r-2cS)+(w-2)(s+cS)="
                "wf+(w-1)r+(w-2)s"),
            "Hasse_q_generalization": (
                "(y',r',s')=(q+f+cS,r-q-2cS,s+cS), "
                "destination width loses exactly q while Hasse_q(p) loses q"
            ),
        },
        "source_census": source_census(pairs),
        "structured_locator_packets": structured_heads(),
        "q0_raw_diagonal_shape_graph": raw_diagonal_projected_graph(pairs),
        "terminal_transition_census": terminal_transition_census(pairs),
        "structured_frontier_classification":
            structured_frontier_classification(pairs),
        "structured_head_frontier": head_frontier_receipt(),
        "verdict": {
            "GREEN": (
                "All 187 terminal channels and their exact physical strips "
                "are enumerated.  Of the 72,850 choices which do not fit a "
                "complete agreement-Hermite representative, 57,512 have an "
                "exact sharp local order-two basis pivot with every cap, "
                "survival guard, and external-X product width checked."
            ),
            "STOP": (
                "The graph is not yet a Full187 residue pipeline: the local "
                "basis leaves 15,338 occurrences / 7,726 distinct low-T "
                "corner rows, and even its green pivots lack a simultaneous "
                "global tail orientation.  Also, 94.2499% is agreement-side "
                "capacity, not error correction or THREE-RHS containment."
            ),
            "retracted": (
                "Y^82 -> Y^81 Z is absent after order-60 truncation; the "
                "11 one-degree misses concern unreduced product-form "
                "transport only and disappear for the actual depth-one "
                "value solve."
            ),
        },
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
