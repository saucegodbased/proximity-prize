#!/usr/bin/env python3
"""Exact whole first-later-Z frontier gate behind the two P59 pivots.

Commit 91265f0 checked two principal aggregate rows and left the first
strictly-later passive layer open.  A P59 q=0 control has precisely three
live u0-free outputs on that next layer: its ordinary q=0 row, its induced
coefficient-Hasse q=1 row, and its first curvature row.  This executable
builds all six rows exported by P59^(10,10) and P59^(9,10), reconstructs
every physical same-key origin, and checks one simultaneous legal section.

The section uses, at each of the two passive grades, the actual jets

  X = H0(P58^(r,10)),  Y = H1(P57^(r+1,10)),  Z = H1(P58^(r,10)).

The X/Z pair has a legal two-jet Hermite section because width(P58)>2N.
The Y coordinate has a legal section Omega*V with H0=0 because
width(P57)>2N.  H2(P57), all higher jets, and all contributions from the
first grade into the second are retained as arbitrary linear K blocks.

This is a GREEN only for these six complete aggregate rows.  It proves an
acyclic filtration for every outgoing monomial, but it does not construct
the sections on every later filtration grade or close the Full187 packet.
"""

from __future__ import annotations

from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import resource
import sys


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import full187_complete_depth_pascal_hermite_slide_6900 as CD
import full187_cross_slope_second_fringe_confluence_6900 as C


P = 2_130_706_433
N = 262_144
M = 60
INV2 = pow(2, -1, P)

AUTHORITIES = {
    "full187_cross_slope_second_fringe_confluence_6900.py":
        "2cc322266c4428bd112384a59eaf5782ce5c97b5a0df720a0a3f418af4f4de29",
    "full187_complete_depth_pascal_hermite_slide_6900.py":
        "e6de6ca5273bcae6e369b7ffd779c815a393c6e7e3494ee8853f7c3ab1d46969",
}

EXPECTED_ALL_PROVENANCE_SHA256 = (
    "52522a3a514015d175deea51de3972de31a1541337e2092a86f38124a89f1347")
EXPECTED_DEPENDENCY_CONTRIBUTIONS_SHA256 = (
    "03346d0e58ab9399578e47ac8a5d84e16490b4a5c04a61916222f546dfbb7d70")

PIVOTS = (
    ("band1", 10, 10, C.L - 59 - 10 - 10),
    ("band2", 9, 10, C.L - 59 - 9 - 10),
)

ROW_ORDER = ("ordinary", "curvature", "jet")
NODE_ORDER = (
    "band1_x", "band1_y", "band1_z",
    "band2_x", "band2_y", "band2_z",
)


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def first_later_frontier(name: str, r: int, s: int, z: int):
    """Enumerate every live h=1,f=58 output of one P59 pivot."""
    f = 58
    h = 1
    rows = {}
    origin_parameters = []
    for a_e in range(f + 1):
        for c_s in range(f - a_e + 1):
            base = f + 2 * a_e + c_s
            for q in range(max(0, M - base)):
                row = C.row_of(r, s, z, f, h, a_e, c_s, q)
                if (a_e, c_s, q) == (0, 0, 0):
                    label = "ordinary"
                elif (a_e, c_s, q) == (0, 1, 0):
                    label = "curvature"
                elif (a_e, c_s, q) == (0, 0, 1):
                    label = "jet"
                else:
                    raise AssertionError((a_e, c_s, q, row))
                assert label not in rows
                rows[label] = row
                origin_parameters.append((label, a_e, c_s, q, row))
    assert tuple(sorted(rows)) == tuple(sorted(ROW_ORDER))
    return {
        "name": name,
        "pivot_P59_r_s_outerZ": (r, s, z),
        "enumerated_origin_parameters": tuple(origin_parameters),
        "rows": tuple((label, rows[label]) for label in ROW_ORDER),
    }


def origin_signature(origin):
    return (
        origin["kind"], origin["r"], origin["s"],
        origin["source_y_or_k"], origin["contact_f"],
        origin["u_power_h"], origin["u0_power"], origin["aE"],
        origin["cS"], origin["coefficient_hasse_q"],
        origin["coefficient_width"],
        origin["scalar_mod_p_before_Uh_Hq"],
    )


def aggregate_provenance(frontiers):
    """Invert all six target keys over all 187 C/P physical streams."""
    receipts = []
    residual_groups_by_row = {}
    all_signatures = []
    for frontier in frontiers:
        for label, row in frontier["rows"]:
            origins = C.exact_target_provenance(row)
            signatures = tuple(map(origin_signature, origins))
            assert origins and all(origin["u0_power"] == 0 for origin in origins)

            groups = defaultdict(list)
            for origin in origins:
                key = (
                    origin["r"], origin["s"], origin["contact_f"],
                    origin["coefficient_hasse_q"], origin["aE"],
                    origin["cS"],
                )
                groups[key].append(origin)
            residual = tuple(sorted(
                key for key in groups
                if key[3] > CD.complete_qmax(key[0], key[1], key[2])
            ))
            row_name = f'{frontier["name"]}_{label}'
            residual_groups_by_row[row_name] = residual
            signature_sha = hashlib.sha256(
                json.dumps(signatures, separators=(",", ":")).encode()
            ).hexdigest()
            receipts.append({
                "row_name": row_name,
                "target_key_T_E_R_S_Z": row,
                "physical_same_key_origin_count": len(origins),
                "physical_contact_block_count": len(groups),
                "post_complete_depth_residual_groups": residual,
                "origin_signature_sha256": signature_sha,
            })
            all_signatures.append((row_name, signatures))

    expected_residual = {
        "band1_ordinary": (),
        "band1_curvature": (),
        "band1_jet": ((11, 10, 57, 2, 0, 0),),
        "band2_ordinary": ((11, 10, 56, 2, 0, 0),),
        "band2_curvature": ((11, 10, 56, 2, 0, 1),),
        "band2_jet": (
            (10, 10, 57, 2, 0, 0),
            (11, 10, 56, 3, 0, 0),
            (12, 9, 56, 2, 0, 1),
        ),
    }
    assert residual_groups_by_row == expected_residual
    assert tuple(r["physical_same_key_origin_count"] for r in receipts) == (
        11, 11, 20, 26, 26, 40)
    assert sum(r["physical_same_key_origin_count"] for r in receipts) == 134
    return tuple(receipts), hashlib.sha256(
        json.dumps(all_signatures, separators=(",", ":")).encode()
    ).hexdigest()


def controls_for(frontiers):
    controls = {}
    physical_sections = {}
    row_by_name = {}
    for frontier in frontiers:
        name = frontier["name"]
        _pivot_name, r, s, z = next(p for p in PIVOTS if p[0] == name)
        for label, row in frontier["rows"]:
            row_by_name[f"{name}_{label}"] = row

        p58 = (58, r, s)
        p57 = (57, r + 1, s)
        controls[f"{name}_x"] = {
            "physical": p58, "coordinate": "H0",
            "matched_row": f"{name}_ordinary",
        }
        controls[f"{name}_y"] = {
            "physical": p57, "coordinate": "H1_with_H0_zero",
            "matched_row": f"{name}_curvature",
        }
        controls[f"{name}_z"] = {
            "physical": p58, "coordinate": "H1",
            "matched_row": f"{name}_jet",
        }
        p58_width = C.correction_width(58, r, s)
        p57_width = C.correction_width(57, r + 1, s)
        assert p58_width > 2 * N and p57_width > 2 * N
        physical_sections[name] = {
            "outer_Z_active_degree": (z + 1, 58 + r + s),
            "P58_r_s_width_twoN_slack": (
                r, s, p58_width, p58_width - 2 * N),
            "P57_r_s_width_twoN_slack": (
                r + 1, s, p57_width, p57_width - 2 * N),
            "P58_section": (
                "confluent Hermite interpolation prescribes H0,H1 jointly; "
                "all Hq,q>=2 retained as linear operators in (x,z)"),
            "P57_section": (
                "delta=Omega*V preserves H0=0 and prescribes H1 because "
                "H1(Omega)(alpha)=N*alpha^-1 is a unit; Hq,q>=2 retained"),
        }
    assert tuple(controls) == NODE_ORDER
    assert len({tuple(v["physical"]) for v in controls.values()}) == 4
    return controls, physical_sections, row_by_name


def coordinate_owners(control_name, coefficient_q):
    """Conservative exact dependency of a section's q-th induced jet."""
    band, coordinate = control_name.rsplit("_", 1)
    if coordinate == "y":
        return (control_name,) if coefficient_q >= 1 else ()
    if coordinate == "x":
        # The P58 section is shared with z.  q=0 is x, q=1 is z, and every
        # higher induced jet may depend linearly on both prescribed jets.
        if coefficient_q == 0:
            return (control_name,)
        if coefficient_q == 1:
            return (f"{band}_z",)
        return (control_name, f"{band}_z")
    if coordinate == "z":
        # Avoid scanning the shared P58 polynomial twice.  Its dependencies
        # are emitted through the x record above.
        return ()
    raise AssertionError(control_name)


def dependency_graph(controls, row_by_name):
    """Build the full six-row graph from literal physical provenance."""
    row_owner = {
        value["matched_row"]: name for name, value in controls.items()
    }
    adjacency = {name: set() for name in controls}
    contribution_records = []
    for row_name, row in row_by_name.items():
        owner = row_owner[row_name]
        origins = C.exact_target_provenance(row)
        for control_name, control in controls.items():
            if control_name.endswith("_z"):
                continue
            k, r, s = control["physical"]
            for origin in origins:
                if origin["kind"] != "P" or (
                        origin["source_y_or_k"], origin["r"], origin["s"]
                ) != (k, r, s):
                    continue
                q = origin["coefficient_hasse_q"]
                for source_coordinate in coordinate_owners(control_name, q):
                    adjacency[source_coordinate].add(owner)
                    contribution_records.append((
                        source_coordinate, owner, row_name, (k, r, s), q,
                        origin["contact_f"], origin["u_power_h"],
                        origin["cS"],
                        origin["scalar_mod_p_before_Uh_Hq"],
                    ))

    adjacency = {
        node: tuple(sorted(successors, key=NODE_ORDER.index))
        for node, successors in adjacency.items()
    }
    expected = {
        "band1_x": ("band1_x", "band1_y", "band2_z"),
        "band1_y": (
            "band1_x", "band1_y", "band1_z",
            "band2_x", "band2_y", "band2_z"),
        "band1_z": (
            "band1_z", "band2_x", "band2_y", "band2_z"),
        "band2_x": ("band2_x", "band2_y"),
        "band2_y": ("band2_x", "band2_y", "band2_z"),
        "band2_z": ("band2_z",),
    }
    assert adjacency == expected
    assert not any(successor.startswith("band1")
                   for node, successors in adjacency.items()
                   if node.startswith("band2") for successor in successors)
    return adjacency, tuple(sorted(contribution_records))


def tarjan_scc(adjacency):
    index = 0
    indices = {}
    low = {}
    stack = []
    on_stack = set()
    components = []

    def visit(vertex):
        nonlocal index
        indices[vertex] = low[vertex] = index
        index += 1
        stack.append(vertex)
        on_stack.add(vertex)
        for successor in adjacency[vertex]:
            if successor not in indices:
                visit(successor)
                low[vertex] = min(low[vertex], low[successor])
            elif successor in on_stack:
                low[vertex] = min(low[vertex], indices[successor])
        if low[vertex] == indices[vertex]:
            component = []
            while True:
                member = stack.pop()
                on_stack.remove(member)
                component.append(member)
                if member == vertex:
                    break
            components.append(tuple(sorted(component, key=NODE_ORDER.index)))

    for vertex in NODE_ORDER:
        if vertex not in indices:
            visit(vertex)
    return tuple(sorted(components, key=lambda c: NODE_ORDER.index(c[0])))


def modular_rank_and_det(matrix):
    a = [[value % P for value in row] for row in matrix]
    rows = len(a)
    columns = len(a[0]) if a else 0
    rank = 0
    determinant = 1
    sign = 1
    for column in range(columns):
        pivot = next((i for i in range(rank, rows) if a[i][column]), None)
        if pivot is None:
            continue
        if pivot != rank:
            a[pivot], a[rank] = a[rank], a[pivot]
            sign = -sign
        value = a[rank][column]
        determinant = determinant * value % P
        inverse = pow(value, -1, P)
        a[rank] = [entry * inverse % P for entry in a[rank]]
        for i in range(rows):
            if i == rank or not a[i][column]:
                continue
            factor = a[i][column]
            a[i] = [(left - factor * right) % P
                    for left, right in zip(a[i], a[rank])]
        rank += 1
    if rows != columns or rank != rows:
        determinant = 0
    return rank, determinant * sign % P


def diagonal_scc_gate(adjacency):
    components = tarjan_scc(adjacency)
    expected = (
        ("band1_x", "band1_y"), ("band1_z",),
        ("band2_x", "band2_y"), ("band2_z",),
    )
    assert components == expected

    minus_29 = -29 % P
    minus_57_half = -57 * INV2 % P
    two_by_two = ((1, 1), (minus_29, minus_57_half))
    rank2, det2 = modular_rank_and_det(two_by_two)
    assert (rank2, det2) == (2, INV2)
    rank1, det1 = modular_rank_and_det(((1,),))
    assert (rank1, det1) == (1, 1)

    # With row order ordinary,curvature,jet and controls x,y,z, the exact
    # all-node diagonal block is [[I,I,0],[-29I,-57/2 I,0],[0,K,I]].
    # K is H2 of the chosen Omega*V section and is never set to zero.
    for sample_k in (0, 1, P - 1, 17_291):
        matrix = (
            (1, 1, 0),
            (minus_29, minus_57_half, 0),
            (0, sample_k, 1),
        )
        assert modular_rank_and_det(matrix) == (3, INV2)
    return {
        "conservative_graph_adjacency": tuple(
            (node, adjacency[node]) for node in NODE_ORDER),
        "strongly_connected_components": components,
        "two_by_two_curvature_block_rows_A_C_cols_X_Y": two_by_two,
        "two_by_two_rank_determinant_mod_p": (rank2, det2),
        "jet_singleton_rank_determinant_mod_p": (rank1, det1),
        "one_band_operator_block": (
            "[[I,I,0],[-29I,-57/2 I,0],[0,K_actual,I]]"),
        "one_band_rank_cokernel_for_every_K": (3 * N, 0),
        "two_band_rank_cokernel_for_every_internal_and_cross_K": (6 * N, 0),
        "two_band_determinant": "(1/2)^(2N), nonzero in F_p",
        "explicit_section_for_target_a_c_b": (
            "y=58*a+2*c; x=-57*a-2*c; z=b-K_actual*y"),
    }


def outgoing_filtration_gate(frontiers):
    """Audit all structural outputs of the four physical section polynomials."""
    receipts = []
    all_full_rows = defaultdict(set)
    global_counts = Counter()
    for frontier in frontiers:
        name = frontier["name"]
        _pivot_name, r, s, pivot_z = next(p for p in PIVOTS if p[0] == name)
        source_z = pivot_z + 1
        sources = (
            ("P58_two_jet_section", 58, r, s, 0),
            ("P57_H0zero_H1_section", 57, r + 1, s, 1),
        )
        for source_name, k, source_r, source_s, q_min in sources:
            counts = Counter()
            full_rows = set()
            source_active = k + source_r + source_s
            assert source_active <= C.J
            source_order = (source_z, C.J - source_active)
            for f in range(k + 1):
                for a_e in range(f + 1):
                    for c_s in range(f - a_e + 1):
                        q_count = max(0, M - (f + 2 * a_e + c_s) - q_min)
                        if not q_count:
                            continue
                        if f == k:
                            assert k - f == 0
                            for q in range(q_min, q_min + q_count):
                                full_rows.add(C.row_of(
                                    source_r, source_s, source_z,
                                    f, 0, a_e, c_s, q))
                            counts["same_filtration_full_contact"] += q_count
                        else:
                            # h=k-f is u0-free and raises passive Z.
                            later_u0free_order = (
                                source_z + (k - f),
                                C.J - (f + source_r + source_s),
                            )
                            assert later_u0free_order > source_order
                            counts["strictly_later_u0free"] += q_count

                            # h=0,...,k-f-1 has positive u0.  At h=0,
                            # passive Z ties but active degree drops, and at
                            # every h>0 passive Z itself increases.
                            same_z_order = (
                                source_z, C.J - (f + source_r + source_s))
                            assert same_z_order > source_order
                            counts["strictly_later_positive_u0"] += (
                                (k - f) * q_count)

            expected_counts = (
                Counter({
                    "same_filtration_full_contact": 3,
                    "strictly_later_u0free": 109_171,
                    "strictly_later_positive_u0": 3_973_894,
                }) if k == 58 else Counter({
                    "same_filtration_full_contact": 3,
                    "strictly_later_u0free": 102_396,
                    "strictly_later_positive_u0": 3_662_434,
                })
            )
            assert counts == expected_counts
            expected_frontier_rows = {
                row for _label, row in frontier["rows"]}
            assert full_rows == expected_frontier_rows
            all_full_rows[name].update(full_rows)
            global_counts.update(counts)
            receipts.append({
                "band_source_k_r_s_outerZ_qmin": (
                    name, source_name, k, source_r, source_s, source_z, q_min),
                "source_filtration_Z_JminusActive": source_order,
                "complete_output_occurrence_counts": tuple(sorted(counts.items())),
                "same_filtration_rows": tuple(sorted(full_rows)),
                "every_nonfull_output_strictly_advances_Z_negActive": True,
            })
    assert all(len(rows) == 3 for rows in all_full_rows.values())
    assert global_counts == Counter({
        "same_filtration_full_contact": 12,
        "strictly_later_u0free": 423_134,
        "strictly_later_positive_u0": 15_272_656,
    })
    return {
        "common_well_founded_order": (
            "lexicographic (outer passive Z, J-active degree E+R+S)"),
        "proof_of_strictness": (
            "for contact f<k, h>0 raises Z; h=0 keeps Z and lowers active "
            "degree from k+r+s to f+r+s"),
        "physical_section_receipts": tuple(receipts),
        "global_occurrence_counts": tuple(sorted(global_counts.items())),
        "all_same_filtration_outputs_are_exactly_the_six_audited_rows": True,
        "every_other_output_strictly_advances_the_common_order": True,
    }


def main():
    for filename, expected in AUTHORITIES.items():
        assert file_sha256(HERE / filename) == expected
    assert (P - 1) % N == 0 and N % P != 0

    frontiers = tuple(first_later_frontier(*pivot) for pivot in PIVOTS)
    assert tuple(row for frontier in frontiers for _label, row in frontier["rows"]) == (
        (58, 0, 68, 10, 2625),
        (59, 0, 67, 11, 2625),
        (59, 0, 68, 10, 2625),
        (58, 0, 67, 10, 2626),
        (59, 0, 66, 11, 2626),
        (59, 0, 67, 10, 2626),
    )
    provenance, provenance_sha = aggregate_provenance(frontiers)
    assert provenance_sha == EXPECTED_ALL_PROVENANCE_SHA256
    controls, physical_sections, row_by_name = controls_for(frontiers)
    adjacency, contributions = dependency_graph(controls, row_by_name)
    contributions_sha = hashlib.sha256(
        json.dumps(contributions, separators=(",", ":")).encode()
    ).hexdigest()
    assert contributions_sha == EXPECTED_DEPENDENCY_CONTRIBUTIONS_SHA256
    scc_gate = diagonal_scc_gate(adjacency)
    filtration = outgoing_filtration_gate(frontiers)

    stable = {
        "scope": (
            "all six live u0-free rows on the first strictly-later passive-Z "
            "layer emitted by the two P59 q0 pivots of 91265f0; every "
            "same-key C/P origin, curvature collision, and section-induced "
            "higher jet retained; later filtration grades not solved"),
        "target_p_N_M": (P, N, M),
        "authority_sha256": tuple(sorted(AUTHORITIES.items())),
        "p59_pivot_frontiers": frontiers,
        "aggregate_physical_provenance": provenance,
        "all_134_origin_signatures_sha256": provenance_sha,
        "legal_physical_sections": tuple(sorted(physical_sections.items())),
        "dependency_contributions": contributions,
        "dependency_contributions_sha256": contributions_sha,
        "pivot_dependency_and_exact_scc_gate": scc_gate,
        "outgoing_filtration_gate": filtration,
        "decision": "GREEN_WHOLE_SIX_ROW_FIRST_LATER_Z_FRONTIER",
        "scope_guard": (
            "This removes the first exported frontier as an obstruction and "
            "provides a common acyclic order. It does not instantiate the "
            "sections at the remaining 423134 u0-free and 15272656 "
            "positive-u0 occurrences, close one full passive band, prove "
            "F3 containment, or produce a lower-6900 candidate."),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    print(json.dumps({
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": file_sha256(Path(__file__)),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
