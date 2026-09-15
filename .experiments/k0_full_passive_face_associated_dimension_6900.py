#!/usr/bin/env python3
"""Exact dimension gate for the complete k0 successor passive face.

No matrix is materialized.  The global face is enumerated directly over
legal ``(S,R,Y)`` shapes; the local associated cap is independently
enumerated as the successor-layer slope of the accepted relaxed source and
weighted-kernel counts.  Both are cross-checked against the literal closed
formula transcriptions used by the accepted second-jet source.

This is only an associated-grade gate.  Its kernel need not lift through the
lower passive grades of complete contact, and it says nothing by itself
about the four-row boundary image.
"""

from __future__ import annotations

import hashlib
import json
import sys

sys.path.insert(0, ".experiments")
import higher6810_secondjet_retarget_exact as Closed  # noqa: E402


def nsub(a: int, b: int) -> int:
    return max(a - b, 0)


def q_value(m: int, s_cap: int, outer: int, h: int) -> int:
    return max((m - outer + 1) // 2,
               nsub(nsub(m, outer), nsub(s_cap, h)))


def global_face_by_s(
    g: int, m: int, w: int, B: int, s_cap: int, U: int
) -> tuple[int, ...]:
    """Number of new cap-face X coefficients, split by raw S exponent."""
    D = m * g
    answer: list[int] = []
    for s in range(s_cap + 1):
        subtotal = 0
        for r in range(B - 2 * s + 1):
            for y in range(U - s - r + 1):
                weight = (w - 2) * s + (w - 1) * r + w * y
                assert weight < D
                subtotal += D - weight
        answer.append(subtotal)
    return tuple(answer)


def local_face_slopes(
    m: int, B: int, s_cap: int, U: int
) -> tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]:
    """Successor slopes of local source, known kernel, and their difference."""
    source = [0] * (s_cap + 1)
    kernel = [0] * (s_cap + 1)
    for outer in range(m):
        for h in range(s_cap + 1):
            source[h] += sum(
                1
                for i in range(outer + 1)
                for j in range(nsub(B, 2 * h) + 1)
                if h + i + j <= U
            )
            q = q_value(m, s_cap, outer, h)
            if q <= outer and nsub(m, outer) + 2 * h <= B:
                kernel[h] += sum(
                    1
                    for i in range(nsub(outer, q) + 1)
                    for j in range(nsub(nsub(B, 2 * h), q) + 1)
                    if h + q + i + j <= U
                )
    rank = [a - b for a, b in zip(source, kernel)]
    return tuple(source), tuple(kernel), tuple(rank)


def profile(
    *, n: int, g: int, m: int, w: int, B: int, s_cap: int, U: int,
    old_cap: int, crosscheck_closed: bool,
) -> dict[str, object]:
    by_s = global_face_by_s(g, m, w, B, s_cap, U)
    local_source, local_kernel, local_rank = local_face_slopes(
        m, B, s_cap, U
    )
    face = sum(by_s)
    one_node_cap = sum(local_rank)
    all_node_cap = n * one_node_cap

    # Cross-check target successor slopes against the accepted closed
    # formulas.  That transcription fixes the target W globally, so the
    # scaled control intentionally uses only the independent enumerators.
    if crosscheck_closed:
        assert w == Closed.W
        closed_face = (
            Closed.coefficient_count(
                g, m, old_cap + 1, B, s_cap, U, 0, 1
            )
            - Closed.coefficient_count(g, m, old_cap, B, s_cap, U, 0, 1)
        )
        closed_cap = (
            Closed.relaxed_rank_bound(m, old_cap + 1, B, s_cap, U)
            - Closed.relaxed_rank_bound(m, old_cap, B, s_cap, U)
        )
        assert face == closed_face
        assert one_node_cap == closed_cap

    return {
        "parameters_n_g_m_w_B_s_U_oldCap_newCap": (
            n, g, m, w, B, s_cap, U, old_cap, old_cap + 1
        ),
        "global_face_columns_by_raw_S": by_s,
        "global_face_columns": face,
        "local_source_slope_by_h": local_source,
        "local_known_kernel_slope_by_h": local_kernel,
        "local_rank_cap_slope_by_h": local_rank,
        "one_node_associated_rank_cap": one_node_cap,
        "all_node_associated_rank_cap": all_node_cap,
        "associated_dimension_surplus": face - all_node_cap,
    }


def main() -> None:
    target = profile(
        n=262_144, g=180_413, m=47, w=131_071,
        B=16, s_cap=8, U=64, old_cap=3757, crosscheck_closed=True,
    )
    assert target["global_face_columns_by_raw_S"] == (
        3_671_014_323,
        3_233_888_380,
        2_798_728_244,
        2_365_271_777,
        1_933_256_841,
        1_502_421_298,
        1_072_503_010,
        643_239_839,
        214_369_647,
    )
    assert target["local_source_slope_by_h"] == (
        19_176, 16_920, 14_664, 12_408, 10_152,
        7_896, 5_640, 3_384, 1_128,
    )
    assert target["local_known_kernel_slope_by_h"] == (
        7_252, 5_789, 4_437, 3_220, 2_162,
        1_287, 619, 182, 0,
    )
    assert target["local_rank_cap_slope_by_h"] == (
        11_924, 11_131, 10_227, 9_188, 7_990,
        6_609, 5_021, 3_202, 1_128,
    )
    assert (
        target["global_face_columns"],
        target["one_node_associated_rank_cap"],
        target["all_node_associated_rank_cap"],
        target["associated_dimension_surplus"],
    ) == (17_434_693_359, 66_420, 17_411_604_480, 23_088_879)

    # Corrected formal-contact m6 control.  The exact full L8 -> L9 run has
    # contact-rank increment 5445-4719=726, exactly this all-node cap; hence
    # its attached nullity grows by the predicted 133 dimensions.
    control = profile(
        n=11, g=8, m=6, w=5, B=2, s_cap=1, U=8, old_cap=8,
        crosscheck_closed=False,
    )
    assert (
        control["global_face_columns"],
        control["one_node_associated_rank_cap"],
        control["all_node_associated_rank_cap"],
        control["associated_dimension_surplus"],
    ) == (859, 66, 726, 133)
    control["observed_complete_contact_rank_old_new"] = (4719, 5445)
    control["observed_complete_kernel_old_new"] = (45, 178)
    assert 5445 - 4719 == 726
    assert 178 - 45 == 133

    raw_only_columns = sum(
        47 * 180_413 - 131_071 * y for y in range(65)
    )
    raw_only_hermite_cap = 262_144 * (47 * 48 // 2)
    assert (raw_only_columns, raw_only_hermite_cap,
            raw_only_hermite_cap - raw_only_columns) == (
        278_534_035, 295_698_432, 17_164_397
    )

    payload = {
        "scope": "complete successor passive face; associated grade only",
        "target": target,
        "corrected_formal_m6_control": control,
        "raw_only_target": {
            "columns": raw_only_columns,
            "bivariate_Hermite_cap": raw_only_hermite_cap,
            "deficit": raw_only_hermite_cap - raw_only_columns,
        },
        "logical_scope": {
            "green": (
                "dimension-forced associated kernel conditional on the "
                "filtration-compatible 66420/node rank cap"
            ),
            "open": (
                "lift associated kernel through lower passive grades and "
                "separate the missing boundary class"
            ),
        },
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
