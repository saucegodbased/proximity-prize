#!/usr/bin/env python3
"""All-defect actual-residual and high positive-prefix gate for m69.

For every deliberately overinclusive deficient physical coefficient from the
exact m69 Pascal census, this gate reconstructs the literal incoming source
pattern.  If the current contact coefficient has exponent ``y``, then:

* the current ``h=0`` control is excluded from the incoming residual;
* ordinary higher-contact sources have powers ``W^h``, ``1 <= h < M-y``;
* the terminal source has power ``W^(J-(y+r+s))``.

Thus every incoming term is divisible by W.  Independently, the script finds
the largest *positive-power* direct prefix for every deficient shape.  Its
dimension is at least 258868, so one such channel interpolates any W-positive
target whenever W has at least 3276 nodal zeros.  This is an individual-target
containment theorem only: it does not allocate shared higher-contact tails
simultaneously across the 140153 coefficient equations.
"""

from __future__ import annotations

from collections import Counter
from math import comb
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
MAX_NUMERATOR_ZEROS = 149_776

AUTHORITIES = {
    "m69_reciprocal_all_defect_interval_gate_6900.py":
        "9417a5797aa188cb6a1381b7c11e54f3df0ecf46908ad452d6dee925e1ae5069",
    "m69_hasse_prefix_weight_nonvanishing_gate_6900.py":
        "ec5a2c3db24985f6822f88f4918adc393e4bdcae785264de3446fbd7c0f7762c",
    "M69FirstDefectActualResidualZeroSplit6900.lean":
        "7a2a8bf216dcc29437aab716d5bfcc0e934a5cb59fafbd88bd904a671aa2e0df",
}


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sha256_repr(value) -> str:
    return hashlib.sha256(repr(value).encode()).hexdigest()


def incoming_residual_gate(coefficients):
    """Audit the exact power/scalar ledger for every physical coefficient."""
    direct_power_histogram = Counter()
    terminal_power_histogram = Counter()
    direct_count_histogram = Counter()
    terminal_dimension_histogram = Counter()
    stream = hashlib.sha256()
    direct_term_count = 0
    terminal_term_count = 0

    minimum_terminal_power = profile.J
    maximum_terminal_power = 0
    minimum_direct_last = profile.M
    maximum_direct_last = 0
    minimum_terminal_gap = profile.J
    maximum_terminal_gap = 0
    minimum_terminal_dimension = N
    maximum_terminal_dimension = 0

    for y, r, s, q in coefficients:
        active = y + r + s
        terminal_y = profile.J - r - s
        terminal_power = terminal_y - y
        direct_last = profile.M - y - 1
        terminal_gap = terminal_power - direct_last

        # These facts rule out a hidden h=0 term.  The active range is strict
        # (A<J), every deficient shape has r+s<=24, and M=69,J=94.
        assert active < profile.J
        assert 1 <= direct_last
        assert terminal_power == profile.J - active
        assert terminal_power >= 1
        assert terminal_gap == profile.J - profile.M + 1 - r - s
        assert 2 <= terminal_gap <= 26

        # The special terminal coefficient C_q is a literal nonempty Hasse
        # window.  Its Pascal scalar is nonzero because terminal_y<p.
        terminal_width = profile.width(terminal_y, r, s)
        terminal_dimension = terminal_width - q
        terminal_scalar = comb(terminal_y, y) % P
        assert terminal_width == 127_823 + r + 2 * s
        assert 0 < terminal_dimension < N
        assert terminal_scalar != 0

        terminal_power_histogram[terminal_power] += 1
        direct_count_histogram[direct_last] += 1
        terminal_dimension_histogram[terminal_dimension] += 1
        terminal_term_count += 1
        minimum_terminal_power = min(minimum_terminal_power, terminal_power)
        maximum_terminal_power = max(maximum_terminal_power, terminal_power)
        minimum_direct_last = min(minimum_direct_last, direct_last)
        maximum_direct_last = max(maximum_direct_last, direct_last)
        minimum_terminal_gap = min(minimum_terminal_gap, terminal_gap)
        maximum_terminal_gap = max(maximum_terminal_gap, terminal_gap)
        minimum_terminal_dimension = min(
            minimum_terminal_dimension, terminal_dimension)
        maximum_terminal_dimension = max(
            maximum_terminal_dimension, terminal_dimension)

        terminal_record = (
            "C", y, r, s, q, terminal_y, terminal_power,
            terminal_width, terminal_dimension, terminal_scalar,
        )
        stream.update(repr(terminal_record).encode())
        stream.update(b"\n")

        # q is already outside the complete current prefix.  Complete depth
        # decreases along higher contact, so every higher source is a genuine
        # free prefix.  Commit 34bcb23 separately proves every Hasse diagonal
        # weight in each such prefix is nonzero.
        for power in range(1, direct_last + 1):
            source_y = y + power
            width = profile.width(source_y, r, s)
            depth, fringe = divmod(width, N)
            scalar = comb(source_y, y) % P
            assert y < source_y < profile.M
            assert 1 <= depth <= q <= profile.M - 1
            assert 0 < fringe < N
            assert scalar != 0
            direct_record = (
                "U", y, r, s, q, power, source_y,
                depth, fringe, scalar,
            )
            stream.update(repr(direct_record).encode())
            stream.update(b"\n")
            direct_power_histogram[power] += 1
            direct_term_count += 1

    assert terminal_term_count == 140_153
    assert direct_term_count == 7_778_831
    assert direct_term_count + terminal_term_count == 7_918_984
    assert (minimum_terminal_power, maximum_terminal_power) == (31, 94)
    assert (minimum_direct_last, maximum_direct_last) == (25, 68)
    assert (minimum_terminal_gap, maximum_terminal_gap) == (2, 26)
    assert (minimum_terminal_dimension, maximum_terminal_dimension) == (
        127_755, 127_842)

    return {
        "physical_deficient_coefficient_count": len(coefficients),
        "excluded_current_control_power": 0,
        "direct_incoming_power_formula": "1 <= h <= M-y-1",
        "direct_incoming_positive_term_count": direct_term_count,
        "direct_last_power_range": (minimum_direct_last,
                                    maximum_direct_last),
        "direct_power_histogram": tuple(sorted(
            direct_power_histogram.items())),
        "terminal_formula": (
            "terminalY=J-r-s; terminalPower=terminalY-y=J-(y+r+s)"),
        "terminal_incoming_term_count": terminal_term_count,
        "terminal_power_range": (minimum_terminal_power,
                                 maximum_terminal_power),
        "terminal_power_histogram": tuple(sorted(
            terminal_power_histogram.items())),
        "terminal_minus_last_direct_power_range": (
            minimum_terminal_gap, maximum_terminal_gap),
        "terminal_Hq_dimension_range": (
            minimum_terminal_dimension, maximum_terminal_dimension),
        "terminal_Hq_dimension_histogram_sha256": sha256_repr(tuple(sorted(
            terminal_dimension_histogram.items()))),
        "literal_formula": (
            "binom(J-r-s,y) W^(J-(y+r+s)) C_q + "
            "sum_(h=1)^(M-y-1) binom(y+h,y) W^h U_(y+h,q)"),
        "all_actual_incoming_terms_have_strictly_positive_W_power": True,
        "all_actual_incoming_residuals_vanish_on_the_numerator_zero_set":
            True,
        "every_pascal_scalar_is_nonzero_mod_p": True,
        "incoming_term_stream_sha256": stream.hexdigest(),
    }


def best_positive_channel(shape):
    """Unique largest direct prefix among powers 1,...,M-y-1."""
    y, r, s = shape
    candidates = []
    for power in range(1, profile.M - y):
        width = profile.width(y + power, r, s)
        depth, fringe = divmod(width, N)
        candidates.append((fringe, power, depth))
    maximum_fringe = max(fringe for fringe, _power, _depth in candidates)
    maximizers = tuple(record for record in candidates
                       if record[0] == maximum_fringe)
    assert len(maximizers) == 1
    fringe, power, depth = maximizers[0]
    return power, depth, fringe, N - fringe


def high_positive_prefix_gate(shapes, coefficients):
    """Find the exact one-channel large-zero threshold for every shape."""
    shape_records = []
    shape_power_histogram = Counter()
    shape_threshold_histogram = Counter()
    coefficient_power_histogram = Counter()
    coefficient_threshold_histogram = Counter()

    for shape in shapes:
        power, depth, fringe, threshold = best_positive_channel(shape)
        y, r, s = shape
        assert 1 <= power < profile.M - y
        assert 1 <= depth
        assert 258_868 <= fringe <= 258_926
        assert 3_218 <= threshold <= 3_276
        record = (shape, power, depth, fringe, threshold)
        shape_records.append(record)
        shape_power_histogram[power] += 1
        shape_threshold_histogram[threshold] += 1

    by_shape = {
        shape: (power, depth, fringe, threshold)
        for shape, power, depth, fringe, threshold in shape_records
    }
    coefficient_stream = hashlib.sha256()
    for y, r, s, q in coefficients:
        power, depth, fringe, threshold = by_shape[(y, r, s)]
        # 34bcb23's exhaustive exact-field receipt covers this (depth,q)
        # pair and every coefficient exponent below fringe.
        assert depth <= q <= profile.M - 1
        assert threshold + fringe == N
        coefficient_power_histogram[power] += 1
        coefficient_threshold_histogram[threshold] += 1
        coefficient_stream.update(repr((
            y, r, s, q, power, depth, fringe, threshold)).encode())
        coefficient_stream.update(b"\n")

    first_defect = by_shape[(39, 14, 10)]
    hostile_zero_shape = by_shape[(0, 0, 0)]
    assert first_defect == (28, 1, 258_926, 3_218)
    assert hostile_zero_shape == (67, 13, 258_868, 3_276)
    assert max(record[-1] for record in shape_records) == 3_276
    assert min(record[-1] for record in shape_records) == 3_218
    assert all(record[-1] <= MAX_NUMERATOR_ZEROS
               for record in shape_records)

    return {
        "positive_direct_channel_selection": (
            "for each (y,r,s), uniquely maximize "
            "rho_h=width(y+h,r,s) mod N over 1<=h<M-y"),
        "shape_count": len(shape_records),
        "coefficient_count": len(coefficients),
        "selected_power_range": (
            min(record[1] for record in shape_records),
            max(record[1] for record in shape_records)),
        "selected_prefix_dimension_range": (
            min(record[3] for record in shape_records),
            max(record[3] for record in shape_records)),
        "exact_zero_threshold_range_N_minus_prefix": (
            min(record[4] for record in shape_records),
            max(record[4] for record in shape_records)),
        "uniform_zero_threshold": 3_276,
        "first_defect_power_depth_prefix_threshold": first_defect,
        "former_countergate_shape_power_depth_prefix_threshold":
            hostile_zero_shape,
        "shape_selected_power_histogram": tuple(sorted(
            shape_power_histogram.items())),
        "shape_exact_threshold_histogram": tuple(sorted(
            shape_threshold_histogram.items())),
        "coefficient_selected_power_histogram": tuple(sorted(
            coefficient_power_histogram.items())),
        "coefficient_exact_threshold_histogram": tuple(sorted(
            coefficient_threshold_histogram.items())),
        "shape_selection_receipt_sha256": sha256_repr(tuple(shape_records)),
        "coefficient_selection_stream_sha256":
            coefficient_stream.hexdigest(),
        "hasse_prefix_authority_commit": "34bcb23",
        "hasse_prefix_nonzero_for_every_selected_coefficient": True,
        "one_channel_theorem": (
            "if z=#{i:W(i)=0} >= N-rho_h, interpolate target/W^h on "
            "the <=rho_h live nodes; W^h*A equals every target which "
            "vanishes on the zero set"),
        "uniform_consequence": (
            "every individual deficient coefficient target is contained "
            "using one positive direct channel whenever z>=3276"),
        "remaining_small_zero_branch": "0 <= z <= 3275",
    }


def main():
    for filename, expected in AUTHORITIES.items():
        assert file_sha256(HERE / filename) == expected
    defects, shapes, coefficients = profile.defect_census()
    assert len(defects) == 13_093
    assert len(shapes) == 6_930
    assert len(coefficients) == 140_153

    incoming = incoming_residual_gate(coefficients)
    positive = high_positive_prefix_gate(shapes, coefficients)
    stable = {
        "scope": (
            "all 140153 rank-insensitive deficient m69 physical "
            "coefficients; individual actual-target containment only, not "
            "simultaneous allocation or multi-stratum confluence"),
        "profile_M_slope_curvature_J_L": (
            profile.M, profile.SLOPE, profile.CURVATURE,
            profile.J, profile.L),
        "authority_sha256": tuple(sorted(AUTHORITIES.items())),
        "actual_incoming_residual_gate": incoming,
        "best_positive_direct_prefix_gate": positive,
        "decision": (
            "GREEN_EVERY_ACTUAL_INCOMING_RHS_IS_W_POSITIVE__"
            "GREEN_ONE_HIGH_POSITIVE_CHANNEL_FOR_Z_GE_3276__"
            "STOP_SIMULTANEOUS_CONFLUENCE_AND_Z_LE_3275"),
        "scope_guard": (
            "A separately solvable coefficient family need not admit a "
            "single simultaneous choice of shared higher-contact tails. "
            "Nothing here proves the z<=3275 rational rank branch."),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    assert peak < 512 * 1024
    print(json.dumps({
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": file_sha256(Path(__file__)),
        "peak_rss_kib": peak,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
