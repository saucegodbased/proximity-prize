#!/usr/bin/env python3
"""Targeted hardest-family variant of the exact m69 block gate.

Take Z=X^4096, E=Z-2 and

    N0 = Z^32 E + 2 = Z^33 - 2 Z^32 + 2.

Modulo E the numerator is 1, so the pair is reduced, while
W=N0/E=Z^32+2/E is the smallest root-free coprime perturbation of the
forbidden
involution W=Z^32.  The latter would preserve the even Pascal modes but has
the illegal common factor E.  This checks whether the minimal perturbation
already restores exact terminal containment.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from collections import Counter, defaultdict

import m69_literal_pascal_high_numerator_block_gate_6900 as gate


def primitive_64th_root():
    for base in range(2, 100):
        root = pow(base, (gate.P - 1) // 64, gate.P)
        if pow(root, 64, gate.P) == 1 and pow(root, 32, gate.P) != 1:
            return root
    raise AssertionError("no primitive 64th root found")


def main():
    # Install the near-involution numerator into the exact rank oracle.
    numerator = [0] * gate.BLOCK_LENGTH
    numerator[0] = 2
    numerator[32] = gate.P - 2
    numerator[33] = 1
    gate.N0 = tuple(numerator)
    gate.N_POWERS = gate.power_table(gate.N0, gate.TERMINAL - gate.FIRST_Y)

    root = primitive_64th_root()
    values = []
    value = 1
    for _ in range(64):
        nvalue = (pow(value, 33, gate.P)
                  - 2 * pow(value, 32, gate.P) + 2) % gate.P
        values.append(nvalue)
        value = value * root % gate.P
    zero_count = sum(value == 0 for value in values)
    assert zero_count == 0

    grouped = defaultdict(list)
    for residue in range(gate.STRIDE):
        grouped[gate.block_pattern(residue)].append(residue)
    rank_histogram = Counter()
    defect_histogram = Counter()
    records = []
    for pattern, residues in sorted(grouped.items(), key=lambda item: item[1][0]):
        source, target = gate.pattern_matrices(pattern)
        source_rank = source.rank()
        augmented_rank = gate.horizontal_concat(source, target).rank()
        defect = augmented_rank - source_rank
        rank_histogram[source_rank] += len(residues)
        defect_histogram[defect] += len(residues)
        records.append(((residues[0], residues[-1], len(residues)),
                        pattern, (source.nrows(), source.ncols(), target.ncols()),
                        (source_rank, augmented_rank, defect)))
    assert defect_histogram == Counter({0: gate.STRIDE})
    stable = {
        "numerator": "N0=Z^32*(Z-2)+2=Z^33-2Z^32+2",
        "degrees_e_n": (4096, 135168),
        "gcd_receipt_N_mod_E": 2,
        "primitive_64th_root": root,
        "numerator_zero_count_on_Z64": zero_count,
        "distinct_residue_cap_pattern_count": len(grouped),
        "source_rank_histogram_weighted_by_residue": tuple(sorted(rank_histogram.items())),
        "target_containment_defect_histogram_weighted_by_residue": tuple(sorted(defect_histogram.items())),
        "pattern_record_stream_sha256": hashlib.sha256(repr(tuple(records)).encode()).hexdigest(),
        "decision": "GREEN_MINIMAL_COPRIME_PERTURBATION_OF_INVOLUTION",
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    print(json.dumps({
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
