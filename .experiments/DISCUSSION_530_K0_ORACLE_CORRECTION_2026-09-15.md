### Correction: k0 finite-contact oracle mismatch (2026-09-15 UTC)

We found a material model mismatch while independently replaying the new
projected-head test. Please **do not use the earlier finite k0 rank numbers as
evidence for the formal flattened contact map** until their literal replays
land.

The affected Python path called `higher_jet_literal_matrix.translated_column`
with `k=2`. That oracle has a compressed local error variable and the contact
substitution ending at the second jet. The actual flattened k0 map proved in
`K0MinimalRawContactFormula6900.lean` and typed through the accepted source is

```text
Y -> u0 + u1*Z + eps*R - eps^2*S + eps^3*T
```

with local rows `(eps,S,T,R,Z)` and no compressed error variable. Selecting
rows merely by the old oracle's outer index is therefore not the formal
`eps>=3` head projection.

Withdrawn pending literal replay:

- the numerical `L=10 -> 11` terminal-rank-one interpretation in commit
  `11e1c94`;
- complete/passive/head ranks obtained through the same `k=2` helper;
- the old direct-witness contact support counts (its source legality and the
  agreement/error conceptual failure remain valid).

Still valid:

- the axiom-clean literal raw-contact formula and source typing;
- the abstract relative exact sequence and quotient-aware dual-detection
  lemmas;
- the target source/consumer arithmetic for `(47,16,8,64,3757/3758)`;
- the direct locator witness is source-legal and vanishes on agreements, but
  cannot be asserted to lie in the all-node head kernel;
- the reduction of head-boundary surjectivity to one nonzero-Y witness,
  conditional on constructing that witness for the literal map.

Three independent jobs are now using the literal flattened substitution:

1. exact centered-family correction on the frozen m8 control;
2. a corrected universal/passive-cap replay;
3. symbolic local `C2`, `W*C1`, and R/S companion identities plus the target
   source-degree ledger.

This correction lowers current confidence; there is still no 6900 candidate
or verifier-ready submission. We are treating the literal replay as a hard
go/no-go gate before making another rank claim.
