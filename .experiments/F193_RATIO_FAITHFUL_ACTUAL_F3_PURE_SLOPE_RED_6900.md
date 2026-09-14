# Ratio-faithful actual-F3 pure-plus-slope connector: exact RED

Date: 2026-09-14 UTC. Scope: lower-6900 research only. This is an exact
finite-field discriminator, not a Full187 theorem, score, candidate, or
submission.

## Decision

The two-shape first-shell mechanism that is GREEN in the balanced F101
chamber does **not** persist into a chamber with the target's strict degree
inequalities. In the exact F193 ratio-faithful chamber, the complete
grade-`J` prefix plus every legal raw first-shell column of shapes

```text
(r,s)=(0,0) and (r,s)=(1,0)
```

fails to lift each of the actual `F0,F1,F2,F3` packets by one rank. Their
joint defect remains four. This decisively falsifies a uniform
pure-plus-first-slope connecting-surjectivity theorem.

It does **not** falsify the complete first shell. Curvature `(0,1)` was
deliberately omitted from this binary gate, and the earlier arbitrary-error
small controls make it the next semantically justified family.

## Exact chamber and fidelity

The executable artifact is
`f193_ratio_faithful_actual_f3_connector_gate_6900.py`, invoked with
`--decisive-only`. It fixes

```text
F_193,
(N,w,g,m,D,s,t,J,L)=(64,31,44,4,176,1,1,6,10),
e=N-g=20,
G={0,...,43}, E={44,...,63},
agreement direction Q=Xi_E^2, deg Q=40,
error direction X^(e-1)=X^19,
F3=B(Y-Zq_H).
```

All 64 nodes `0,...,63` are distinct in F193. The chamber obeys exactly

```text
w < 2e < g < e+w,
31 < 40 < 44 < 51,
g-(e+w) = -7.
```

Full187 has the same strict chamber, with `g-(e+w)=-32389`. This fixes the
main defect of the earlier N11 chamber, where `g=e+w`.

The script constructs the actual four polynomial normals. It interpolates
`q_H` on the `w+1=32` anchor nodes rather than assuming `deg Q=w+1`.
Literal order-four contact re-evaluation is zero on all 44 agreement nodes.
The four normals have respectively 279, 280, 340, and 279 nonzero contact
rows outside agreement, so the test does not accidentally revert to a
globally contact-zero packet.

Every tested source monomial comes directly from the literal weighted
support. The script streams only the complete grade-at-most-six prefix and
the exact grade-seven pure/slope shell. It never builds an arbitrary
terminal column, localizes in `X`, or replaces the coupled contact map by a
pointwise proxy.

## Exact RED receipt

```text
complete source columns (audit only)         12,946
streamed prefix columns / exact rank          7,202 / 7,202
prefix packet quotient rank                       4
prefix F0,F1,F2,F3 residue supports          296,425,554,314
pure-plus-R shell columns / quotient rank      1,011 / 1,011
defects after adding entire pure-plus-R shell  (1,1,1,1), joint 4
```

Stable hashes:

```text
canonical result
  d9b82d21cfc26da4ef71bdb682ff1c9f2c8dc80d565e75aacb4a9d4b7c0a6882
streamed monomial list
  1eeef3956a7e7308e577e9a8de5a5ac596ab6a0c1d326714f6d77844ac6ddb80
script at execution
  eb93593f8c083bfeeecfc0190c40fdf2c41d332ec2cb37c4b6bee5ee1bd47cff
```

Runtime was 1,216.34 seconds. Peak RSS was 633,508 KiB under a hard
3,221,225,472-byte address-space limit.

## Relation to the F101 GREEN

Commit `5c33fa9` proves that in the smaller balanced chamber

```text
(N,g,e,w)=(11,8,3,5),  g-(e+w)=0,
```

the grade-`J` prefix plus raw pure and first-slope groups uniquely minimally
closes all four packets. Its exact F3 representative uses both shapes.

The present RED shows that result was not merely missing a formal uniformity
argument. Uniformity is false across the key degree wall. The source ranks
remain injective in both experiments, but the connecting class changes when
`deg Q=2e` exceeds `w+1` and `g<e+w`.

The independent pure-face fixed-boundary control at commit `94b183f` is also
RED (rank 270/270, target residue support 62; canonical hash begins
`77411a`, residue hash begins `a4a1e0`). Therefore this failure should not be
reinterpreted as a pure bivariate membership problem. If curvature closes
the F193 packet, it will be genuine translated derivative coupling.

## Target implication and next gate

Do not formalize or scale the 165-channel pure-plus-slope target ansatz from
the F101 GREEN. It lacks a true statement in the target chamber. Widening
the old individually-contact-zero bicovariant rectangle is also unsupported;
that ansatz was already exact RED by one in the targetlike N11 replay.

The narrow next discriminator is the same F193 prefix with the *complete*
first shell

```text
{(0,0),(1,0),(0,1)}.
```

There are only 425 additional curvature columns. If all three shapes close,
the target theorem candidate becomes a 247-channel polynomial connecting
map (83 pure, 82 slope, 82 curvature channels), still subject to target
width and passive-continuation proofs. If all three remain RED, first-shell
surjectivity itself is falsified in a ratio-faithful chamber and the route
must move to a higher shell or a genuinely different mapping-cone family.

The first attempt computed every redundant subset and hit its 30-minute
outer timeout after finishing source reduction. The committed code reuses
each base elimination, and `--decisive-only` performs just the required
binary test. This is a process correction only; it does not change the
literal columns or result.

