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
deliberately omitted from the first binary gate, and the earlier
arbitrary-error small controls made it the next semantically justified
family.

That terminal gate has now also run. The complete raw first shell
`{pure,R,S}` is **RED**: all 1,436 shell columns are independent modulo the
prefix, including all 425 curvature columns, but every packet still has
defect one and their joint defect is still four. Therefore the entire
first-shell connector architecture is stopped in this target-ratio chamber.

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

### Complete first-shell STOP receipt

The same artifact was then invoked with `--full-shell-only`, changing no
field, packet, prefix, contact map, or source policy:

```text
prefix columns / rank                          7,202 / 7,202
full pure+S+R shell columns / quotient rank    1,436 / 1,436
verified pure+R quotient rank                  1,011
marginal rank supplied by all S columns          425
F0,F1,F2,F3 defects after complete shell       (1,1,1,1)
joint packet defect                                4
```

Stable full-shell fingerprints are:

```text
canonical result
  c7d6c92b4c272a81b0a7e5267d8ebbefdb06984a1db8c0830ce30a4f6491cdf5
streamed monomial list
  2f5406e17e6dc8157ad7f632498de34d0985dbb42ceb091bcb5e6a66de996c70
script at execution
  ff7f49b80029c95353182752d18ea218a4542b30c444dca4178a8bc76bdd1c25
```

Runtime was 1,571.33 seconds and peak RSS was 691,668 KiB under the same
hard 3 GiB address-space cap. Curvature therefore contributes its full
source quotient dimension without contributing even one of the four missing
packet directions. This is stronger than a simple capacity failure.

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

## Target implication and architecture STOP

Do not formalize or scale the 165-channel pure-plus-slope target ansatz from
the F101 GREEN. It lacks a true statement in the target chamber. Widening
the old individually-contact-zero bicovariant rectangle is also unsupported;
that ansatz was already exact RED by one in the targetlike N11 replay.

The complete first-shell test is now RED. Do not spend more time adding
coefficient shifts, centered carriers, or derivative shapes within that
shell. The failure is not insufficient source rank: the entire shell is
independent, and the four packet classes stay transverse to it.

This finite RED does not prove Full187 impossible and does not logically
exclude a higher source shell. It does decisively remove the only
low-state first-shell extrapolation supported by the balanced small
chambers. A return to this route would require a new theorem explaining why
the actual target differs from the ratio-faithful chamber, not another
rectangle or shell-group computation. The active search should pivot to a
genuinely different mapping-cone/cross-slope mechanism.

The first attempt computed every redundant subset and hit its 30-minute
outer timeout after finishing source reduction. The committed code reuses
each base elimination, and `--decisive-only` performs just the required
binary test. This is a process correction only; it does not change the
literal columns or result.

## Frozen survivors and the bounded grade-eight diagnostic

A final single-pass replay used `--survivors-and-next-shell`. It rebuilt the
same exact prefix and full first-shell echelon once, emitted the complete
deterministic survivor vectors, and then reused that live state for one
grade-`J+2=8` diagnostic. It did not widen the source shapes or perform a
second parameter search.

The four full-first-shell survivor vectors have exact support sizes

```text
(F0,F1,F2,F3) = (296,425,554,314)
```

and hashes

```text
F0  4e70d88683320b60e8ce98f590d30fc9e00e6904ebf4d518217878c00d4cd87d
F1  fb0fcddba6a75ae7af6a1c60ab1d5932671782a968d80ea48105ea911e7b4278
F2  24878991ab92edaef5917f96287b588e2ea7fd23a720bd54a8daa78db8e7f278
F3  2d2f78e61aae834e9369462753fcb30d041e2475359ec8b122d89f8110093780
```

The executable JSON includes every row and coefficient, not merely these
hashes. A deterministic four-coordinate quotient chart is supported on the
boundary rows

```text
(J,0,3), (J,0,2), (J,0,1), (J,0,4).
```

The packet columns in that chart are

```text
F0 = (69,  0,   0,173)
F1 = (91,124,   0, 27)
F2 = (164,11, 138, 12)
F3 = (72,  0,   0,191),
```

of exact rank four.

Streaming every legal grade-eight column through the already-built prefix
and first-shell echelons gives the following ranks on those four quotient
coordinates:

| grade-eight shape | columns | nonzero projected columns | four-channel rank |
|---|---:|---:|---:|
| pure `(0,0)` | 591 | 415 | 3 |
| curvature `(0,1)` | 425 | 278 | **4** |
| slope `(1,0)` | 420 | 274 | 3 |

The unique inclusion-minimal shape family with rank four is curvature alone.
Exact projected-column hashes are respectively

```text
pure  3c15240a7414b7c7246a5d556403b0eb8dd4cb3904eb50053beef3e2ced897e8
S     2c7d05de5a2f1313fe613337e34924b53cf9f76c1834943a7fe9096d472d3a40
R     0a2c94ed11245622b70b306da5725787bab27804439a7abb9e47239db8692ccf
```

The grade-eight monomial-list hash is
`a488a7edde7086950c9073dfb3b871dfa695f4971a8b96ef3145ab881b311d9d`.
The combined run used 692,752 KiB peak RSS in 2,150.56 seconds under the
hard 3 GiB cap. Its canonical result hash is
`824499b0ec91399c4d5a54aa9d59548d16fccbe6b89130fa2ba8c5cd103c9816`.

This is deliberately **not** reported as a grade-eight lift. The four row
coordinates are quotient-linear functionals and full projected rank is a
necessary directional signal; grade-eight columns can retain other quotient
components, so the test does not prove the packet lies in their span. Nor is
the action symbolic or coefficient-independent: it is one exact F193
instance. Commits `f8560b5` and `49afff4` independently show that the target
instance's `u1` rank cannot be promoted as a universal law. The compiled
universal high branch begins only at `deg U1 >= 133120` via
`WeightedScalarList133119` (not 132103).

Consequently the curvature rank-four hit is preserved only as finite-control
evidence. The smallest local falsifier would be exact grade-eight-curvature
containment after the frozen first shell, but it is not a justified Full187
scaling route without a new symbolic, coefficient-independent mechanism.
This task stops here rather than turning that numerical projection into a
new rabbit hole.
