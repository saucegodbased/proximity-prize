# F101 grade-seven correction collapses to one centered covariant shell

Date: 2026-09-13 UTC. Scope: lower-6900 research only. This is an exact
finite mechanism certificate, not a target theorem, candidate, build, score,
or submission change.

## Verdict

The deterministic exact correction vectors that first close the three
locator borders in the faithful primary F101 chamber have 157, 157, and 158
nonzero coefficients in their new grade-seven shells. Those dense vectors
are not unstructured. For every one of `F0,F1,F2`, the complete new shell is
exactly

```text
V^2 Z^3 (c V^2 + C Lambda V Z + A Xi J1 Z),                 (COV)

V  = Y - Xi^2 Z,
V1 = R - 2 Xi Xi' Z = R - (Xi^2)' Z,
J1 = Lambda V1 - Lambda' V.
```

Here `Lambda` is the degree-eight agreement locator, `Xi` is the degree-three
error locator, and `A,C` and `c` depend on the prescribed locator normal.
Their degree bounds in this chamber are

```text
deg A <= 4,   deg C <= 6,   deg c = 0.
```

Thus the first successful passive shell is a three-term value/first-jet
covariant packet. It is not a broad collection of unrelated monomials. This
is the first exact finite evidence that identifies the derivative companion
missing from the previously formalized centered-shell unit.

## Exact derivation from all eight source shapes

The fixed chamber is

```text
F101,
(n,w,A,m,D,s,t,J,L)=(11,5,8,4,32,1,1,6,10),
G={0,...,7}, E={8,9,10}, P=gamma=0, Q=Xi_E^2.
```

For each prescribed normal, the script reconstructs the canonical contact
kernel correction used by the prior `L=J+1=7` bordered solve and groups only
its new grade-seven coefficients by `(Y,R,S,Z)` shape. In all three cases the
support has exactly the same eight shapes:

```text
(0,0,0,7), (1,0,0,6), (2,0,0,5), (3,0,0,4), (4,0,0,3),
(0,1,0,6), (1,1,0,5), (2,1,0,4).
```

There is no `S` shape. Treating the coefficient of each shape as a polynomial
in `X`, the three `R` coefficients satisfy the exact identities

```text
[R Z^6]       =  A Lambda Xi^5,
[Y R Z^5]     = -2 A Lambda Xi^3,
[Y^2 R Z^4]   =  A Lambda Xi.
```

They are therefore the single carrier

```text
A Lambda Xi R Z^4 (Y-Xi^2 Z)^2.
```

Changing the five pure coefficients from the `Y` basis to
`V=Y-Xi^2Z` gives coefficients `C_0,...,C_4`. Exact polynomial equality then
gives

```text
C_0 = 0,
C_1 = 0,
C_2 = -2 A Lambda Xi^2 Xi',
deg C_3 <= 14,
C_4 = c.
```

Combining `C_2` with the `R` carrier replaces `R` by the honest centered
first jet `V1`. Finally the remaining coefficient obeys

```text
C_3 + A Xi Lambda' = C Lambda
```

with zero remainder and `deg C<=6`. Substitution yields `(COV)` exactly.
Every displayed equality is asserted by exact `nmod_poly` arithmetic; it was
not inferred by visually matching factors.

There is a second cancellation directly relevant to the tapered pure-seed
strip. Put

```text
B0 = C_3 - c Q + 2 A Lambda Xi'.
```

For all three RHS, `deg B0=13` and the raw boundary-zero coefficient is
exactly

```text
[Z^7] = B0 (-Q)^(m-1).
```

The naively degree-14 centered coefficient therefore loses its top term only
after the value and derivative carriers are assembled. This is the coupled
head cancellation that a componentwise source-width audit would miss.

## Why this is the right contact shape

At an agreement root of `Lambda`, the leading contact term of `V` is its
centered first jet. The Wronskian combination

```text
J1 = Lambda V1 - Lambda' V
```

cancels that leading term and gains the next agreement-contact order. Hence
the three summands in `(COV)` have the intended order-four structure:

```text
c V^4 Z^3,
C Lambda V^3 Z^4,
A Xi J1 V^2 Z^4.
```

The shell can still leak to lower passive grades at error nodes, which is
exactly what is needed to cancel the earlier-shell residual in the
lower-triangular seed trellis. This reconciles the finite `J+1` closure with
the centered-shell/Hermite picture: the derivative companion is a locator
Wronskian, not an independent actuator with a fictitious scalar term.

## Target-shaped extrapolation and precise remaining gap

The literal degree-83 analogue for `(m,J)=(60,82)` has the form

```text
V^58 Z^23 (c V^2 + C Lambda V Z + A Xi J1 Z),
```

or equivalently the three shapes

```text
V^60 Z^23,
Lambda V^59 Z^24,
Xi J1 V^58 Z^24.
```

These respect the active-degree cap 82 and use only one explicit slope
carrier. That observation is structural, not yet a source-legality theorem.
The unresolved work is to derive the target-scale degree bounds for `A,C,c`
from the three prescribed normals, prove all cancellations inside each
literal weighted X strip, and iterate the corresponding Wronskian step across
the complete slope/curvature trellis through the load-bearing seed endpoint
2703. The finite canonical basis does not itself prove those statements.

The immediate proof target is now sharply smaller:

> Prove a one-shell Wronskian lifting lemma with shape-dependent X widths,
> then identify its iteration with the exact lower-triangular HPL transfer.

This replaces the vague search for 311 independent grade-seven columns and
also explains why the retracted pure actuator route failed: the needed
first-jet term is coupled to `V` by `J1`.

## Reproduction and immutable receipts

```text
prlimit --as=4294967296 python3 \
  .experiments/f101_grade7_correction_factor_probe_6900.py
```

The script first verifies contact rank/nullity `1735/39`, normal rank 12 on
the contact kernel, and the previously recorded whole-correction hashes:

```text
F0  support 1088  sha256 81cda...
F1  support 1115  sha256 ac1f...
F2  support 1523  sha256 aad0...
```

The full hashes remain in the machine-readable payload. Current compact
receipts are:

```text
script sha256
  20cd252f4fbd42601da2b85e5cc190143c32e0cee5ff2c54aeb30d029f02c568
canonical payload sha256
  2ca8a1f4edd0fde0b2c51b926087dbb0273d02b7e17d8f2c052951bf692cb7ee
generic Lean identity sha256
  ffa71adb7df0bc04b9a5c5a660abb641f4adbd9c1c2e98d2b3467830a81296c2
```

`F101Grade7CenteredCovariantShell6900.lean` proves both the Wronskian
assembly and the boundary-zero head cancellation over an arbitrary
commutative ring. Its capped build is green without `sorry`, `decide`, or
`native_decide`.

## Process guard

This result is worth promoting because it passed three independent gates:

1. it replays the exact successful bordered solve rather than a surrogate;
2. it asserts complete polynomial identities for all eight shell shapes; and
3. the same covariant form holds for all three required RHS.

It remains one finite-field chamber and the selected correction depends on a
canonical kernel basis. Do not call it `THREE-RHS`, do not change the score,
and do not submit until the uniform weighted-width recurrence is proved and
integrated with the literal Full187 source.
