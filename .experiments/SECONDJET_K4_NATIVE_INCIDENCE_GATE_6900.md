# Native k=4 second-jet incidence gate for lower 6900

Date: 2026-09-14 UTC.  This is a source/consumer feasibility gate, not a
candidate or a submission.

## Result

There is a numerically viable route that does not ask a moving P5 family to
produce one fixed P4 carrier.  Use the target-positive second-jet profile

```text
(m,B,s,U,L,k,n0) = (148,64,30,200,5465,4,5)
source-minus-rank margin = +3,553,593,355.
```

Let `V` be its actual global contact kernel.  For a selected polynomial
`f` and seed `z`, the existing derivative/root-count theorem gives

```text
specialize f z ((pderiv S)^4 Q) = 0
```

for every `Q in V`.  Thus all candidates are common zeros, over `K(X)`, of
the fixed derivative-image `D4(V)` in the four coordinates `(S,Y,R,Z)`.
This reverses neither a diagonal quantifier nor a seed specialization: the
P5 rows are fixed before the selected candidates are ranged over.

Four curvature derivatives lower the ordinary active cap from `200` to
`196` and the total/seed cap from `5465` to `5461`.  At `(J,L)=(196,5461)`,
the existing conservative 52-chart consumer has exact values

```text
active projection cap       1,910,696,592 < 2,130,706,433
inactive projection cap     1,978,462,416 < 2,130,706,433
active chart cost           1,246,845,984,384
inactive chart cost         1,291,119,656,064
all 52 charts                  65,013,085,874,688
MCA allowance          254,684,620,614,660,120.
```

Unlike Full187, this is one global candidate-major incidence problem, so no
factor `81,732` for exact-agreement strata appears.  The complete chart cost
uses only about `0.0256%` of the allowance.  Hence arithmetic and
characteristic headroom are not the obstruction.

## Retraction of the order-15 tangent proposal

The first focus pass proposed ordinary gradient rank four. A subsequent
version of this note incorrectly replaced it by an order-15 osculating
condition. On an agreement set, interpolate the received direction `u1` by
a polynomial `h` of degree at most `A-1`; then

```text
v = (h'',h,h',1)
```

is the formal motion `(f,z) -> (f+t*h,z+t)` preserving the agreement values.
For `W=D4(Q)`, its specialization degree is strictly below `(m-4)*A`, since

```text
4*(A-w+2) + 4*(w-2) = 4*A.
```

This identity has already spent all four units of contact: `W` has contact
only `m-4`, not `m`. There is consequently only the strict one-degree slack
below `(m-4)A`. Each directional replacement costs at most
`A-w-1=49,341` in X degree, so the first directional coefficient is already
outside the root-count range. The literal target-legal endpoint

```text
X^((m-4)A-1) * S^4
```

shows that the degree envelope is sharp. The earlier expression
`4*A-14*(A-w-1)` subtracted the four-contact loss when constructing `W` and
then incorrectly reused the same `4*A` as fresh tangent slack. The first
root-count-unforced order is `1`, not `15`.

When `degree h <= w`, the motion is a legal polynomial pencil and its first
coefficient genuinely annihilates the conormal. When `degree h > w`, tangent
annihilation is not forced. This is exactly the distinction in the archived
Global-O2 audits.

## Actual load-bearing theorem

The route is therefore conditional on a rank-defect recovery statement about
the *actual* derivative image:

```text
for every retained selected (f,z),
  rank over K(X) of grad_(S,Y,R,Z)(D4(V)) < 4
    implies that u1 on its agreement set has an interpolant
    h of degree <= w.
```

On the retained/non-pencil branch this gives ordinary pointwise rank four,
which permits the regular-Jacobian consumer. A weaker acceptable output is a
rank-deficient component theorem whose candidates have a separately paid
cover. Kernel dimension `3,553,593,355` by itself proves neither form: a
large kernel can consist of multiples of a common differential factor, and
a faithful small chamber in the companion discriminator has `D4(V)=0`
despite kernel dimension `339`.

The remaining formal consumer join is the already identified Fin4
component/aggregate-degree producer. Rank four does not magically
instantiate `AggregateDenseBlockBezoutOutput`; the source-to-minimal-component
cover still has to be constructed honestly.

## Immediate discriminator and stop rule

The companion executable
`secondjet_candidate_major_function_field_rank_gate_6900.py` finds a
faithful small chamber in which the complete D4 image is zero. This does not
falsify target-specific noncollapse, but it kills any inference from total
kernel dimension alone. It also checks the sharper zero-reserve source:
low-degree tangents have exact rank three and twelve high-degree tangents
have rank four. That behavior reproduces, rather than solves, the archived
Global-O2 rank-defect-recovery blocker. Do not run more random grids; the next
useful unit must be a symbolic recovery theorem or a target derivative-image
lower bound.

Do not fall back to top-curvature coefficient extraction.  Commit `47180ac`
gives a kernel-checked Full187 counterexample and an exact `49,344*d`
root-forcing deficit for that operation.

## Formal arithmetic receipt

`SecondJetK4NativeIncidenceArithmetic6900.lean` compiles with an 8 GB Lean
allocator cap and prints only `[propext, Classical.choice, Quot.sound]`.  It
contains no `sorry`, `decide`, or `native_decide`.
