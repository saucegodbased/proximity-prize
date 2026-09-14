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

## Exact load-bearing theorem

The route is conditional on a new statement about the *actual* contact
kernel.  The strongest convenient form is

```text
for every retained selected (f,z),
  rank over K(X) of
    Q in V |-> grad_(S,Y,R,Z) (D4 Q)(f'',f,f',z)
  is 4.
```

Pointwise rank four permits simultaneous generic row selection after base
change and makes every selected graph point regular/isolated for four fixed
rows.  A weaker acceptable output is a rank-deficient component theorem
whose exceptional candidates have a separately paid cover.  Kernel
dimension `3,553,593,355` by itself proves neither form: a large kernel can
consist of multiples of a common differential factor.

The remaining formal consumer join is the already identified Fin4
component/aggregate-degree producer.  Rank four makes that join simpler but
does not magically instantiate `AggregateDenseBlockBezoutOutput`; the
source-to-minimal-component cover still has to be constructed honestly.

## Immediate discriminator and stop rule

Before building wrappers, compute the displayed derivative-gradient rank on
faithful small second-jet contact kernels with actual selected graphs.  A
rank-three-or-less chamber which preserves the derivative/root-count
interface kills universal pointwise rank four and forces the component
branch.  A collection of generic random rank-four samples is only evidence;
it does not prove the target theorem.

Do not fall back to top-curvature coefficient extraction.  Commit `47180ac`
gives a kernel-checked Full187 counterexample and an exact `49,344*d`
root-forcing deficit for that operation.

## Formal arithmetic receipt

`SecondJetK4NativeIncidenceArithmetic6900.lean` compiles with an 8 GB Lean
allocator cap and prints only `[propext, Classical.choice, Quot.sound]`.  It
contains no `sorry`, `decide`, or `native_decide`.

