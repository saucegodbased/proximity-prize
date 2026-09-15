# K0 low-head rank-three splice: projection RED, first carrier equation

Date: 2026-09-15 UTC. Scope: lower-6900 target connection. No candidate or
submission is changed.

## Verdict

Route F cannot currently reduce the corrected low-head problem from four
rows to one. There is no target-literal theorem saying that the kernel of
the old `epsilon^0,...,epsilon^43` head covers a boundary hyperplane.

Two pieces of earlier evidence were easy to conflate:

- the exact rank-three boundary image is for the m8 **complete-contact**
  kernel, hence is finite evidence only;
- `K0HeadKernelThreeAxes6900` puts pure `S,R,Z` in the kernel of the opposite
  projection, `epsilon^3,...,epsilon^46`.

The latter does not splice into the final-three detector, whose complementary
head is `epsilon<44`.

## Literal target countergate

`K0LowHeadRankThreeSpliceRed6900.lean` constructs the actual dependent raw
index for pure `S` inside `K0RawSource K 180413` and proves

```text
targetLowHead(x,u0,u1)(rawBasis pureSIndex) = C(S) != 0.
```

Therefore this source vector is not in the kernel of even one corrected
low-head block, let alone the all-node low head. This is a direct computation
through raw reconstruction, localization, flattening, contact, m47
truncation, and head44 truncation. It decisively invalidates reuse of the
known pure-axis trio for route F.

This does not prove that the target low-head kernel has boundary rank below
three; it proves that no existing rank-three result establishes otherwise.
The formal file names the exact conditional premises:

```text
TargetRankThreeHyperplane:
  every b with ell(b)=0 is realized on ker(oldLowHead)

TargetOneSyndrome:
  some v in ker(oldLowHead) has ell(freshBoundary(v)) != 0.
```

Only after the first is proved does the second become “the one remaining
syndrome.” The coordinate-free rank-three-plus-one consumer is proved in the
same file.

## Four osculating carriers: first error equation

The minimal agreement-side candidates remain worth testing as a four-row
construction:

```text
H^43 A,  H^42 B1,  H^41 B2,  H^44 W,
```

where `H` is the agreement locator, `W=Z-gamma`, and

```text
A  = Y-P-WQ,
B1 = H*RG-H'*A,
B2 = H^2*SG-2HH'*RG+(2(H')^2-HH'')*A.
```

At an error `beta`, put `h=H(beta)`, which is nonzero, and let `delta` be the
nonzero value mismatch (the constant coefficient of `A`). In rows
`(1,R,S,W)`, the epsilon-zero coefficient matrix is triangular. Its diagonal
is

```text
h^43*delta,  h^43,  2*h^43,  h^44,
```

so its determinant is

```text
2 * delta * h^173.
```

Over the target characteristic this is nonzero. The Lean theorem
`error_epsZero_four_carriers_forced_zero` proves the equivalent elimination
statement over any field under explicit `2!=0`, `delta!=0`, `h!=0`
hypotheses. Thus no nonzero scalar combination of the four bare carriers
kills even the epsilon-zero contact at one error. Error-side correction is
not optional; it starts with four independently prescribed values.

## Taper result: first step GREEN, full schedule OPEN

One degree-`<e` error-value interpolant on each first equation is legal. Lean
checks, with `g=180413`, `e=81731`, `w=131071`, `D=47g`,

```text
43g+w+e     < D,
43g+(w-1)+e < D,
43g+(w-2)+e < D,
44g+e       < D.
```

So there is no first-step taper failure. This is a useful positive result:
the four error epsilon-zero residuals can in principle be cancelled by the
existing value-CRT primitive.

It is not yet a 44-layer recurrence. Higher epsilon coefficients contain
Hasse derivatives of those four interpolants plus contact terms from the
new corrections. A valid schedule must prove triangularity and stay below
the two already formal cliffs:

```text
q=14 plus error values does not fit on S*R*Y^43;
q=1  plus error values does not fit on Y^64.
```

The present audit does not claim every schedule necessarily hits either
cliff. It says exactly what must be derived next: a shape-by-shape recurrence
that reduces the higher-order residual before it requests those illegal
grades. A bare appeal to `q*g+e` or to source dimension is insufficient.

## Decision

- **STOP route F as an ASAP shortcut:** its rank-three premise is absent and
  the only proposed three axes use the wrong projection.
- **GO one step on the four-carrier recurrence:** the agreement orders and
  first error-value corrections fit, and the first error matrix is explicitly
  nonsingular.
- **Next binary gate:** write the epsilon-one correction equation after the
  four value interpolants. If its residual can be assigned to a source-legal
  next shape without moving toward `q14/SRY43` or `q1/Y64`, continue; otherwise
  freeze the four-carrier path as RED.

## Verification

The Lean file compiles under the 8-GiB capped runner in about eight seconds.
Printed axioms are only `propext`, `Classical.choice`, and `Quot.sound`; there
is no `sorry`, `decide`, or `native_decide`.
