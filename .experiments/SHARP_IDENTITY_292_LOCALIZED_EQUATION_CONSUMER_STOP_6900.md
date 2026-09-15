# Sharp identity-292 localized-equation consumer: bounded three-angle STOP

Date: 2026-09-15 UTC. Lower 6900 only. No literature and no production edit.

## Verdict

**STOP for treating the 30635 localized shifts, by themselves, as a new
independent constraint.**  All three bounded checks are red:

1. Dual-rank: even two completely independent 30635-row blocks leave an
   automatic 20462-dimensional kernel in the original 81732-coefficient
   recurrence box.
2. Same-family intersection: the strongest optimistic low-degree extraction
   improves a derived locator residual to 51673, but does not improve the
   literal pair-intersection cap `W <= 149485`; its best Johnson gap is still
   negative by 6594095651.
3. Abstract-equation countergate: for every field and every two-block linear
   test map with this exact shape, kernel dimension at least 20462 is forced
   solely by dimensions.  The inherited dimension 7459 is smaller by 13003.

Thus the recurrence-localization gate remains a useful exact transport, but
not a 6900 count.  A continuation must prove transversality/nonzero projection
of the **specified original recurrence subspace** using target-size incidence.

## 1. Dual recurrence rank

The hard branch gives the grade and shift ledger

```text
original recurrence coefficient box = 81732
shifts after E0 and Z-complement      = 30635
number of original/Frobenius blocks  = 2
maximum test rank                     = 2*30635 = 61270
automatic nullity                     = 81732-61270 = 20462.
```

The new theorem

```text
arbitrary_two_block_localized_kernel_finrank_ge
```

proves this for an arbitrary linear map

```text
degreeLT K 81732 -> Fin 2 -> Fin 30635 -> K.
```

It assumes no dependence among rows; all 61270 may be independent.  One block
alone has automatic nullity 51097.  Consequently merely finding a nonzero
localized recurrence, or even a 7459-dimensional family of them, creates no
rank deficit.  The latter is 13003 dimensions below the unavoidable
two-block nullity.

This does not say a particular 7459-plane is automatically contained in the
kernel.  That containment could be meaningful if the plane were fixed
independently.  In the actual producer it is not: the original recurrence
space is built from the same received rows, hence from the same centre after
the identity substitution.  A useful theorem must exploit that correlation
and prove it transverse, rather than count rows and columns again.

## 2. Strongest optimistic same-family factorization

Grant every mechanical bridge which is favorable to this route.

* From a 7459-dimensional subspace of polynomials of degree at most 81731,
  cancel its top 7458 coefficient coordinates.  This leaves a nonzero
  polynomial of actual degree at most

  ```text
  81731-(7459-1)=74273.
  ```

  It still has only the recurrence shifts exported at declared grade 81731;
  no false descent to `recurrenceSpace ... 74273` is used.
* The sharp package gives

  ```text
  deg Q + max(deg c,deg d) <= 8328.
  ```

  Thus the post-substitution centre multiplier can have degree at most

  ```text
  74273+8328=82601.
  ```
* The 30635 punctured nodal syndromes optimistically give a numerator of
  degree at most `|Z|-30636 <= 231508`.
* The scalar polynomial has degree at most 149485.  Therefore

  ```text
  deg(T*B_gamma-C) <= max(82601+149485,231508)=232086.
  ```

  Dividing its 180413 agreement roots leaves residual degree at most

  ```text
  232086-180413=51673.
  ```

This is a real improvement over the original 81730 agreement residual and is
worth retaining as a possible input to a genuinely new cross-candidate
theorem.  It does not improve ordinary support intersections.  Two scalar
polynomials still agree with the unchanged centre on an intersection, so
their nonzero difference has degree at most `W`.  Multiplying both by the
same `T` and subtracting `C` cannot lower that degree cap.  At the smallest
hard-branch universe and largest W,

```text
261852*149485 - 180413^2 = 6594095651 > 0.
```

Thus pair Johnson remains decisively red.  The small residuals occur beside
different large locators; no existing theorem converts their degree 51673
into a smaller common-intersection cap or a count below 875068543039973.

## 3. Abstract 30635-equation countergate

The two-block finrank theorem is also the requested abstract countermodel.
For any field and any 61270 linear equations on the original recurrence
coefficient box, the solution space has dimension at least 20462.  This
includes equations formed by multiplying by a fixed nonzero factor before
testing a centre word: multiplication is simply part of the linear test map.

Therefore an interface exporting only

```text
30635 shifts per block
+ a nonzero multiplier
+ inherited nullity at least 7459
```

cannot distinguish the target centre from an arbitrary centre.  Exact
same-family incidence must enter through an additional property of the
specified 7459-plane—e.g. a nonzero quotient projection, a transverse image,
or a shared factor/resultant theorem—not through raw equation count.

## Falsifiable GO condition

Reopen this route only with a theorem of the following shape:

```text
for the exact sharp leaf and |Z^c|<=292,
the image of the actual original recurrence space under identity-core
substitution has a target-incidence-controlled transverse/nonzero component
which cannot occur in the automatic 20462-dimensional kernel.
```

For the residual-51673 variant, the substitute GO condition is an exact
cross-candidate theorem which consumes the fixed `T,C`, the varying split
locators, and residual degree 51673 to produce a count at most
875068543039973.  A pair-intersection or ordinary Johnson argument cannot do
so.

## Verification

New module:

```text
.experiments/SharpIdentity292LocalizedEquationRankStop6900.lean
```

It compiles under the 3.5 GiB allocator cap in about 2.9 seconds.  Printed
axioms are only `propext`, `Classical.choice`, and `Quot.sound` (the numerical
ledger itself needs only `propext`).  It contains no `sorry`, `admit`,
`native_decide`, or `unsafe` declaration.

