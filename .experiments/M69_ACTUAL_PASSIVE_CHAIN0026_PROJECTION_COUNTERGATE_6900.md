# Actual m69 passive chain `(0,0,26)`: source-direction countergate

Date: 2026-09-14 UTC. Scope: lower-6900 source attachment audit only.
Production, score, radius, candidate, and submission roots are unchanged.

## Exact result

`M69ActualPassiveChain0026ProjectionCountergate6900.lean` starts at the
literal m69 caller

```text
globalPassiveArrayConstraint
  K I 69 (69*180413) 131071 94 24 10 2369
  (94 <= 2369) nodes values0 values1.
```

The file proves its node-value equation definitionally from
`localPassiveArrayConstraint_value`, then unfolds one genuine
`passiveColumnTerm`.  On the top passive diagonal `g=k-row`, its scalar is

```text
choose(k,row) * values1(i)^(k-row).
```

The residual `values0` exponent is zero.  Therefore the literal Pascal
direction is **the actual second received coordinate `values1`**, not
`values0`, and not an independently inserted leaf wedge `N0/E0`.

For total passive grade 2369 the same term always lands at outer seed
`2369-row`.  In particular, the file gives exact compiled formulas for the
terminal source coefficient

```text
Y^94 * seed^2275
```

in rows 41 and 42, with powers `values1^53` and `values1^52`.  The direct
contacts `k=41,...,68` are instances of the compiled generic theorem.  It
also proves that already the adjacent `k=42 -> row=41` column forces any
replacement direction `W` to equal `values1` whenever the binomial diagonal
42 is nonzero.

## What is and is not projected

There is a canonical physical scalar coefficient of the target seed
polynomial at any chosen monomial.  But the existing m69 caller exposes only
the concrete submodule

```text
passiveTargetSpan K 69 94 24 10 2369
```

and no existing definition splits it into tagged `(r,s,q)` associated
summands or constructs the boundary-dual map used by the rational
confluence experiments.  The formal result here consequently proves the
literal source-column formula, not a nonexistent quotient decomposition.

The intended physical coefficient for q26 is the coefficient of
`Z^26 * contactY^row` at outer seed `2369-row`.  Expanding a source monomial
shows why the max-seed diagonal is promising: if it contributes there, then

```text
z + g = 2369-row,
z + y <= 2369,
g <= y-row,
```

so all three inequalities are equalities: `z+y=2369` and `g=y-row`.  Thus
the outer seed does isolate the top passive diagonal.  However, the exact
coefficient theorem through `seedContactTruncation`, including the q26
Hasse coefficient in the translated X polynomial and its terminal/lower
split, has not been formalized in the current caller.  It must be supplied
before this can feed a cokernel or four-boundary consumer.

## Binary verdict

```text
GREEN: real global caller and node equation;
GREEN: literal direct/terminal top-diagonal source columns;
GREEN: Pascal direction is values1;
RED:   substituting the leaf wedge N0/E0 without a new transform;
OPEN:  full physical q26 coefficient extraction and lower/terminal split;
RED:   any claim that the current abstract confluence module is attached.
```

This kills the present rational-wedge attachment, not the actual-factor
source architecture.  No leaf assumption or 6900 claim is made.

## Verification

The Lean file compiles with one Lean thread under a 5 GB local cap.  Every
printed theorem uses only the standard accepted axioms `propext`,
`Classical.choice`, and `Quot.sound`.  It contains no `sorry`, `admit`,
`decide`, `native_decide`, unsafe declaration, or generated table.
