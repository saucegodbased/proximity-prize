# k=0 first-Newton two-bordered-minor cover

Date: 2026-09-14 UTC. Scope: lower-6900 research only. This is an exact
algebraic-closure certificate in one faithful full-cutoff chamber and a
target theorem reduction. It is not a target theorem, candidate, build, or
submission.

## Verdict

**GREEN for the first extra Newton slot in the exact-`g`, one-error k=0
chamber. OPEN for the target recurrence.**

For the literal relaxed second-jet source

```text
F_101,
(n,w,g,m,B,s,U,L,k,n0)=(5,2,4,3,3,1,4,6,0,1),
D=m*g=12,
```

normalize the selected polynomial and seed to zero, shear away the unique
degree-two interpolant on the anchors `0,1,2`, and write

```text
u0=(0,0,0,0,delta),       delta != 0,
u1=(0,0,0,a,b),           a != 0.
```

Here `a` is exactly the first extra Newton/divided-difference slot. The
unique agreement interpolant is

```text
Q_G(X)=a*X*(X-1)*(X-2)/6,
Q_G(4)=4*a.
```

The literal complete contact map has universal rank at most
`5*121=605`. Two fixed raw `609 x 609` minors of the contact matrix with the
four coefficientwise `Y,R,S,Z` boundary rows appended are

```text
D0 = -18*delta^22*a^17*(b-4*a)^22,

D1 =  15*delta^22*a^17
        *(b-48*a)^3*(b-47*a)^2*(b-32*a)*(b-30*a)
        *(b-3*a)^10*(b+23*a)*(b+25*a)*(b+37*a)^3.
```

Thus `D0` is nonzero whenever the error direction does not match the full
agreement interpolant. At the only missing point `b=Q_G(4)=4a`, `D1` is
nonzero. The minors have no common zero over the algebraic closure whenever
`a*delta != 0`; consequently the complete-kernel four-coordinate conormal
rank is four for every algebraic error direction `b`.

This is stronger than an exhaustive base-field rank grid. It is also a
different statement from the archived sub-full-cutoff three-normal fixed
minor: the cutoff is exactly `m*g`, the first Newton obstruction is literal,
all-node contact is present, and the appended border is the full `Y,R,S,Z`
four-jet.

## 1. Fixed rows and columns

Both charts use the same fixed set of 605 contact rows. Their deterministic
hash is

```text
e80527fd0cdcbbe0d140f6dafd242fd3c0c51af41301b51b8c9a167efee89bfb.
```

The four extra source columns are particularly informative:

```text
nonmatched chart D0:
  X*Y^3*Z,  Y^4,  X^10*R,  X^10*S;

matched chart D1:
    Y^3*Z,  Y^4,  X^10*R,  X^10*S.
```

Only the adjacent `Y^3 Z` / `X Y^3 Z` carrier changes. This is the first
fixed raw-minor evidence that the correct continuation object is an adjacent
Newton shift, not a large arbitrary error-cokernel surjectivity theorem.

The deterministic source-pivot hashes are

```text
D0: 68c97bf9774f344a19c6316b6713b2a9bdf0dfc5cf049608ae3e2ee586a3bf87
D1: ac84d8e9a93b6601a2bf76de51eb837812068b691ac5db49260a81a7c3adc5fc.
```

The complete augmented-column hashes are

```text
D0: 470ef8674c70be9e6a896bc1453980761d73f638a27d000549c12c84430e0f0a
D1: 82d8c26687325d042c0225da0b0482e35a3b717e2cbba1a1a7a897962be4c695.
```

These are fixed source-coordinate minors. No numerical nullspace basis or
piecewise RREF kernel lift appears in their definition.

## 2. Why the interpolation is an exact polynomial identity

For every literal contact entry, the degree in received-direction values is

```text
output seed exponent - source seed exponent.
```

After adding artificial seed weights `0,0,0,1` to the `Y,R,S,Z` boundary
rows, each raw determinant is homogeneous of total `(a,b)` degree `39`.
Therefore its dehomogenization at `a=1` has `b` degree at most 39. Forty exact
determinant values uniquely determine it over `F_101`; the executable also
checks an unused 41st value.

The passive centered-total grading gives, independently,

```text
source grade - target grade = exponent of u0.
```

After giving each boundary derivative row artificial total grade one, both
determinants have exact `delta` degree 22. The interpolated normalized
polynomials have degree 22 in `b`, so bihomogeneity supplies the remaining
factor `a^(39-22)=a^17`. Four direct non-normalized `(a,b,delta)` evaluations,
including the matched chart, recheck these homogeneous formulas.

## 3. What this says about the target proof

The exact-`g` wrapper is the right one. At every target cardinality one may
take `D=47*g`; the user-facing arithmetic audit shows all 81,732 exact
strata fit the allowance. Thus the maximal actual agreement set can be used,
every complement value residual is nonzero, and the fixed-cutoff
extra-agreement counterexample is irrelevant.

After choosing `w+1` anchors, badness says that some subsequent Newton slot
is nonzero. The agreement-side packet is already formal:

```text
F0,F1,F2,
F3 = Lambda_H^(m-1)*Lambda_(G\H)^m
       *(Y-P-(Z-gamma)q_H).
```

Its four-normal determinant is

```text
Lambda_G^(4m-3) * ((Q_G-q_H)/Lambda_H),
```

so the first nonzero Newton slot is exactly the fourth agreement pivot. The
new calculation says that, in the first faithful full-cutoff chamber, the
complete all-node lift needs only two adjacent raw carrier charts:

```text
error mismatch epsilon=b-Q_G(error) != 0:
  one bordered numerator is a unit times epsilon^22;

all error directions matched by Q_G:
  the adjacent carrier numerator remains nonzero.
```

The target-sized theorem should therefore be split, rather than asking for
surjectivity onto an enormous error quotient:

1. **Mismatch recurrence.** Order the errors and let the first nonzero
   `epsilon_i=u1(i)-Q_G(i)` be the pivot. Prove a raw bordered numerator from
   the adjacent `X*C,C` carrier pair is a unit times a positive power of
   `epsilon_i`, after earlier matched errors have been eliminated.
2. **Matched recurrence.** If every `epsilon_i=0`, use the adjacent unshifted
   carrier chart to lift the four exact agreement packets when `U1` is the
   single global degree-`<g` polynomial `Q_G`.

Both statements are only three/four-column projected continuation claims.
They are strictly weaker than terminal error-surjectivity, the stopped
43,528-dimensional cokernel fill, or fixed correction of every possible
agreement row.

## 4. Honest remaining gap and stop rule

This chamber does **not** prove either target recurrence. With 81,731 errors,
later error blocks can mix into the first raw minor, and the varying weighted
X windows must make the elimination triangular. The two formulas above do
not justify deleting those blocks, taking a product over nodes, or assuming
the same 605-row pivot pattern scales.

The next admissible progress on this lane is one of:

* prove the stripwise Hasse/Newton elimination making the first-mismatch
  bordered numerator triangular for arbitrary error count;
* prove the globally matched `Q_G` adjacent-carrier chart directly in the
  literal polynomial module; or
* give a ratio-faithful exact symbolic counterexample to one of those two
  statements.

Do not run another generic random rank scan. The useful invariant—the two
adjacent carrier columns and the mismatch/matched split—is already exposed.

## Reproduction

```text
prlimit --as=8589934592 --cpu=600 -- \
  python3 -B .experiments/k0_first_newton_two_bordered_cover_6900.py
```

The executable constructs the literal source and contact matrix, records the
fixed row/column selections, evaluates and factors both raw bordered minors,
checks the grading bounds and non-normalized formulas, and reports peak RSS.
It uses neither floating point nor random sampling.
