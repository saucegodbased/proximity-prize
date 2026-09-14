# k=0 target-gated rank-defect adversary and first-Newton cover

Date: 2026-09-14 UTC. Scope: lower-6900 research only. This note records
exact finite-field counterexample searches and a two-bordered-minor
algebraic-closure certificate. It is not the target theorem, a candidate,
a build, or a submission.

## Verdict

**GO for the first Newton slot in a fully target-gated one-error chamber;
NARROW for the target recurrence. No high-degree rank defect was found.**

The earlier first-Newton cover used a faithful full-cutoff source, but its
small parameters did not satisfy the target terminal-strip hypotheses. The
new chamber does:

```text
(n,w,A,m,B,s,U,L,k,n0) = (5,2,4,4,2,1,7,7,0,1),
D = m*A = 16.

literal source columns                 1276
one-node relaxed contact rank           183
n times the local bound                  915
strict source margin                     361
B = 2*s                                  yes
U-B = m+1                                yes
closed-cap slack                           1
terminal raw width                         2
number of errors                            1
```

Thus the width is strictly larger than the complete error set. The contact
source is the actual relaxed promoted second-jet staircase:

```text
2*deg_S + deg_R <= B,
deg_S <= s,
deg_Y + deg_R + deg_S <= U,
deg_Y + deg_R + deg_S + deg_Z <= L,
deg_X + w*deg_Y + (w-1)*deg_R + (w-2)*deg_S < m*A.
```

It is not the older asymmetric toy box.

## 1. Complete normalized finite census

Over `F_7`, use agreement nodes `0,1,2,3`, error node `4`, and the standard
source-safe normalizations:

1. translate the selected seed and graph to `gamma=0`, `P=0`;
2. shear away the degree-two word determined on the first three agreement
   nodes; and
3. projectively normalize the first extra Newton discrepancy to one.

The normalized received data is then

```text
u0 = (0,0,0,0,delta),  delta in F7^*,
u1 = (0,0,0,1,b),      b in F7.
```

The executable exhausts all `6*7=42` remaining pairs. Every literal all-node
contact matrix has rank `915` and kernel dimension `361`. At both off-domain
points `X=5,6`, appending the four coefficientwise `(Y,R,S,Z)` boundary rows
raises rank by four. Therefore every case has conormal rank four over
`F_7(X)`. Three `a=0` controls have contact rank `907` and conormal rank
three, exactly as the legal degree-two pencil tangent predicts.

This is a complete census after the explicitly listed normalizations, not a
random sample.

## 2. Two fixed raw minors over the algebraic closure

The stronger calculation works over `F_101` without normalizing the two
nonzero quantities. Write

```text
u0 = (0,0,0,0,delta),       delta != 0,
u1 = (0,0,0,a,b),           a != 0.
```

Here `a` is literally the first extra Newton/divided-difference coordinate.
The unique agreement interpolant is

```text
Q_A(X) = a*X*(X-1)*(X-2)/6,
Q_A(4) = 4*a.
```

At the boundary specialization `X=5`, choose 915 fixed contact rows and add
the four boundary rows. Two deterministic raw `919 x 919` minors use the
same contact-row set. Their extra source columns are

```text
D0: X*Y^4*Z, Y^5, X^10*Y*R, X^15*S,
D1:   Y^4*Z, Y^5, X^10*Y*R, X^15*S.
```

Again only the adjacent `C, X*C` carrier changes. Exact passive gradings give

```text
total (a,b) degree = 74,
delta degree       = 44.
```

Seventy-five exact normalized determinant values therefore determine each
minor, and an unused 76th value checks the interpolation. The first factors
as

```text
D0 = 44 * delta^44 * a^36 * (b-4*a)^38.
```

Its only projective zero is the matched-error locus `b=Q_A(4)=4a`. The
second normalized determinant factors over `F_101` as

```text
39 * (b-3)^14
   * (b^2+69b+15)^3
   * (b^4+28b^3+9b^2+80b+21)^3
   * (b^6+80b^5+84b^4+34b^3+20b^2+67b+37),
```

and has value `72` at `b=4`. After homogenization its value on the matched
locus is `72*delta^44*a^74`, hence nonzero. Consequently the two raw minors
have no common zero over the **algebraic closure** whenever
`a*delta != 0`. This covers extension-field directions as well as the prime
field.

Since the old contact rows have rank at most `5*183=915`, a nonzero
`919 x 919` augmented minor forces old rank exactly 915 and boundary gain
exactly four. Thus this is an exact conormal-rank proof for the whole
one-error chamber, not merely a generic specialization.

The fixed selections are reproducible by hashes:

```text
common pivot rows:
  26f4d6b3fa41003e3a6e003cb95edde0714da61283a05cba2c6af6cb97b31738

D0 pivot columns:
  f554dfff81cef3e73d0c718e0c36abe05688e9351455899255c136b42fe17090
D0 augmented columns:
  34c472b749f71072ba392372c7bec39a49e9f266ad13ddb9a4a7ada623eef376

D1 pivot columns:
  f928f2a42602b96fb078473b614a5a9baa6c650a0c4ec16e038d842637e105e3
D1 augmented columns:
  ab1ade9ac8c91d9fce6ee21c409ba82ec2170d5af51446e402ace24b58a7aa0a
```

## 3. Adversarial variation and the rank-two branch

Two additional exact structured probes changed both the quotient dimension
and the `(w,A)` pair:

```text
F_11(X), (n,w,A,m,B,s,U,L)=(7,2,5,3,2,1,6,6):
  source 932, n*rank 679, margin 253;
  every projective class in the two-dimensional high-Newton quotient;
  continuation, zero, constant, and residual-coupled error directions;
  48/48 cases rank four.

F_11(X), (n,w,A,m,B,s,U,L)=(8,3,6,4,2,1,7,7):
  source 1851, n*rank 1464, margin 387;
  28 structured top-monomial/dense and error-coupled cases;
  28/28 cases rank four.
```

These latter probes are structured scouting, not exhaustive in all error
coordinates and not used in the algebraic-closure conclusion. Across all
`42+48+28=118` high-degree cases, the minimum observed conormal rank was
four. Hence no rank-two high-degree branch arose, and a quadratic escape is
not needed in any retained case found here. The only rank defects in the
complete census were the expected `a=0` low-degree controls, with rank three
rather than rank two.

## 4. What changed and what remains

This removes three plausible objections to the first-Newton mechanism:

* it is not an artifact of a source-negative chamber;
* it survives the target terminal-width and closed-cap conditions; and
* it is not a prime-field-only phenomenon, because the two-minor cover has
  no common algebraic zero.

It also identifies the same local architecture twice: split at the first
error mismatch `b-Q_A(4)`, and switch between adjacent `C` and `X*C`
carriers on the matched locus. This is stronger evidence for a triangular
first-mismatch recurrence than another generic rank scan would provide.

The target theorem is still open. With 81,731 errors one must prove that
ordered error elimination preserves a corresponding bordered numerator, or
construct its target analogue directly. A one-error factorization cannot be
multiplied across later blocks, and the tiny fixed pivot pattern cannot be
assumed at target scale. The next useful work is therefore:

1. derive the stripwise/Hasse recurrence for the first mismatching error;
2. show later error blocks act triangularly on the adjacent carrier pair;
3. handle the globally matched `U1=Q_A` branch with the unshifted chart; and
4. formalize the resulting rank-defect-to-first-Newton implication.

Decision: **GO** on this recurrence, **STOP** random rank scans, and **NARROW**
overall until the multi-error triangular identity is proved.

## Reproduction

```text
prlimit --as=8589934592 --cpu=600 -- \
  python3 -B .experiments/k0_rankdefect_adversary_6900.py

prlimit --as=8589934592 --cpu=600 -- \
  python3 -B .experiments/k0_target_gated_first_newton_cover_6900.py
```

The complete `F_7` census took about 33 seconds with peak parent/child RSS
below 84 MiB and stable canonical hash

```text
4070b2e6055f0c0663a05f571b87170904a2536422ecff65b7300e379fcb6e14.
```

The algebraic-closure replay took about 96 seconds with parent/child RSS
below 99 MiB and stable canonical hash

```text
415db8f592569580b1c772d039700c7e0fee24003a3f5a14e5690cca6ba70dfe.
```

Both executables use exact modular linear algebra. They use no random
sampling, floating point, `decide`, or `native_decide`.
