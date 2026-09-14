# m47 filtered CRT/Groebner dual gate

Date: 2026-09-14 UTC. Scope: lower 6900, full m47 source only. This is a
structural proof/STOP audit, not a candidate or a submission edit.

## Verdict

There is a clean and now Lean-formal **univariate description of every
isolated weighted-shape cokernel**. If the pole polynomial `A` is monic of
degree `M`, a raw shape has strict X window `M-c`, and its node/contact
multiplier is `U`, then a quotient numerator `g` annihilates that whole strip
exactly when

```text
r = (g U) mod A

r = 0  or  deg r < c.                              (CW_c)
```

At cost zero, testing the full window forces `r=0`. This uses the perfect
top-coefficient pairing on `K[X]/(A)` and an explicit multiplication/reduction
identity. It does not infer rank from dimensions and does not select a matrix
minor.

For the live m47 weighted source,

```text
c(y,r,s) = 131071 y + 131070 r + 131069 s
         = 131069(y+r+s) + 2y+r.
```

Every legal active shape `y+r+s<=64` has

```text
0 < c(y,r,s) < 47g                         when g>=180413,
47*180413 - 131071*64 = 90867.
```

Thus every isolated nonconstant shape leaves only a low-degree reduced
numerator, while the constant active shape leaves none.

This is **not yet DUAL0**. The full literal staircase does not decompose into
independent shape strips. The exact missing theorem is the construction of
those isolated strip equations from the coupled raw `Y/R/S/Z` source. A
generic module/CRT projection argument cannot supply it: exact controls show
that the bounded source image is not X-stable and is not stable under CRT
idempotents. Individual PC terms are triangular, but cancellation among
diagonal columns can have a lower tail outside the earlier image.

The honest status is therefore:

```text
local weighted initial staircase                         GREEN
CRT/Hasse representation of an arbitrary contact dual    GREEN
isolated tapered-shape cokernel = degree-<cost remainder  GREEN (formal)
zero-cost full-window dual numerator = 0                 GREEN (formal)
full raw weighted staircase is a quotient module         RED (exact control)
individual-term order implies global elimination         RED (exact control)
target-ratio faithful finite CS4 control                  GREEN evidence only
boundary-compatible dual -> low-degree bad interpolant   OPEN
```

## 1. The genuine local Groebner/initial-ideal structure

At node `i`, put

```text
epsilon = X-x_i,
E       = Y-u0_i-u1_i Z-epsilon R+epsilon^2 S/2.
```

The order-two contact truncation retains exactly the local standard
monomials

```text
epsilon^a E^b,                 a+3b < 47,
```

with `R,S,Z` carried as coefficient/passive coordinates subject to the
literal finite caps. Equivalently, the local monomial initial ideal contains
the weighted monomials `epsilon^a E^b` with `a+3b>=47`. This is the correct
local staircase and gives explicit reversed-Hasse intervals for every
contact shape. Distinct nodes are then separated by the coprime factors
`(X-x_i)^depth_i`.

The following existing artifacts already formalize the two ingredients on
the two sides of that statement:

* `Order2SourceBasisScaffold.lean` formalizes the contact substitution and
  the strict `epsilon+3E` truncation.
* `HrsCrtPairingBridge6900.lean` formalizes variable-depth Hasse CRT and
  represents every nodewise jet dual by a unique global quotient numerator.

The accepted `SecondJetWeightedBasis.weightedTerm` must **not** be used as
the raw monomial basis here. It is an explicit local contact-kernel family.
`K0WeightedRawAdjointRecurrence6900.lean` proves that its complete-contact
pairing is identically zero and identifies
`SecondJetRelaxedGlobalIndex.exponent` as the actual raw global basis. The
existing `SecondJetRelaxedRank.local_rank_bound` uses the weighted kernel
family to prove rank capacity; it does not turn `weightedTerm_coeff_self`
into a dual moment or prove quotient surjectivity.

## 2. Exact per-shape cokernel theorem

Use the Frobenius pairing

```text
<g,p>_A = coeff_(M-1) ((g p) mod A).
```

For monic `A` of degree `M>0`, every reduced product

```text
r = (g U) mod A
```

has degree `<M`. The already formal multiplication transport is

```text
<r,p>_A = <g,U p>_A.
```

The complementary-window theorem says that a reduced `r` annihilates all
`p` of degree `<W`, for `W<M`, iff

```text
r=0 or deg r < M-W.
```

Putting `W=M-c` proves `(CW_c)` exactly. The endpoint `c=0` is handled by
injectivity/perfectness of the full quotient pairing; no convention about
`natDegree 0` is used to fake a degree-`<0` statement.

Formal artifact:

```text
.experiments/K0FilteredCrtGroebnerDual6900.lean

natDegree_reduced_mul_lt
annihilates_multiplier_window_iff_complementary
annihilates_cost_window_iff_remainder_below_cost
annihilates_full_multiplier_window_iff_remainder_zero
m47_active_shape_cokernel
m47_constant_shape_dual_zero
```

The printed axiom set is exactly

```text
propext, Classical.choice, Quot.sound.
```

There is no `decide`, `native_decide`, generated table, or finite rank
oracle in this proof.

## 3. Why this does not make the full source mechanical

A global raw column `X^a Y^y R^r S^s Z^z` does not land in only one local
shape. Expanding `Y` through the displayed contact coordinate produces the
PC triangle indexed by contact factors, `u0` factors, `u1 Z` factors, and
the `E/R/S` choices. The diagonal term has coefficient one and every
individual off-diagonal term is earlier in the intrinsic key

```text
(PC grade increasing,
 seed decreasing,
 shifted contact weight decreasing,
 reversed-Hasse index decreasing).
```

`HrsU0PCInteriorOrdering6900.lean` proves this local order theorem. But a
term order is not a global source-legal elimination algorithm. A relation
among several diagonal columns can cancel their unit pivots while leaving a
lower PC tail not generated by earlier legal columns. In block notation the
needed confluence condition is

```text
B_d(ker A_d) <= image C_d.                           (CONF_d)
```

The exact complete F101 control in
`LITERAL_PC_DEPENDENCY_DAG_WINDOW_GATE_6900.md` has, at the first nontrivial
grade,

```text
dim ker A_2 = 9,
rank image C_2 = 185,
confluence defect = 2.
```

So individual triangularity does not imply `(CONF_d)`. The same audit finds
the target pure-Y `u1` edge landing in an earlier polynomial window smaller
than the 262144-node domain. Removing that edge requires a real bounded
interpolation identity, not merely a reordering.

There is an independent, sharper module-law countercontrol in
`F101_O2_ARTIN_TRACE_BEZOUT_STOP_6900.md`:

```text
rank C                    = 2560,
rank [C | X C]            = 2566,   X-stability defect 6,
rank after CRT split hull = 2574,   CRT split defect 14.
```

Hence the whole bounded source image is not a
`K[X]/(product_i (X-x_i)^m)`-submodule, and ambient CRT idempotents do not
preserve the source taper. This is an exact counterexample to a
parameter-uniform claim that the legal staircase maps onto the ambient
quotient/contact module merely because its dimension is large.

These controls are not counterexamples to the live target-ratio DUAL0
statement. The new faithful ratio control

```text
(n,w,g,m,B,s,U,L)=(11,5,8,6,2,1,8,8),
constant-T Q=binom(X,6), three equal errors epsilon=3/delta=1,
source/contact/nullity=(4764,4635,129), boundary gain=4
```

retains the desired four boundary directions. It is positive evidence that
the complete target-shaped source can kill the final dual line, not a proof
of the uniform theorem.

## 4. Exact-G badness and the remaining boundary join

Retained exact-G badness already yields a nonzero quotient polynomial `T`
with

```text
Q-q = locator(H) T,
deg T < g-(w+1).
```

This is formal in `K0ExactGDirectHrsCarrierObstruction6900.lean`. That same
file proves why the obvious direct carrier cannot finish the argument: its
top term has weighted degree `47g-1`, so even one additional X factor hits
the strict cutoff. The raw terminal active strip has width 90867 and can
hold the 81730-degree error-complement locator, but the already
agreement-killing partial locator carrier has no such room.

The new cokernel theorem says exactly what a successful full-source
elimination would leave: for each positive-cost shape, a low-degree
remainder `(g_shape U_shape) mod A`; for the constant shape, zero. To invoke
badness, one must still prove that boundary compatibility identifies a
nonzero combination of these remainders with an interpolant for the bad
direction (or with the nonzero `T` above) inside a forbidden degree window.
Neither local rank capacity nor CRT perfectness provides that identification.

## 5. Precise next theorem / pivot rule

The next useful theorem is not another ambient CRT lemma. It must be a
**target-strict raw-to-filtered-CRT isolation theorem** with the following
content:

1. start from the literal compatible-dual equation on
   `SecondJetRelaxedGlobalIndex.exponent`;
2. retain the coupled PC block, rather than projecting each shape by a CRT
   idempotent;
3. prove confluence only on the four-dimensional boundary-compatible dual
   cone (generic confluence is false);
4. output the multiplier-window equations required by
   `m47_active_shape_cokernel` and `m47_constant_shape_dual_zero`; and
5. identify the surviving degree-`<c` remainder with a forbidden exact-G
   interpolant, forcing all four boundary coefficients to vanish.

If step 3 fails in a faithful target-ratio chamber, the full-source CRT route
should be stopped. If it survives, the finite tests indicate that it should
be proved directly on the rank-adaptive boundary cone, not by trying to make
the entire contact image into a quotient module.

## 6. Reproduction

The new formal artifact was checked under the task-local sub-8-GiB wrapper:

```text
./.experiments/run_lean_8g_capped.sh \
  /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work/.experiments/K0FilteredCrtGroebnerDual6900.lean \
  -o /tmp/K0FilteredCrtGroebnerDual6900.olean

exit 0
wall approximately 3 seconds
Lean source SHA256 f79049881db597fa50276f75c032beb9e83c9bc79d7051cf24d5fe5e9d910ab9
Lean object SHA256 a37206128c7704b2c2ecceefccb0612b94465a663a231e9cd9c99e0ace03c987
```
