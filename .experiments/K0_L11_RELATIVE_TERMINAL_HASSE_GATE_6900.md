# K0 relative passive layer: exact terminal reverse-Hasse detector

Date: 2026-09-14 UTC. Scope: lower-6900, one frozen exact `F_101`, `m=8`
mechanism chamber. This is not a target theorem, candidate, build, or
submission.

## Verdict

**GREEN for the finite dual-tail detector.** The final three reverse-Hasse
coordinates detect the unique missing boundary direction after quotienting
by pure contact annihilators. Their induced map has rank one and kernel zero,
exactly the rank and kernel of the full relative connecting transpose.

There is a crucial formulation constraint. If all lower contact rows are
simply discarded on the primal side, the test is RED: the old truncated
contact kernel already has all four boundary directions, so its relative
connecting map is zero. The successful statement retains the complete
compatible dual, restricts its coordinates to the terminal tail, and then
quotients those terminal coordinates by restrictions of pure contact duals.
This is the invariant object that the HRS/reverse-Hasse proof must use.

## Frozen chamber and the full relative map

The data are unchanged from the passive-face discriminator:

```text
field                         F_101
(n,w,g,m,B,s,U,L_old)         (9,3,6,8,3,1,12,10)
candidate/tangent degrees     3 / 4
agreement set                 {0,1,4,5,6,8}
old complete source columns   11,178
new passive-only columns      1,860
new active-11,z=0 columns     101, excluded
```

Write `C0,B0` for old contact and boundary maps and `D,BD` for the new
passive layer. The exact complete-contact ranks are:

```text
stage                 columns   contact rank/nullity   boundary rank on kernel
L10 old                11178       10861 / 317                    3
old + passive          13038       12321 / 717                    4
```

Therefore

```text
dim {d : D d is in image C0} = 1860 - (12321-10861) = 400,
rank(delta)                                      = 4 - 3 = 1,
dim ker(delta)                                         = 399.
```

Equivalently, the old compatible boundary-dual quotient is one-dimensional,
and the transpose `delta*` has rank one and kernel zero.

## Which rows are the last three?

The literal local contact monomial is ordered

```text
(T, E, R, S, Z).
```

Its first exponent is the outer Hasse/contact index. At multiplicity eight
these indices are `0,...,7`, so the exact analogue of target indices
`44,45,46` is

```text
tail = {5,6,7},       head = {0,1,2,3,4}.
```

The complete L11 row universe has 16,560 rows, split as follows:

```text
outer index       0     1     2     3     4     5     6     7
row count      1539  1944  1944  2295  2880  1728  2025  2205
```

Thus the head has 10,602 rows and the last-three tail has 5,958.

## Basis-free dual quotient computation

Let `T` denote the full contact row space and define

```text
L = {eta in T* : C0^T eta = 0},
A = {(ell,eta) : C0^T eta = B0^T ell}.
```

`L` consists of pure contact annihilators. `A/L` is the space of compatible
boundary-dual classes. Let `rho` restrict `eta` to outer indices `5,6,7`.
The coordinate restriction is not well-defined on `A/L` until its target is
also quotiented by `rho(L)`, so the invariant terminal map is

```text
rho_bar : A/L -> tail* / rho(L).
```

All dimensions below follow by exact rank-nullity; no canonical pivot vector
or random projection is used.

Full old contact gives

```text
dim L = 16560 - 10861 = 5699,
dim A = dim L + dim(A/L) = 5699 + 1 = 5700.
```

A pair has zero final-three coordinates exactly when `eta` is supported on
the head. The head-projected old map has

```text
head rows / contact rank / nullity       10602 / 7029 / 3573
boundary rank on its kernel                              4.
```

The last number is decisive: every boundary covector annihilating the
head-contact kernel is zero. Hence there is **no** nonzero compatible
boundary dual with final-three coordinates all zero. Quantitatively,

```text
dim ker(rho | L) = 3573,       rank rho(L) = 5699-3573 = 2126,
dim ker(rho | A) = 3573,       rank rho(A) = 5700-3573 = 2127,
rank rho_bar      = 2127-2126 = 1,
dim ker rho_bar   = 1-1       = 0.
```

This is exactly the full relative connecting-transpose receipt
`rank(delta*)=1`, `dim ker(delta*)=0`. Therefore the two kernels agree on the
one-dimensional compatible boundary-dual quotient. In particular, the
specific counterexample requested by the ADHD focus note -- a nonzero
compatible boundary dual with terminal coordinates zero modulo pure contact
duals -- does not exist in this chamber.

`K0TerminalDualDetection6900.lean` formalizes the basis-free implication used
here. `boundaryDual_eq_zero_of_terminal_eq_zero` proves that surjectivity of
the boundary map on the head-contact kernel forces any compatible pair with
zero terminal component to have zero boundary covector.
`boundaryDual_eq_of_terminal_diff_is_pure` proves the quotient-aware version:
two compatible pairs whose terminal components differ by the terminal part
of a pure contact annihilator have the same boundary covector. The file
compiles in about four seconds under the 3.5-GiB Lean allocator cap; its only
printed axioms are `propext` and `Quot.sound`.

## Why the tempting tail-only computation is RED

For completeness, retaining only terminal primal contact rows gives:

```text
kept indices   old contact rank/nullity/gain   extended rank/nullity/gain
{7}                 1890 / 9288 / 4               2205 / 10833 / 4
{6,7}               3645 / 7533 / 4               4230 /  8808 / 4
{5,6,7}             4995 / 6183 / 4               5760 /  7278 / 4
```

Every such projected old kernel already maps onto all four boundary
coordinates. Its boundary quotient is zero and its relative connecting rank
is therefore zero. This does not contradict the GREEN dual detector. It asks
for a dual supported only on the tail, whereas the HRS proposal restricts an
arbitrary complete dual to the tail modulo restrictions of pure complete
contact annihilators. Confusing these two operations would turn the finite
evidence into a false theorem.

## Family provenance and semantic sanity

The independent family-order receipt on the same frozen chamber already
shows that only the new raw-`1` passive family is needed in the chosen order.
The first relative fourth normal occurs after 285 raw-`1` additions, with
last column `X^2 Y^9 Z^2`. Its canonical relation has 10,193 nonzero terms:
9,908 old L10 terms, 284 earlier raw-`1` terms, and that last term.

The independent chain audit rebuilt this relation and checked both semantic
conditions which a matrix artifact could have violated:

```text
literal contact support                      empty
candidate specialization polynomial          identically zero
partial-X derivative at X=9                  55
boundary-gradient dot graph tangent          46
full chain rule                         55 + 46 = 0 mod 101
```

Its canonical hash is
`8654b53422aab030424746c9ae4093986ac55ec01a7359b1e82e5e43f9dff0bb`.
Thus the fourth normal used here is compatible with exact specialization and
the full five-coordinate chain rule; it is not a scaling mismatch between
ordinary and Hasse second derivatives.

## What this changes, and what remains open

This result upgrades the last-three idea from a speculative compression to a
successful exact mechanism test:

```text
full relative passive connecting direction        exact, rank 1
last-three detector modulo pure contact duals      exact, rank 1/kernel 0
raw-1 family provenance and chain-rule sanity      exact
target last-passive-layer source capacity          exact, previously GREEN
target m47 terminal aggregate adjoint producer     OPEN
target 6900 theorem/candidate/build/submission     OPEN
```

The remaining theorem is now sharply stated. For the literal target raw
source, the relative passive layer must produce the three aggregate adjoint
equations at reverse-Hasse indices `44,45,46`, in the quotient by terminal
restrictions of pure contact annihilators. The compiled upper-tail closure
then consumes exactly those equations. This finite calculation does not
construct that target producer and must not be cited as genericity or as a
proof that three raw bands are independently sufficient.

### Target head dimension sanity (not a rank theorem)

For the cap-3756 target ledger, the published relaxed-rank contributions at
ordinary outer orders `0,1,2` are

```text
303,669 + 607,257 + 910,764 = 1,821,690.
```

Subtracting these cells from the full local bound gives

```text
248,124,600 - 1,821,690 = 246,302,910.
```

The cap-3756 source therefore has the positive reduced dimension margin

```text
65,044,354,424,601 - 262,144 * 246,302,910
  = 477,524,385,561.
```

The exact arithmetic is compiled as
`target_head_ge_three_dimension_margin` in the same Lean file. This is only
a capacity sanity check for a future target head/tail argument. It neither
identifies the abstract head projection with a literal target filtration nor
proves that its kernel boundary image has rank four; that remains part of the
target-uniform producer theorem.

### What one spare passive layer changes

Moving the target source from `L=3757` to `L=3758` improves the published
dimension ledger but does not make the detector theorem automatic:

```text
L       source columns       local bound       all-node margin
3757    65,061,789,117,960   248,191,020          2,371,080
3758    65,079,223,811,319   248,257,440         25,459,959
                                                  +23,088,879
```

`target_L3758_margin_receipt` compiles the last two arithmetic identities.
The useful structural simplification is source legality: multiplication by
the passive variable sends every legal cap-3757 monomial into cap 3758,
including the former terminal face. There is no taper exception to split off.

What it does **not** supply is contact compatibility. In general
`C(Zv)=Z_local C(v)` need not lie in `image(C|S_3757)`, and when `v` is an old
contact-kernel relation the exact root-count stop makes its value trace zero,
so its shifted boundary normal remains in the old boundary image. One spare
layer removes a legality obstruction, not the relative connecting-map
obstruction.

The exact primal producer still required at `L=3758` is:

```text
Let S=S_3757, Splus=S_3758, and let ell span the annihilator of
B(ker(C|S)).  Produce d in Splus and p in S such that

    C(d) = C(p),
    ell(B(d)-B(p)) != 0.
```

Equivalently, prove that the connecting map

```text
{d mod S : C(d)=0 in coker(C|S)}
    -> Boundary / B(ker(C|S))
```

has rank one. In the quotient-aware HRS formulation, the same obligation is
to use the newly legal shifted equations to force the terminal restriction
class in `tail* / rho(pure contact annihilators)` to zero for every compatible
dual. The GREEN terminal detector then forces `ell=0`. Neither the positive
`L=3758` margin nor full shift legality proves this last source-adjoint
realization; that remains the single load-bearing producer statement.

## Reproduction

Run under the same hard address-space ceiling used for this receipt:

```bash
prlimit --as=4404019200 -- \
  python3 .experiments/k0_l11_relative_terminal_hasse_gate_6900.py

.experiments/run_lean_4g_capped.sh \
  /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work/.experiments/K0TerminalDualDetection6900.lean
```

Final unified replay hashes and measurements:

```text
canonical SHA-256   f8da3a8b5fb097dcdb033d0738d795fc969f2fdc9e7c7e18201a8976ed40900e
script SHA-256      d1f8f9f0098a9857ba7005d8cc6ccdb7caa5e09445db0ee5dff41a7e39e5c934
runtime             1164.027 seconds
peak RSS            3,106,332 KiB
```
