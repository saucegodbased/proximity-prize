# K0 locator-lifted order seven: complete next-rung discriminator

Date: 2026-09-15 UTC. Scope: lower 6900, projective-high K0 leaf. This is
not a candidate, endpoint theorem, or claim of a 6900 proof.

## Verdict

**YELLOW/GREEN finite evidence for exactly one recurrence rung.** The
locator-lifted packet

```text
H^37 N^6 J,
H^37 N^5 C1,
H^37 N^4 C2,
H^37 N^7 Z
```

survives the first faithful exact test that includes all three consumers at
once:

1. every forbidden top-X coefficient;
2. one order-seven residual output at every error; and
3. the four raw compatible-boundary outputs at the fresh point.

The target box is `(M,K)=(81731,3)`. The evidence covers the singular fresh
stratum `J=C1=C2=0`, not merely random nonzero covariant values. It is still
a rank experiment, not a uniform theorem. More importantly, it supplies
only the seventh old-error equation. Orders 8 through 43 remain open, and
the companion linear-tower audit already stops the same four-generator
linear architecture at order eight. This packet must not be advertised as
an endpoint construction.

## 1. Exact target map being tested

Let coefficient polynomials `A0,...,A3` have

```text
deg_X Ai <= M = e = 81731,
deg_Z Ai <= K = 3.
```

After factoring the common monic `H^37` face and reversing X coefficients,
write `q=1/X` and

```text
g(q,Z) = reverse(U0 + Z U1).
```

Because the required top window has length `112610<n`, the lower term of
`N=X^n-1` does not enter it. The four normalized data faces are exactly

```text
-q g,
-q^2 (theta+1)g,
-q^3 (theta+1)(theta+2)g,
Z.
```

The top block is therefore coefficient extraction, through q index
`112609`, from

```text
-q A0 g - q^2 A1 (theta+1)g
  -q^3 A2 (theta+1)(theta+2)g + Z A3.
```

There are five output Z channels and `81731+30879=112610` q rows. One row
is structurally zero, but the conservative ledger charges all of them:

```text
domain columns = 4*(81731+1)*(3+1) = 1,307,712,
top rows       = 112610*(3+2)       =   563,050.
```

The next-rung residual contributes **one scalar row per error**, hence at
most 81731 more rows, not four rows per error. The fresh probe contributes
four rows. The resulting ambient surplus is large, but the script tests
rank rather than inferring surjectivity from this count.

At an error node `a`, put `n1=N'(a)`. If `j1,c12,c23` are the literal first,
second, and third epsilon coefficients of contacted `J,C1,C2`, the tested
order-seven row is

```text
n1^6*j1 * A0(a,gamma)
+ n1^5*c12 * A1(a,gamma)
+ n1^4*c23 * A2(a,gamma)
+ n1^7*gamma * A3(a,gamma).
```

The omitted `H(a)^37` is a nonzero common row scalar at an error. The script
computes `j1,c12,c23` by expanding the literal raw definitions, including
the `4*N^2*S` correction in `C2`; it does not sample these four weights as
independent random numbers.

At the fresh point it sets `Y=U0+gamma*U1`, so `J=0`, and differentiates the
literal raw formulas with respect to `(S,Y,R,Z)`. Coefficient-polynomial Z
derivatives are included. The default mode chooses `R,S` so that the actual
values also satisfy `C1=C2=0`, the most singular compatible stratum.

## 2. Why the received series is target-faithful

The earlier arbitrary-series probe found genuine `K=2` boundary defects.
Degree or first-support information alone therefore does not imply the
joint-rank theorem.

The complete probe constructs the received direction in the form forced by
agreement. On a multiplicative-subgroup node set it chooses

```text
deg P <= w,
H = product of the g agreement factors,
Q_gamma = P + H*E,
U0 + gamma*U1 = Q_gamma.
```

It cycles `deg E` through `0,...,e-1`. Thus every permitted reversed
valuation `M-1,...,0` is tested; `deg E=0` is the critical edge
`deg Q_gamma=g`, not a generic full-degree shortcut. It also exhaustively
checks the small projective pencil and retains only instances in which every
nonzero received direction lies above the scaled projective-high cutoff.

This distinction matters. An arbitrary affine-Z top series can obey
`valuation(g(q,gamma))<M` without being the reversal of a polynomial that
agrees with a degree-`w` polynomial on the chosen roots of `H`.

## 3. Exact finite receipts

All ranks are computed over prime fields with FLINT. For `K=3`:

```text
GF(193), n=32, g=22, e=10:
  2000 instances on actual C1=C2=0:       0 failures
  500 each on C1=C2=0, C1=0, C2=0,
      and generic fresh strata:           0 failures

GF(97),  n=16,  g=11, e=5:   200 tests:  0 failures
GF(257), n=64,  g=44, e=20:  200 tests:  0 failures
GF(769), n=128, g=88, e=40:   50 tests:  0 failures
```

Every green instance had

```text
rank(top+all errors)-rank(top) = e,
rank(top+all errors+boundary)-rank(top+all errors) = 4.
```

For the default `n=32` model the fixed ranks are `74,84,88`. The advertised
75 top rows include one identically zero `(q^0,Z^0)` row.

Replay:

```bash
python3 .experiments/k0_lifted_t7_joint_error_boundary_probe_6900.py \
  --seeds 2000 --k 3 --boundary-mode bothzero
```

No `decide` or `native_decide` is involved.

## 4. What remains and the correct process decision

### Endpoint relevance audit: disconnected

There is no existing callgraph which consumes this t7 rank statement. The
terminal theorem is

```text
K0LowHeadFourRowAnnihilator6900.
  compatibleBoundaryDual_eq_zero_of_lowHead_annihilator
```

and its concrete primal premise is the `TargetFourRowCRT` proposition in
`K0LowHeadFourRowCRT6900`. Both concern the kernel of
`targetRawOldLowHead`, whose literal projection retains every epsilon
coefficient `0,...,43` at every old node.

The lifted packet has order 44 at agreements but only order 7 at errors.
Consequently it is automatically invisible only in error orders `0,...,6`;
its order-seven coefficient is precisely the nonzero row tested above. It
does **not** lie in the full old-low-head kernel and cannot instantiate the
terminal annihilator's `hkill` premise. No source theorem currently stitches
this one correction layer to cap-legal layers 8 through 43.

The closest abstract induction (`TriangularKernel.eq_zero_of_triangular`)
would consume a complete family of diagonal maps after those global source
layers had been constructed; it does not construct them. Likewise, the
node-local order-44 ladder in `K0M44WeightedShapeSchedule6900` has no proved
simultaneous raw lift (`K0WeightedNodeFamilyLiftable` remains the missing
statement). Therefore the honest endpoint classification is:

```text
t7 complete next-rung finite discriminator     GREEN evidence
t7 uniform joint-rank theorem                  OPEN
existing target consumer/callgraph             NONE
t8 direct linear continuation                  STOP
t8..43 simultaneous nonlinear global lift      OPEN / fundamental
```

The missing theorem is the uniform full-rank statement for the literal
target map. A proof has to use the actual divisibility
`Q_gamma-P=H*E`, not just box dimensions or genericity. A likely proof form
is a transpose/CRT argument: any dual relation among the error and fresh
rows that extends through the top Toeplitz block should yield a polynomial
of degree below `g` vanishing at all agreement nodes, then a degree-`e`
polynomial vanishing on all error nodes plus the fresh point.

Even that theorem would close only t=7. The exact order-eight audit in
`K0CompatibleBoundaryAndTowerAudit6900.lean` shows that the direct linear
lift has coefficient cap only 18463 while its top overhang is 112610, so its
dimension inequality fails for every passive Z cap. Progress toward 6900
therefore requires a genuinely parametric nonlinear tower identity, not
individual tuning of the remaining 36 rungs.
