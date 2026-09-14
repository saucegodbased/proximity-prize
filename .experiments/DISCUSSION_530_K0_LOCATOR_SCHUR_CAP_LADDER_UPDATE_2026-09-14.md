### Lower 6900: exact locator/Schur decomposition, cap-regression diagnosis, and formal SR seam

Status first: the verified floor remains accepted **6810** (`09d8a2a`,
submission `1852e895-c0db-46ad-8705-e0c92d638224`). There is still no 6900
candidate, build, comparator run, or submission. This update reports exact
finite mechanism results and axiom-clean research lemmas; it does not claim
target transport.

The public research branch is

https://github.com/saucegodbased/proximity-prize/tree/codex/6900-live-research

#### 1. The full-source gain-four result now has an exact locator/Schur decomposition

For the capacity-positive F101 chamber

```text
(n,w,g,m,B,s,U,L,k,n0)=(8,3,5,8,3,1,12,16,0,1),
source=17679, one-node bound=2179, margin=+247,
agreement={0,1,3,4,6}, errors={2,5,7}, Q=X^4,
```

we changed every consecutive X window to the canonical basis

```text
Lambda_G(X)^q X^d, 0<=d<g.
```

The direct localization/contact factorization was checked coefficientwise.
One relaxed local source has 2844 coordinates, local contact rank 2179, and
kernel dimension 665. Familywise agreement localization has total kernel
3550 and cokernel 91; the cokernel splits as

```text
R:4, S:1, R2:20, R3:56, SR:10.
```

The product of the five universal 665-dimensional local contact kernels maps
onto all 91 missing cells. Consequently the complete agreement-contact map
has exact rank `5*2179=10895` and kernel dimension 6784.

We then avoided the previous near-4-GiB monolithic RREF. After agreement RREF
`[I A]`, the implicit certificate `K=(-A;I)` has shape `17679x6784`, rank
6784, and satisfies `C_G K=0`. Applying only the three error blocks gives

```text
C_error K: 6537x6784, rank 6516, nullity 268.
```

The remaining boundary quotient is literally `4x268` and has rank **4**.
Every one of its 268 columns is nonzero, every free coordinate is in the SR
family, and their locator/residue distribution is

```text
(q,d)=(0,4):90, (1,3):63, (1,4):97, (2,4):18.
```

The first four Schur pivots already give a four-column witness:

```text
SR(q=2,d=4,y=4,z=10,width=25),
SR(q=2,d=4,y=5,z=2,width=22),
SR(q=2,d=4,y=5,z=3,width=22),
SR(q=2,d=4,y=5,z=4,width=22).
```

Its determinant is `72 mod 101`. Exact hashes are:

```text
free-label hash  af81cab8a779873c1d64e2006e9700bb4b6d4ed365d6d7d96683f6751516635a
Schur-entry hash 7a62e7e7c8c3770ed56232de845fe2f05ae3045753f2579576d4c09cd2894f44
canonical JSON  b54ee89b1b20556999c22f1ed1182137b0cc6bff921d2260e31e5c4a7fe1dfa0
```

The staged run took 445.992 seconds and peaked at 3,801,516 KiB under a hard
3.9-GiB address-space cap. Commit `618d008` contains the executable and full
receipt. This replaces a bare rank observation with a reproducible causal
factorization: agreement localization, local-kernel repair, error
elimination, then a four-row Schur block.

#### 2. A real rank-three regression was found, scoped, and repaired by one source layer

A second capacity-positive chamber initially looked like a counterexample:

```text
(n,w,g,m,B,s,U,L)=(9,3,6,8,3,1,12,10),
candidate degree 3, exact maximal agreement 6, Q=X^4,
source=11178, local bound=1207, margin=+315.
```

Its exact contact rank/nullity is `10861/317`, but boundary gain is only 3.
This is not a bad evaluation point: ranks at boundary X=9,10,11 are all 3,
and every one of the 317 exact polynomial tangent contractions is identically
zero. The surviving covector is exactly `(Q,Q',Q'',1)`.

The process audit caught the missing fidelity check before this was promoted
to a target RED. Since the source also imposes

```text
y+r+s<=U, y+r+s+z<=L,
```

the effective active cap is `min(U,L)`. Thus `L=10` deletes the active-degree
11 and 12 layers even though the displayed parameter still says `U=12`.
Positive dimension margin did not preserve the graded source closure.

We froze the candidate, agreement/errors, seed, all received values, and
`Q=X^4`, then changed only the source cap. The exact ladder is:

```text
L=10: rows 14535, cols 11178, rank 10861, nullity  317, boundary gain 3
L=11: rows 16560, cols 13139, rank 12321, nullity  818, boundary gain 4
L=12: rows 18585, cols 15183, rank 13779, nullity 1404, boundary gain 4
```

At L=11 the first three normals appear after R2 and the fourth after R3. At
L=12 even the selected low family already has gain two, and the remaining S
layer completes gain four. These first-pivot statements are relative to the
explicit source order, not invariant minimality claims.

The important conclusion is narrow but positive: the minimal bad tangent
`deg Q=w+1` is not intrinsically a complete-source obstruction. One added
source layer changes exact function-field rank 3 to rank 4. The target is far
inside this cap regime (`L-U=3693` in the original m47 profile and 5043 in
the reduced-curvature profile). We are separately ablating the 101 new
active-degree-11 cells from the other 1860 L11 additions to identify which
part of the layer is load-bearing.

#### 3. The first SR seam is formal and source-legal at the target

Commit `c05d608` isolates four small Lean modules instead of rebuilding the
49k-line aggregate. They prove the literal centered relation

```text
epsilon^2 * S*R * (V-anchor)^q
  = epsilon^(q+2) * S*R * (R-epsilon*S+epsilon^2*T)^q.
```

Thus `q=6` gives order 8 in the finite chamber and `q=45` gives order 47 at
the target. The epsilon-squared factor is a literal three-X finite
difference. Every companion in the target centered expansion is proved to
satisfy all five raw source caps. Two further exact connections are formal:

```text
(partial_S+epsilon*partial_R)(SR column)
  = R column + shifted S column - x*S column,

delta(Y^(y+1) R2)
  = X-lowering + (y+1)Y^y R3 + 4 S R Y^(y+1).
```

The SR boundary row is also the exact inclusion-exclusion of matching R, S,
and base rows. The modules compile with only `propext`, `Classical.choice`,
and `Quot.sound`; no `sorry`, `decide`, or `native_decide`. Maximum measured
Lean RSS was 1.964 GiB.

#### 4. Honest remaining theorem

These results remove three uncertainties: the full legal source has the four
normals in a positive chamber, the gain survives the `deg Q=w+1` adversary
once the cap is not truncated, and the first SR/R2/R3 seam is a literal
source-legal identity. They do **not** prove 6900.

The dominant gap is now a uniform locator-residue Schur identity. At target
scale, `d<g=180413` is large, but this is also what makes error CRT plausible:
there are only `e=81731<g` errors, so a residual polynomial of degree `<g`
can interpolate arbitrary error values, while `Lambda_G` is nonzero on every
maximal-set error. The Hasse-order interaction is the nontrivial part:
`Lambda_G^1` does not itself kill 47 agreement jets, so the 91-cell/local
kernel repair must be proved parametrically rather than assumed pointwise.

The next proof target is therefore:

1. formalize the universal locator/Hasse agreement quotient and local-kernel
   repair;
2. use residual-degree `<g` CRT to decouple the genuine errors inside that
   agreement kernel, respecting every tapered X window; and
3. factor one four-by-four SR boundary determinant by the nonzero mismatch
   data.

Until that chain is compiled, there is no 6900 candidate or honest submission
ETA. The verified fallback remains 6810.
