### Full187 pure-face update: exact two-generator contact ideal and affine Popov basis

This is a target-exact algebraic compression for the open F3 pure-face gate.
It is not a 69.00 construction, candidate, build, or submission.

#### 1. The prescribed boundary has one explicit legal agreement section

Let `H`, `R`, `G=HR`, and `E` be the frozen Full187 locators. The F3
Y-linear boundary `B=H^59 R^60` has the exact agreement-side section

```text
K0(X,Y) = -R(X)^60 Y (Y-H(X))^59.
```

At an H-node, its sixty local factors give order 60; at an R-node, `R^60`
does. Its coefficient of `Y^n` has degree

```text
60 deg(R) + (60-n) deg(H) = D-n(W+1) < D-nW.
```

Under the graph transform this is simply

```text
F0(X,V) = -R V (R V-1)^59.
```

On the error face `Y=1`, the complete structured Hasse residue is

```text
rho_j = -R^60 (1-H)^(59-j)
          (binom(60,j)-H binom(59,j-1)),   0 <= j < 60.
```

Commit `2bd2ce2` evaluates the literal target and finds all 60 residues
nonzero modulo E, all with degree `81730=deg(E)-1` (sequence hash
`c54ab00570540d477be96db5ae685378ce8727bb0b3467c14b1dad988e33dc42`).
Thus the correction is real, but future gates need only test membership of
this one binomial residue vector—not arbitrary codomain surjectivity.

#### 2. Exact compact contact basis

The pure graph takes value `Y=0` on G and `Y=1` on E. Put

```text
A = E Y,
C = G(Y-1).
```

Because `gcd(G,E)=1`, the radical graph ideal is exactly

```text
I = (G,Y) intersect (E,Y-1)
  = (G,Y)(E,Y-1)
  = (A,C).
```

Indeed `EC-GA=-GE`, and a Bezout identity `uG+vE=1` gives
`uYC+v(Y-1)A=Y(Y-1)`, recovering all four product generators. Since all
graph-point maximal ideals are pairwise comaximal, total Hasse order 60 is
the ordinary power

```text
I^60 = ((EY)^i (G(Y-1))^(60-i) : 0 <= i <= 60).
```

Commit `5801b65` checks the literal G/E partition and Bezout certificate.
This is an explicit 61-row unbounded contact basis—the missing
soundness/completeness input for a shifted reducer on this face.

#### 3. Literal target affine weak-Popov start

Commit `d0301b2` shifted-reduces the two affine coefficient rows

```text
[0,E], [-G,G]    with coefficient shift [0,W].
```

After 16,196 full-quotient Euclidean reductions, the exact weak-Popov data is

```text
row 0 component degrees       (196608,65535)
row 0 shifted degree / pivot  (196608,constant)
row 1 component degrees       (196607,65536)
row 1 shifted degree / pivot  (196607,Y)
sum shifted degrees           393215 = N+W
determinant                   GE = X^N-1
row hash                      e1c0ca4e32500d7c5bbeaf83b7d80b8b58362444ea4fb8a47218e1e84137f98f
```

The replay took about 40 seconds and 170 MiB RSS. This supplies a compact
starting point for the multiplicity-60 symmetric-power reduction instead of
first expanding degree-10M raw rows.

One important caution: the affine Popov degrees cannot simply be multiplied
by 60. Power-ideal S-polynomials can lower the minimum weighted degree (this
already occurs in exact small controls). The load-bearing next computation
must retain those cancellations, permitted Y-shifts through degree 82, and
the literal tapered coefficient shifts before pairing with `rho`.

#### 4. Scalar dual route remains stopped

The first scalar Euler orders not decided by root counting, `k=17,18`, are
both target-exact surjective. After rooting all individually-surjective
lanes, `A72` supplies a common prefix and `A2=G^58 q` closes exact Hankel
minors of sizes 1,759 and 83,490. Commit `cd73bcb` records the exact full-rank
Berlekamp--Massey receipts under 0.5 GiB. So the next pure-face test must be
genuinely coupled; another scalar projection is not the bottleneck.

Current independent runs are testing (a) a ratio-faithful first-shell packet
connector and (b) the first target positive-u0 frontier. Neither is claimed
here until its exact audit completes.
