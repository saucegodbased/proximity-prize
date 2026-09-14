# m69 first defect: actual-residual zero seam GREEN, containment still STOP

Date: 2026-09-14 UTC. Scope: lower-6900 research only; no production or
submission files are changed.

## Decision

The numerator-zero counterexample in `cb97180` does **not** obstruct the first
descending m69 Pascal defect.

At that defect the literal actual incoming residual has a common factor `W`;
it therefore vanishes on every numerator-zero node. More strongly, the
first defect's `W^0` prefix has dimension `258898`, exceeding the full-leaf
upper bound `149776` on the number of numerator zeros. If there are at least
`134317` numerator-zero nodes, the `W^0` and `W^1` channels alone are onto all
`262144` coordinates by two Lagrange interpolations.

This does **not** finish the first-defect rational theorem. The remaining
branch is

```text
129450 <= deg N0 <= 149776,
#{domain zeros of N0} <= 134316.
```

The existing no-wrap dual theorem ends at `deg N0=129449`. In the displayed
remaining branch, divisibility of the actual target by `W` kills duals
supported only on `W=0`, but it does not prove that every other four-prefix
cokernel vector kills the target. Calling the target contained from
`W`-positivity alone would be the same unsupported jump this audit was meant
to detect.

## Exact first defect

For `(M,slope,curvature,J,L)=(69,24,10,94,2369)`, the unique first descending
defect is

```text
(A,n,H,target dimension,Jraw,Jlegal,defect)
  = (63,44,24,1,{14},{},1).
```

The associated raw chain has `s=10`, `y=39..53`,

```text
r = 53-y,
q = 54-y.
```

Only its first member is outside the literal initial prefix:

```text
(y,r,s,q) = (39,14,10,15),
width       = 4191058 = 15*262144 + 258898.
```

Thus the missing scalar direction is not an absent coefficient polynomial.
It has a `258898`-dimensional partial order-15 channel.

## Literal actual residual

The terminal stream with `(r,s)=(14,10)` has

```text
terminal y = J-r-s = 70,
terminal y - contact f = 70-39 = 31.
```

Every ordinary correction source visible in this quotient is

```text
(y,r,s,q,z,A)=(39+h,14,10,15,2306-h,63+h),
h=0,...,29.
```

There are exactly 30: `h=30` would require correction exponent `y=69`, but
the source cap is `y<M=69`. The special terminal source is nevertheless legal
at `y=70` and reaches the quotient with frozen-word power `h=31`.

After excluding the current `h=0` control, the actual incoming residual is

```text
binom(70,39) W^31 C_15
  + sum_(h=1)^29 binom(39+h,39) W^h U_(39+h,15).
```

All binomial scalars are nonzero in the benchmark field because their
arguments are below the characteristic. Factoring gives

```text
W * [binom(70,39) W^30 C_15
     + sum_(h=1)^29 binom(39+h,39) W^(h-1) U_(39+h,15)].
```

Therefore the complete incoming residual—not merely its terminal term—is zero
where `W=N0/E0=0`. The Lean theorem
`positiveResidual_eq_mul` proves this with arbitrary coefficient symbols, so
it does not assume canonical higher jets vanish.

The terminal coefficient window is also retained exactly:

```text
width(C)=127857,
X^15 H_15(C) has support 15..127856 and dimension 127842.
```

The executable checks every one of its `127842` nonzero binomial weights.

## The first four physical prefix channels

For `h=0,1,2,3`, preserving every already prescribed lower Hasse jet leaves

```text
h       0       1       2       3
depth  15      15      14      14
rho 258898  127827  258900  127829.
```

At every NTT node, multiplication by `X^15` normalizes the order-15 Hasse
map on a variation `(X^N-1)^depth A` to a diagonal map on the coefficients of
`A`. The executable evaluates all `773454` diagonal weights exactly modulo
`2130706433`; none is zero. Hence the literal first-four envelope is exactly

```text
F_<258898 + W F_<127827 + W^2 F_<258900 + W^3 F_<127829.
```

No Hasse rank or hidden-section assumption separates this envelope from the
physical source. The remaining issue is the rational cyclic rank itself.

## Why the cb97180 zero dual is harmless here

The counterexample in `cb97180` uses the later deficient shape `(0,0,0)`,
whose base prefix is only `127729`. It chooses `127730` numerator-zero nodes,
so every positive-power channel vanishes and the base prefix is one dimension
short.

At the first defect the base prefix is instead `258898`. The actual full-leaf
bound gives

```text
z = #{i | N0(domain i)=0} <= deg N0 <= 149776 < 258898.
```

Thus the base prefix can interpolate arbitrary data on all zero nodes. The
actual incoming residual is already zero there, but this larger statement is
useful for gluing.

If `z>=134317`, then the live set has

```text
262144-z <= 127827
```

nodes. First choose `A0` of degree `<258898` matching any desired word on the
zero set. On the live set, `W` is nonzero; choose `A1` of degree `<127827`
interpolating `(target-A0)/W`. Then `A0+W*A1` is the target at every node.
`exists_two_channel_interpolants` formalizes this exact two-step argument for
arbitrary finite injective nodes.

## Precise remaining theorem

There are now three honest regions:

1. `deg N0<=129449`: the committed no-wrap square-dual lemma applies.
2. `nodalZeros(N0)>=134317`: the new `W^0/W^1` Lagrange gluing is onto even
   for an arbitrary target.
3. `129450<=deg N0<=149776` and `nodalZeros(N0)<=134316`: still open.

For region 3 the actual-target condition to prove is

```text
W^31 * X^15 H_15(C)
  + all fixed/induced positive-W higher-jet terms
  belongs to
F_<258898 + W F_<127827 + W^2 F_<258900 + W^3 F_<127829.
```

It is enough to show that every dual solution of the corresponding cyclic
Padé relation annihilates this actual target. `W`-positivity proves that only
for zero-supported duals. A proof must now use the high-degree cyclic syzygy,
the source-induced higher-jet correlations, or a sharper zero/live split; it
cannot cite `cb97180` as a first-defect obstruction, and it cannot declare
containment from a dimension count.

## Reproduction

```bash
cd /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work
prlimit --as=536870912 --cpu=300 -- \
  python3 -B \
  .experiments/m69_first_defect_actual_residual_and_zero_split_gate_6900.py

env LEAN_NUM_THREADS=1 lake env lean -j1 -M3500 \
  .experiments/M69FirstDefectActualResidualZeroSplit6900.lean
```

Both artifacts are bounded and use no `decide`, `native_decide`, `sorry`, or
unsafe declaration. The executable emits its canonical and source hashes;
the Lean file prints every theorem's axiom set.

Recorded bounded run:

```text
Python exit / peak RSS     0 / 54468 KiB
canonical SHA256           7a83723aee11879a796c7d1c1c7162889ee38d261e11a8c8ff9a6926f68eadb3
Python source SHA256       222811944f695a5a0eefc56b34df2a12a54c27204334e9091d963d8a1b006f85
Lean source SHA256         7a2a8bf216dcc29437aab716d5bfcc0e934a5cb59fafbd88bd904a671aa2e0df
Lean axiom sets            [propext, Classical.choice, Quot.sound]
```
