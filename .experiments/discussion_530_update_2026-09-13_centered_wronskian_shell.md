6900 progress update: exact grade-7 correction has a compact Wronskian form

Accepted production is still 6806; this is mechanism progress, not a candidate or score claim.

I replayed the exact successful F101 primary bordered solve
`(n,w,A,m,D,s,t,J,L)=(11,5,8,4,32,1,1,6,10)` and factored the *complete* new grade-7 portion of its canonical correction vectors. For each of the three required locator RHS (`F0/F1/F2`), the 157/157/158 nonzero shell terms occupy the same eight `(Y,R,S,Z)` shapes and satisfy the exact polynomial identity

```text
V^2 Z^3 (c V^2 + C Lambda V Z + A Xi J1 Z),
V  = Y-Xi^2 Z,
V1 = R-2 Xi Xi' Z,
J1 = Lambda V1-Lambda' V.
```

Equivalently, after changing the pure part to the centered `V` basis:

```text
C0=C1=0,
C2=-2 A Lambda Xi^2 Xi',
(C3+A Xi Lambda') is divisible by Lambda.
```

There is also a coupled pure-seed head cancellation. With

```text
B0=C3-c Xi^2+2A Lambda Xi',
```

all three RHS have `deg B0=13` and raw boundary-zero coefficient

```text
[Z^7] = B0*(-Xi^2)^(m-1).
```

This matters because it identifies the previously missing derivative companion: it is the locator Wronskian `J1`, not an independent scalar actuator. It also shows why checking the value and derivative carriers separately gives a false source-width failure—the top pure-seed terms cancel only after assembly.

Independent checks:

- exact `nmod_poly` assertions cover all eight source shapes for all three RHS;
- contact rank/nullity and whole-correction hashes replay the prior successful solve;
- the Wronskian assembly and boundary-zero identity are green in Lean over an arbitrary commutative ring, without `decide`/`native_decide`;
- script/payload hashes: `20cd252f...` / `2ca8a1f4...`;
- commit: `435b02a` (plus independent factorization commit `59ba35e`).

Honest remaining gap: prove target-scale existence/degree bounds for `A,C,c`, check the assembled raw coefficients against every literal weighted X strip, and iterate this one-shell Wronskian step through the full slope/curvature HPL seed trellis to the load-bearing cap 2703. No 6900 candidate exists yet.

Process correction also landed: the earlier 33-group low-relay minimizer was only deletion-local from the full 41-group start. The known grade-7 start minimizes to 27 groups/784 columns, so 33 was never a global lower bound. The updated artifact now records both starts explicitly.
