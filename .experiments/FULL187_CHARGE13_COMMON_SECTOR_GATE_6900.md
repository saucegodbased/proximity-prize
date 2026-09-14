# Full187 charge-13 common sector and discussion-530 transfer gate

Date: 2026-09-14 UTC. Scope: lower-6900 research only. No production,
submission, score, or radius file is changed.

## Verdict

**GREEN (exact):** the eleven Full187 charge-13 origins have a uniform
`76,979`-coefficient rectangle of complete binary degree-ten `R/S` sectors,
dimension `846,769`. Their remaining `55` coefficients are not an irregular
remainder: they split into ten complete smaller binary sectors of dimensions
`10,9,...,1` after fixed powers of `S`. Thus strict X-window compatibility is
completely understood.

**STOP (transfer):** this is only a combinatorial binary-simplex match to the
sector in discussion #530. The discussion's `C0,C1` are special conics on
three derivative jets, with

```text
in(C0) = a0 U + t^2 Q(Z),
in(C1) = t (Z-s1)(Z-s2),
in(Y-v) = t Z.
```

The benchmark `R,S` are source derivative variables. No filtered local-ring
map identifies their initial forms with these conics. Therefore the
discussion contact-order formula cannot presently be imported into the
Full187 proof. The missing object is one small initial-form bridge, not more
dimension counting or a broad mapping-cone computation.

## 1. Exact eleven-origin ledger

At the target parameters

```text
(p,w,g,m,D,J,q,t,L)
  =(2130706433,131071,180413,60,10824780,82,21,10,2703),
```

the charge-13 terminal origins are indexed by `s=0,...,10`:

```text
(y,r,s,z) = (61,21-s,s,2621).
```

For a source monomial

```text
X^a Y^61 R^(21-s) S^s Z^2621,
```

the strict coefficient width is

```text
D - w*61 - (w-1)*(21-s) - (w-2)*s = 76979+s.
```

Hence the physical source dimension is

```text
sum_{s=0}^{10} (76979+s)
  = 11*76979 + (0+...+10)
  = 846769 + 55
  = 846824.
```

These are eleven physical coefficient polynomials, not 33 independent
polynomials. The latter mistake would count `2,540,472` dimensions and
overcount by `1,693,648`.

## 2. Complete common rectangle

Put `i=10-s`. Then

```text
R^(21-s) S^s = R^11 * R^i S^(10-i).
```

For every `a<76979`, all eleven values `i=0,...,10` occur. Thus, after the
fixed factor

```text
B = Y^61 R^11 Z^2621,
```

the common source is exactly

```text
B * { sum_{i=0}^{10} p_i(X) R^i S^(10-i)
      | deg p_i < 76979 }.
```

It is a literal complete binary simplex in `R,S`, with dimension
`11*76979=846769`. This statement is coefficientwise and respects the
half-open X windows.

## 3. The 55-cell fringe is ten smaller complete sectors

At the extra coefficient `a=76979+j`, with `j=0,...,9`, origin `s` is legal
exactly when `j<s`. Therefore `s=j+1,...,10`, giving `10-j` monomials. Factor
`S^(j+1)` and put `N=9-j`:

```text
R^(10-s) S^s
  = S^(j+1) * R^(10-s) S^(s-j-1),

(10-s) + (s-j-1) = 9-j = N.
```

So the entire fringe is

```text
j=0: X^76979 * S^1  * complete binary degree 9   (10 cells)
j=1: X^76980 * S^2  * complete binary degree 8    (9 cells)
...
j=9: X^76988 * S^10 * complete binary degree 0    (1 cell).
```

The dimensions sum to `10+9+...+1=55`. Since the target NTT domain excludes
zero, every fixed `X^(76979+j)` is a local unit at every target node. Thus the
X-window staircase itself creates no new local contact order. Global
simultaneous-node compatibility remains a separate issue.

If a future bridge sends `R` to the weight-two conic `C0` and `S` to the
weight-one conic `C1`, every original binary monomial has contact offset

```text
2*i + (10-i) = 10+i.
```

The fringe factorization preserves this exact offset:
the fixed `C1^(j+1)` contributes `j+1`, while the residual degree-`9-j`
sector contributes `(9-j)+i`, again totaling `10+i`. Consequently the common
rectangle plus fringe would fit the discussion formula without an X-window
loss *if* the missing initial-form bridge existed.

## 4. Provenance of the three top contact rows

Each origin polynomial produces three correlated charge-13 top rows:

```text
type  (f,aE,cS,rawR,h)   target (T,E,R,S,Z)             scalar mod p  u1 power
A     (7,6,1,0,54)       (2,6,21-s,s+1,2675)             603758703       54
B     (8,5,3,0,53)       (6,5,21-s,s+3,2674)             693269975       53
C     (8,6,1,1,53)       (3,6,22-s,s+1,2674)             642373467       53
```

For each type, `2*aE+cS=13` and `E+R+S+Z=2703`. The scalars satisfy

```text
C = 54*A,       B = C/4                  in F_2130706433.
```

This shared provenance must be retained. The 33 displayed rows are three
outputs of eleven coefficient blocks, not 33 separately choosable columns.

## 5. Exact mismatch with discussion #530

The discussion lemma applies to a **literal complete saturated local sector**

```text
C0^i C1^(N-i) (Y-v)^j
```

and gives order

```text
min_{i,j} (ord_t(a_ij) + N+i+j),
```

together with the stated `t^[q-N-i-j]+` divisibility. The Full187 census
supplies the right index simplex and, by Sections 2--3, the right strict
windows. It does not supply the local generators:

1. `R,S` are source derivative variables; `C0,C1` are uniquely constrained
   conics with initial forms in `U,t,Z`. Equality of exponent diagrams is not
   equality in the filtered local ring.
2. The fixed carrier `B=Y^61 R^11 Z^2621` has not been shown to have a regular
   nonzero initial form of known contact order.
3. `Y^61` is not a fixed power of the centered variable `(Y-v)` uniformly in
   the received value; centering expands it into correlated layers.
4. The three principal target rows in Section 4 share one source polynomial
   and two different powers of `u1`; the discussion lemma does not by itself
   justify separating them.

Therefore this lemma is not yet a target charge-13 theorem. The exact
rectangle/fringe result removes the window objection, but the algebraic
identification remains wholly unproved.

## 6. Smallest useful missing theorem

Let

```text
B = Y^61 R^11 Z^2621.
```

The narrow bridge to prove at each nonzero target node `x` is an
associated-graded statement of the following shape (pseudocode, not a proved
declaration):

```lean
theorem full187_charge13_initial_bridge (x : Domain) :
  exists (kappa : Nat) (b : gr_x kappa),
    b != 0 /\ IsRegular b /\
    exists (u : Fin 11 -> gr_x 0),
      (forall i, IsUnit (u i)) /\
      forall i : Fin 11,
        initial_x (localize_x (B * R^i * S^(10-i))) =
          b * u i * initial_x(C0)^i * initial_x(C1)^(10-i)
```

Here `C0,C1` must be the actual discussion conics, not renamed `R,S`. A
filtered unit-triangular variant is acceptable, but it must preserve the
weight-two/weight-one leading terms. Under this bridge, the discussion lemma
would yield the genuinely useful local target statement

```lean
theorem full187_charge13_common_exact_order
    (p : Fin 11 -> K[X])
    (hp : forall i, (p i).natDegree < 76979) :
  ord_x (localize_x
    (B * sum i, p i * R^i * S^(10-i))) =
  kappa + min_i (ord_x (p i) + 10 + i)
```

plus ten scalar-coefficient fringe instances with residual degrees
`9,8,...,0`. This would prove a local saturation/no-cancellation theorem for
the Full187 charge-13 block. It still would not, alone, prove global
all-node CRT compatibility, the four packet containment statement, or the
full 6900 mapping-cone recurrence.

The next decisive gate is therefore a symbolic associated-graded calculation
of the actual localized benchmark `R,S,B` against the conics' displayed
initial forms. If that fails to be regular and filtration-preserving, stop
this route immediately; further rank grids will not repair the mismatch.

## 7. Reproducibility

Exact executable:

```text
python3 .experiments/full187_charge13_common_sector_gate_6900.py
```

The accompanying Lean file proves the parameter, width, factorization,
fringe, and dimension identities using `omega`/`norm_num`, with no
`decide` or `native_decide`:

```text
.experiments/run_lean_4g_capped.sh \
  /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work/.experiments/Full187Charge13CommonSector6900.lean
```

It compiles successfully under the task-local 3.5 GiB Lean allocator cap.
