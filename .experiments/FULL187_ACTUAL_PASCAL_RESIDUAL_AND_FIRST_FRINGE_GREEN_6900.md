# Full187 actual Pascal residual and first physical fringe: GREEN

Date: 2026-09-14.  This is a lower-6900 experiment only; production and the
accepted submission are unchanged.

## Outcome

The exact raw-column rank STOP in `b05608c` does **not** obstruct the actual
Pascal residual.  Every actual residual common coefficient—including the
terminal `C` jet and all unprescribed higher jets of the previously selected
`P_k`—multiplies one intact raw contact polynomial.  Hence the complete actual
residual is in the image of the raw block matrix and all 36,299 raw left-duals
vanish automatically.

The real obstruction is coefficient-window compatibility after lower Hasse
jets have already been fixed.  The tightest first-fringe instance reduces to
an exact Toeplitz/Hankel map for the frozen target `u1`; that map is full row
rank.  Thus the first direct physical fringe gate is GREEN, and the next gate
is the whole multi-contact/multi-Hasse cascade rather than another raw-row SCC.

## Actual residual factorization

For a stream `(r,s)`, contact degree `f`, and surviving order `q`, complete
depth is monotone in `f`.  Therefore `q>Q_f` implies `q>Q_k` for every `k>=f`.
Every `P_k,q` appearing from above is genuinely an unprescribed higher jet.
The actual common coefficient is

```text
B_(r,s,f,q)
 = binom(J-r-s,f) u1^(J-r-s-f) C_q
   + sum_(k=f)^59 binom(k,f) u1^(k-f) U_(k,q),
```

and its entire contribution is

```text
B_(r,s,f,q) Z^q contactY^f R^r S^s.
```

The executable checks monotonicity 11,033 times and accounts for all 126,315
residual blocks.  No coefficient window, Hasse tail, or contact expansion is
collapsed.

For the smallest Hall dual from `b05608c`, `(r,s,f,q)=(0,10,1,35)`, the common
coefficient is the 60-symbol expression

```text
72 u^71 C_35 + sum_(k=1)^59 k u^(k-1) U_(k,35).
```

Its `S` and `E` rows are `(-1/2)B` and `B`; the dual `(2,1)` gives zero
coefficientwise for all 60 independent symbols.  The same factorization proves
the statement for every raw-column left dual at once.

## Why individual capacity is insufficient

Write a coefficient window as `width=A*N+rho`.  Fixing Hasse jets
`0,...,A-1` at all `N` nodes leaves only `rho` coefficient dimensions.  For
all 9,482 residual-bearing polynomials, this individual fringe is smaller than
the mixed-capacity cost of the first residual order.

The tightest individual failure is

```text
(r,s,f,q)                 (11,10,58,1)
width(P58)                470,202 = N + 208,058
remaining rho             208,058
depth-one mixed cost       262,144 = N
individual deficit         54,086.
```

So the complete-depth projection cannot be followed by independent capacity
interpolation in the same `P_f`; adjacent higher-contact fringes must be used.

## Exact adjacent-degree rescue

The adjacent polynomial has

```text
width(P59) = 339,131 = N + 76,987.
```

After preserving both prescribed order-zero jets, variations are

```text
delta P58 = Omega*A,  deg A < 208,058,
delta P59 = Omega*B,  deg B <  76,987,
Omega = X^N-1.
```

At a domain node `x`,

```text
H_1(Omega*V)(x) = N*x^(-1)*V(x).
```

After removing this common invertible diagonal, the `f=58,q=1` variation is

```text
A + 59*u1*B.
```

Quotienting the freely controlled low 208,058 coefficients leaves a
`54,086 x 76,987` Toeplitz map.  In the literal frozen `u1` coefficient vector,

```text
T[i,j] = U1[208058+i-j].
```

Reverse the columns and select the last 54,086 input monomials.  The resulting
square Hankel matrix uses the sequence beginning at coefficient 131,072.
FLINT Berlekamp--Massey on the exact `2*54,086=108,172`-term determinant
certificate returns complexity exactly 54,086 and remainder degree 54,085.
By the standard Hankel/Berlekamp--Massey criterion, this square minor has
nonzero determinant.  Consequently the full rectangular map has exact rank
54,086 and the joint first-fringe map is onto all 262,144 node values.

```text
nominal joint surplus                         22,901
connection endpoints                1340672286, 872149071
certificate sequence sha256
  be8b8095378b5a0998dee725a01687ef0d45e2b4831f7d64ebc27b95e3184672
connection sha256
  674e30f69b5dc5aa8978a91de600d25965542ff829dce0af015afd5ad586ac8d
```

This is strictly an X-window confluence result.  It does not transport a
low-passive packet to passive grade 2624, dispose of `u0` tails, or prove that
the remaining lower-`f` and higher-`q` equations can all be solved without
reusing the same fringe freedom.

For a future dual proof of the general Hermite map, use the corrected local
hyperderivative weights

```text
w_(i,j)(g) = v_j^(-1) H_(s-i)(g/A_j)(alpha_j),
```

with reversed Hasse order and its local triangular `A_j` factors.  A naive
reversed-HRS dual drops those factors and is not a valid uniform theorem.

## Reproduction

```bash
cd /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work
prlimit --as=2147483648 --cpu=900 -- \
  python3 -B \
  .experiments/full187_actual_pascal_residual_and_first_fringe_gate_6900.py
```

Recorded run:

```text
exit 0
peak RSS       192,484 KiB
canonical sha  a285518b5274462dcaa1a4fc77af24be7a04f7896be87b84ea92a35243fe6df9
script sha     4f71084905369899563eb496f2b9b044245107bd7a3357aac35336709b02da15
```
