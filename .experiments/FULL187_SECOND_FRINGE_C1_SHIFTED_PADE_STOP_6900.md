# Full187 smallest simultaneous second fringe: exact C=1 STOP

Date: 2026-09-14.  This is a lower-6900 experiment only.  Production and the
accepted submission are unchanged.

## Verdict

The adjacent first-fringe GREEN in `b535ccc`/`9192095` does not extend to the
next unsupported layer, even for the constant terminal coefficient `C=1`.
For the tight stream

```text
(r,s)=(11,10),  terminal contact exponent=61,
```

the honest simultaneous `f=58,q=1` and `f=57,q=2` system using the physical
`P57,P58,P59` windows has no solution over the target field.  An exact shifted
approximant basis gives

```text
legal shifted-degree threshold       76,986
minimum basis shifted degree         84,783
certified gap                          7,797
decision      STOP_C1_NOT_IN_THREE_POLYNOMIAL_SECOND_FRINGE_IMAGE
```

Thus the current top-shell Pascal/window cascade is not a full lift.  This is
not a statement about the corrected `F3` packet target, nor about a construction
that recruits lower contact degrees, other `(r,s)` streams, `u0` tails, or a
different packet identity.

## 1. Exact physical windows

With `Omega=X^N-1`, `N=262144`, the three strict coefficient windows are

```text
width(P59) = N  +  76,987
width(P58) = N  + 208,058
width(P57) = 2N +  76,985.
```

After the complete-depth section, write the remaining variations as

```text
delta P59 = Omega B,       deg B <  76,987,
delta P58 = Omega A,       deg A < 208,058,
delta P57 = (forced q1 adjustment) + Omega^2 D,
                            deg D <  76,985.
```

The `P57` order-one jet is not incorrectly frozen: it is recomputed after
choosing `A,B` so that the already-supported `f=57,q=1` equation remains zero.

At a domain root `x`, put `a=H_1(Omega)(x)=N x^-1`.  The normalized operators
used by the executable are

```text
H_1(Omega V)/a       = V,
H_2(Omega^2 V)/a^2   = V,
H_2(Omega V)/a^2
  = H_1(V)/a + (N-1)/(2N) V.
```

Keeping this last triangular term is essential.  After the forced `P57` q1
adjustment it converts exactly into the first `Omega` carry of the relevant
coefficient product.

## 2. Literal C=1 right-hand side

Here `J-r-s=61`, so the three contact coefficients are

```text
binom(61,59)=1,830,
binom(61,58)=35,990,
binom(61,57)=521,855,
binom(59,57)=1,711.
```

Let `[F]_i` denote the `Omega^i` digit of a polynomial.  The canonical lower
jets used only to define the residual are

```text
P59^0    = -[1830 U^2]_0,
P58^0    = -[35990 U^3 + 59 U P59^0]_0,
P57^<2   = -[521855 U^4 + 58 U P58^0 + 1711 U^2 P59^0]_(0,1).
```

If `t1,t2` are the negatives of the next two digits, the exact remaining
equations are

```text
A + 59 [U B]_0                         = t1,
D + [58 U A + 1711 U^2 B]_1           = t2.
```

No Hasse derivative, carry, or frozen-`U` term is discarded in this reduction.

## 3. Half-length two-sequence Padé reduction

Set

```text
a=208058, b=76987, c=76985, H=N/2=131072.
```

The first equation prescribes the ordinary product coefficients
`(UB)[a..N)`; call them `M=t1/59`.  Let `K_j=(UB)_(N+j)` be its high carry and
let `L` be the reversal of `K`, so `deg L<=b-2`.  Reverse `U` at degree `N-1`:

```text
U*(x)=x^(N-1)U(x^-1),
V*(x)=U*(x)^-1 mod x^H.
```

The first-fringe equation is equivalent to

```text
[x^b,...,x^(H-1)] V*(L+M*) = 0.
```

The omitted coefficient at degree `b-1` determines the otherwise invisible
constant coefficient of `B`; it is not silently lost.  On the selected part
`j=a-1,...,N-1` of the second equation, `UA` has no coefficient at degree
`N+j`.  Hence the second equation becomes

```text
[x^(b-2),...,x^(H-1)] U* L = Btarget.
```

These are respectively `H-b=54,085` and `H-b+2=54,087` scalar constraints on
the `b-1=76,986` coefficients of `L`.  Encode them with the `4 x 2` series

```text
S = [ U*          V*       ]
    [ 1           0        ]
    [ 0           1        ]
    [ -Btarget    -Atarget ]       mod x^H,

Atarget = -V*M*.
```

A legal solution is exactly an approximant row `(L,Q1,Q2,1)` of shifted
degree at most `76,986` for

```text
shift s=(1,2,0,76986).
```

## 4. Exact basis certificate

LinBox's exact PM-basis algorithm over
`Fp`, `p=2,130,706,433`, returned shifted row degrees

```text
(84,783, 84,784, 84,783, 84,783).
```

The independent FLINT checker multiplies all eight row/series products and
confirms they vanish modulo `x^131072`.  It also checks

```text
sum(final shifts)-sum(initial shifts) = 262,144 = 2H,
s-leading 4x4 determinant             = 2,130,706,432 = -1 mod p.
```

Because `S` contains the two identity rows, its approximant module has
determinant degree `2H`.  The zero products, exact degree sum, and nonzero
shifted leading determinant therefore certify that the returned matrix is an
`s`-reduced basis.  The predictable-degree property then rules out every
nonzero approximant at shifted degree at most `76,986`; in particular it rules
out `(L,Q1,Q2,1)`.

Certificate receipts:

```text
input binary sha256
  c96393edeab68554487d97bae1024ade5d581397578cd5290840028bc4af84f2
basis binary sha256
  1ff7e342f0208a67d503385af26fd43ab1c089c6ae3d237019d8ff4930a857d6
basis bytes                         5,611,444
data-generator peak RSS              291,124 KiB
order-basis C++ peak RSS              843,940 KiB
independent verifier peak RSS         119,196 KiB
data/verifier script sha256
  9098972b5ea3da9c54453c8f58a8a0ea02dfe0bb565c965e7979019f3ca60a2a
order-basis source sha256
  8b3164645e61a5d776f9ee6646556bf876ec5d4b4710902519806e15cbf512a6
```

## 5. Consequence for scheduling

Do not spend more time trying to iterate the two-polynomial first-fringe
argument mechanically down the same Pascal stream.  It fails one layer later
on the easiest nonzero terminal coefficient.  The useful reusable object is
the `4 x 2`, order-`N/2` shifted-Padé formulation: a fixed packet target can be
inserted by changing only `Atarget,Btarget`, while retaining the same `U*,V*`
and exact certification path.

## Reproduction

```bash
cd /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work

prlimit --as=3221225472 --cpu=600 -- \
  python3 -B \
  .experiments/full187_second_fringe_order_basis_data_6900.py

g++ -O3 -std=c++17 \
  .experiments/full187_second_fringe_order_basis_gate_6900.cpp \
  -o /tmp/full187_second_fringe_order_basis_gate_6900 \
  $(pkg-config --cflags --libs linbox)

prlimit --as=3221225472 --cpu=1200 -- \
  /tmp/full187_second_fringe_order_basis_gate_6900

prlimit --as=3221225472 --cpu=600 -- \
  python3 -B \
  .experiments/full187_second_fringe_order_basis_data_6900.py \
  --verify-basis
```
