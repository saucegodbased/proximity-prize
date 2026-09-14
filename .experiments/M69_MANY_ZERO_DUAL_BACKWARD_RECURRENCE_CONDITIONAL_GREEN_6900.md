# m69 many-zero dual chain: exact conditional GREEN and X² correction

Date: 2026-09-14 UTC. Scope: lower-6900 research only; no production or
submission root is changed.

## Verdict

There is a uniform, exact **many numerator zeros** theorem behind the m69
profile, conditional on the standard prefix-dual adapter.  For every one of
the `6930` rank-insensitive deficient physical shapes, if

```text
deg E >= 2151,
#{domain nodes where N=0} >= 1125,
deg N <= 149776,
```

then the paired dual recurrence kills every paired kernel.  Consequently:

* a high-initial prefix shape has no nonzero dual annihilator;
* a low-initial prefix shape can have a dual annihilator only on the
  numerator-zero set.

The second conclusion is exactly what an actual target divisible by `W=N/E`
needs: every zero-supported dual kills such a target.  Commit `56267de`
subsequently proves that divisibility for all `140153` deficient residuals.
The concrete prefix-dual adapter and common source allocation/confluence are
still separate Full187 obligations.

## Important correction: there is no X² factor

The recovered informal argument said that the pair-to-pair recurrence was

```text
N^2 K_j = X^2 E^2 K_(j+1).
```

That normalization is not compatible with the literal physical envelope

```text
sum_t W^t F_<f_t>,       W=N/E.
```

For a prefix dual, use the standard nodal encoding

```text
lambda_i W_i^t = x_i H_t(x_i).
```

The same factor `x_i` occurs for every prefix length.  From the `t` and
`t+1` encodings and `E_i W_i=N_i`, cancellation of nonzero `x_i` gives

```text
N_i H_t(x_i) = E_i H_(t+1)(x_i).
```

There is no residual `x_i`.  After an adjacent high/low pair is upgraded to
a polynomial equality, coprimality gives

```text
H_high,j = E K_j,
H_low,j  = N K_j.
```

Using the intervening low/high nodal relation gives the exact recurrence

```text
N_i^2 K_j(x_i) = E_i^2 K_(j+1)(x_i).                 (1)
```

`M69ManyZeroDualBackwardRecurrence6900.lean` formally proves both the
adjacent calculation and this substitution.  Thus the orientation is
validated and the spurious `X^2` has been removed.  The earlier theorem
`M69RationalTwoPowerGate6900.short_square_nodal_relation_forces_zero` has also
been corrected to state the physical no-`X²` relation.  Historical receipts
that quote its former `X²` premise must not be cited as source adapters.

The many-zero argument itself survives this correction.  It only needs a
nonzero coefficient multiplying `E^2 K_(j+1)` at numerator roots; equation
(1) supplies coefficient one.

## Complete all-shape enumeration

The executable
`m69_many_zero_dual_chain_all_shape_gate_6900.py` imports the frozen exact m69
census with source SHA256

```text
9417a5797aa188cb6a1381b7c11e54f3df0ecf46908ad452d6dee925e1ae5069
```

and rechecks all `13093` defective Pascal strata, all `6930` deficient
shapes, and all `140153` deficient coefficients.

For a shape `(y,r,s)`, it enumerates every available power
`t=0,...,68-y`.  The prefix fringe alternates high/low because

```text
Wcode = 131071 = 262144/2-1.
```

Across two powers a high fringe rises by exactly two, so its dual cap falls
by exactly two.  Every shape has between `13` and `34` high-then-low pairs.
There is therefore always a preceding pair from which to force the last
kernel on the numerator-zero set.

Exact census:

```text
initial high shapes                 3546
initial low shapes                  3384
pair-count range                    13..34
last paired high-cap range          3218..3276
maximum high cap in any pair        3342
maximum paired-low cap              134413
receipt SHA256
  8ad6e1b9955ba10fca212b8699352a46312ec265b50c7f2a079d3f4c790c44c0
```

The adjacent high/low relation is genuinely no-wrap over the entire current
DataEleven degree box.  With `deg N<=149776`, `deg E<=18414`, and strict dual
cap bounds, the two polynomial degree maxima are

```text
deg(N H_high) <= 149776+3342-1  = 153117 < 262144,
deg(E H_low)  <= 18414+134413-1 = 152826 < 262144.
```

So agreement on all NTT nodes upgrades to a polynomial equality, and
`IsCoprime E N` legitimately gives the common kernel normal form above.

## Root migration and backward killing

Let `Z` be the domain zero set of `N`, of size `z`.  At every `i in Z`, (1)
and root-freeness of `E` give

```text
K_(j+1)(x_i)=0.
```

For the last pair, if its high cap is `c_last`, then

```text
deg K_last < c_last-deg E.
```

All shapes satisfy `c_last<=3276`; hence

```text
deg E>=2151 and z>=1125
  => c_last <= deg E+z
  => deg K_last < z.
```

The `z` distinct roots force `K_last=0`.  Equation (1), now read backwards,
forces `K_(last-1)` to vanish wherever `N` is nonzero.  Since a nonzero
degree-`149776` numerator has at most `149776` domain roots, there are at
least

```text
262144-149776 = 112368
```

nonroots.  Every earlier kernel has strict degree below

```text
3342-2151 = 1191,
```

so these nonroots kill it globally.  Backward induction kills all kernels.

The Lean theorem

```text
nodal_square_recurrence_chain_forces_zero
```

formalizes this root-then-complement induction for an arbitrary finite field,
injective node embedding, finite root/nonroot sets, and arbitrary chain
length.  Supporting theorems formalize finite-set polynomial rigidity,
no-wrap equality, coprime high/low factorization, exact no-X adjacent and
paired relations, and the endpoint degree calculation.

## Two literal controls

For the hostile low-initial shape `(0,0,0)`:

```text
available powers             69
first paired high t          1
first high cap               3342
last paired high t           67
last high cap                3276
threshold at deg E=2151      1125 zeros
```

Thus the old `127730`-zero countermodel does not defeat the full paired chain:
its positive-power dual portion is killed, and any remaining annihilator is
supported on those zeros.  It still defeats arbitrary target surjectivity;
the distinction is precisely whether the actual target vanishes there.

For the literal first descending defect `(39,14,10)`:

```text
available powers             30
first pair t=0/1 caps        3246 / 134317
last paired high t           28
last high cap                3218
threshold at deg E=2151      1067 zeros
```

The uniform `1125` threshold is forced only by the low-initial `(0,0,0)`
edge; the first defect itself needs `1067`.

## Exact scope and next theorem

The following implications are proved or exactly enumerated:

1. standard nodal dual encodings imply the adjacent no-X relation;
2. every high/low adjacent relation is below degree `262144` in the exact
   m69 DataEleven box;
3. coprimality gives one kernel per high/low pair;
4. the oriented paired recurrence plus `z>=1125` kills all pair kernels;
5. high-initial annihilators then vanish, while low-initial annihilators are
   supported on `Z`.

The remaining source obligations are not hidden:

1. formalize existence of the standard `H_t` prefix-dual encodings for the
   concrete NTT pairing used by Full187;
2. compose commit `56267de`'s all-residual `W` divisibility with the dual
   conclusion, jointly with the already prescribed lower jets;
3. prove simultaneous allocation/confluence across shared physical source
   variables.

The maximum-information next test is item 2 over the complete `140153`
coefficient census.  If it is GREEN, the many-zero branch is structurally
closed modulo the mechanical dual adapter and global confluence.  If any
low-initial coefficient has a genuine `W^0` incoming term, this route needs a
different zero-set interpolation argument for that exact shape.

## Reproduction and verifier hygiene

```bash
cd /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work

prlimit --as=536870912 --cpu=300 -- \
  python3 -B \
  .experiments/m69_many_zero_dual_chain_all_shape_gate_6900.py

env LEAN_NUM_THREADS=1 lake env lean -j1 -M3500 \
  .experiments/M69ManyZeroDualBackwardRecurrence6900.lean
```

The Python run reports roughly `40 MiB` peak RSS.  The Lean build succeeds
with its internal `-M3500` cap and prints only the standard axiom set

```text
[propext, Classical.choice, Quot.sound].
```

No `sorry`, `admit`, `unsafe`, `decide`, or `native_decide` is used.  A hard
OS address-space cap around `4 GiB` can prevent the Lean runtime from creating
its worker thread even with `LEAN_NUM_THREADS=1`; that launcher failure is not
a proof failure, so the successful internal Lean cap is the recorded build
receipt.
