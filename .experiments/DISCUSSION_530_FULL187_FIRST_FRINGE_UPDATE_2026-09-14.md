### Lower 6900 update: 87% top projection, every first fringe closes, q26 closed

Context from scratch: the accepted production proof in this checkout is still
6806, the public lower frontier is 6808, and there is **not yet a 6900
candidate**.  This is a research update on the Full187 terminal route, with
exact target-field computations and explicit scope guards.

The terminal top map has now been reduced much further.  For all 187
derivative shapes and every contact degree `f<60`, prescribing every complete
all-node Hermite depth available in the strict coefficient window cancels

```text
17,793,064 / 20,415,725 = 87.1537209675%
```

of the top provenance.  Exactly 2,622,661 terms remain in 126,315 physical
`(r,s,f,q)` blocks, and every residual origin satisfies the strong local
capacity inequality (`2d678e8`).

An important correction followed.  Treating those residual rows as arbitrary
independent targets is false: their 98,862-row raw contact matrix has exact
rank 62,563 and cokernel 36,299, including 234 algebraic defects beyond Hall
matching (`b05608c`).  However, the *actual* Pascal residual retains one common
coefficient on each full contact power, so all of those raw left-duals vanish
identically on it (`b535ccc`).  The proof search is therefore staying at the
coefficient-polynomial level rather than claiming rowwise surjectivity.

There is also a closed form for that correlation.  The 60 descending Pascal
relations are the coefficients of

```text
(Y-U)^60 * sum_(i=0)^22 binom(59+i,i) U^i Y^(22-i)
  = Y^82 + sum_(f=0)^59 c_f U^(82-f)Y^f,

c_f=(-1)^(60-f) binom(82,f) binom(81-f,22).
```

Thus the full top question is one filtered fat-graph problem: move this single
local relation into all tapered coefficient windows using powers of
`Omega=X^N-1`.  The recent explicit reverse-Hasse duality formula for
hyperderivative RS codes gives a compact cokernel interface; on the
multiplicative domain its local triangular correction is node-independent up
to powers of the node (`c6374d8`).

The first filtered obstruction is now completely green.  All 9,482
first-fringe blocks reduce to 219 distinct adjacent-window maps.  Bandwidth
one always fails, but bandwidth two passes **every** block.  Exact Toeplitz /
Hankel ranks range over the two endpoint families 54,086..54,195 and
185,159..185,268; the worst block is `(r,s,f,q)=(0,0,0,41)`, and it also has
full rank.  The audit runs in 23 seconds at 231 MiB (`9192095`).

The previously isolated charge-13 `f=8,q=26` obstruction is independently
closed for all 11 shapes.  Legal variations

```text
delta P8 = Omega^26 A,
delta P9 = Omega^26 B
```

produce `A+9*u1*B`; exact Hankel minors of sizes 54,136..54,146 are
nonsingular.  This handles an arbitrary q26 right-hand side while preserving
all q<=25 prescriptions (`14b5109`).

Two scope guards remain important:

1. these first-fringe greens are not yet a proof that the entire multi-q
   cascade closes; that full cascade is the current computation;
2. the complete-depth carriers and the strongest endpoint confluence still
   do not initiate the low-Z packets.  An exact augmented control retains a
   one-dimensional packet covector, and the literal F3 scalar remains
   separated (`4ad9979`).  The induced `u0`/lower-passive tails must be
   followed through the boundary quotient rather than inferred from support.

The two active gates are therefore (a) a complete reverse-Hasse/dual proof or
smallest counterexample for the multi-q tapered cascade, and (b) the boundary
class of the induced lower-passive tails.  Input on a theorem-sized
superregularity proof for these consecutive Toeplitz/Hankel windows, or a
filtered fat-graph/approximant-basis formulation, would be especially useful.

