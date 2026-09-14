# Full187 all-noncapacity Pascal/Hermite slide

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production, the
accepted 6806 submission, `score.txt`, and `radius.txt` are unchanged.

## Verdict

The sharp-pivot/SCC route is not needed for the **top-diagonal structured
part** of the Full187 terminal map.  There is a direct, source-legal,
unitriangular Pascal/Hermite slide which cancels every terminal origin that
lacks the strong agreement-Hermite/error-value CRT license.

The complete target census is:

```text
all surviving terminal origins                         20,415,725
strong-capacity origins                                20,083,846
non-strong origins                                        331,879
  sharp-pivot licensed                                    294,912
  old local obstructions                                   36,967

distinct noncapacity (r,s,f) blocks                         6,709
maximum needed coefficient-Hasse order                         15
minimum all-node Hermite window slack                    339,119
```

For every one of the 6,709 blocks the noncapacity Hasse orders form an exact
initial interval `0,...,Q`.  The legal lower-active coefficient strip contains
the complete all-node Hermite algebra of depth `Q+1`.  This remains true in
the worst block `(r,s,f,Q)=(21,0,57,0)`:

```text
width = 601,263 = 1*N + 339,119.
```

The executable replays the descending recurrence as a formal sparse linear
expression over the target field.  It performs 41,480 block/Hasse zero checks.
To prevent a hidden canonical-lift assumption, it treats 36,899 higher Hasse
jets of already chosen correction polynomials as independent adversarial
symbols; every required coefficient still cancels.  The largest formal
expression has only 56 terms.

This is a substantial top-map reduction, but it is not yet the four-packet
theorem.  Terms containing the received constant `u0` land at lower passive
grade and are precisely part of the still-open connecting map.  The residual
top terms all have strong capacity individually, but a simultaneous physical
capacity section and its lower-passive tails still have to be propagated.

## 1. The literal terminal block

Fix one of the 187 derivative shapes `(r,s)` and put

```text
y = J-r-s,       z = L-J.
```

The terminal stream is

```text
C(X) Y^y R^r S^s Z^z.
```

At a node, use the literal substitution

```text
Y -> u0 + contactY + u1*Zseed,
contactY = E + Zseed*R - Zseed^2*S/2.
```

For coefficient-Hasse order `q`, the `u0`-free term of contactY degree `f`
has common coefficient

```text
binom(y,f) * u1^(y-f) * H_q(C).                 (TOP-y)
```

Expanding `contactY^f` gives all choices `(aE,cS)` with scalar

```text
multinomial(f;aE,cS,f-aE-cS) * (-1/2)^cS.       (LOCAL)
```

Every surviving scalar `(LOCAL)` is nonzero modulo the target prime: all
factorials are below 60, while `p=2130706433`.  It is therefore sufficient to
kill the common coefficient `(TOP-y)`; that simultaneously kills every local
monomial in the homogeneous `contactY^f` block, rather than treating colliding
row keys as independent coordinates.

## 2. Legal lower-active slides

For each selected contact degree `f`, add

```text
P_f(X) Y^f R^r S^s Z^(L-f-r-s).                 (SLIDE-f)
```

This is a literal Full187 source monomial.  Its active degree is `f+r+s`, its
total degree is `L`, and in all 6,709 selected blocks

```text
0 <= f+r+s <= 78 < J=82.
```

Thus every correction is strictly below the deleted active corner.  If the
`Y^f` term contributes contactY degree `k<=f`, using `f-k` copies of `u1*Zseed`,
its passive exponent is

```text
(L-f-r-s)+(f-k) = L-r-s-k
                         = (L-J)+(J-r-s-k),
```

exactly the same full passive row as the terminal stream at contact degree
`k`.  Its common coefficient is

```text
binom(f,k) * u1^(f-k) * H_q(P_f).                (TOP-f)
```

The diagonal at `k=f` is one.  In particular, the construction never divides
by `u1`; it remains valid at nodes where `u1=0`.

## 3. Descending Pascal recurrence

Let `F(r,s)` be the contact degrees having at least one noncapacity origin.
For each such degree let `Q_f` be its maximum noncapacity Hasse order.  The
exhaustive census proves

```text
noncapacity q set at (r,s,f) = {0,...,Q_f},
Q_f <= 15.
```

Process `f` in strictly descending order.  Once every `P_k` for `k>f` is
fixed, prescribe at every node and for `0<=q<=Q_f`

```text
H_q(P_f) = -binom(y,f) u1^(y-f) H_q(C)
           - sum_(k>f, k in F(r,s))
               binom(k,f) u1^(k-f) H_q(P_k).    (REC)
```

The diagonal contribution of `(SLIDE-f)` is exactly `H_q(P_f)`, so `(REC)`
makes the entire common coefficient at `(f,q)` zero.  Higher jets of `P_k`
which were not prescribed when `P_k` was constructed are already determined
values when the recurrence reaches `f`; `(REC)` adapts to them.  They need not
vanish and need not have a simple formula.  This is why the executable's
adversarial-symbol replay is load-bearing.

All-node Hermite CRT provides a polynomial of degree below `(Q_f+1)N` with
the prescribed jets.  The exact strip check is

```text
(Q_f+1)N <= D-wf-(w-1)r-(w-2)s.
```

It holds in every selected block, with minimum slack 339,119.  Therefore
every `P_f` in `(REC)` is source legal.

## 4. Exact classification after the projection

The status census uses the strong margin required to retain arbitrary scalar
data at all errors:

```text
width >= g*depth + (N-g).
```

Before the slide, origin counts are:

```text
                        q=0          q>0           total
capacity             1,186,372    18,897,474     20,083,846
pivot                    63,245       231,667        294,912
obstruction              17,308        19,659         36,967
```

After applying `(REC)` independently to every physical `(r,s)` stream, every
top homogeneous block labelled pivot or obstruction has zero common
coefficient.  Every remaining top provenance term is in the strong-capacity
class.  Cross-stream or positive-Hasse row collisions do not invalidate this:
the construction zeros the entire fixed-stream homogeneous polynomial before
different provenance terms are aggregated into a row key.

This also explains why the earlier row-by-row mixed graph had avoidable
cycles.  It expanded the sharp basis and tried to pivot individual monomial
rows.  The Pascal slide operates on the physical `contactY^f` block, where the
diagonal is literally one and the only direction is decreasing `f`.

## 5. What this does and does not close

Now exact:

- all 187 terminal derivative shapes are included;
- every surviving coefficient-Hasse origin is classified;
- every non-strong-capacity top block has a direct legal correction;
- all strict coefficient windows and the active-corner deletion are respected;
- unprescribed higher correction jets are carried, not set to zero;
- no inversion of a received value is used.

Still open:

1. A simultaneous, provenance-preserving section for the residual strong-
   capacity top blocks.  Individual capacity does not make reused physical
   source coordinates independent.
2. Every term in which a correction chooses at least one `u0`.  Such a term
   loses passive carrier grade and belongs to the lower connecting map.  It is
   supported only at error nodes, but it is not automatically zero.
3. The explicit low-`Z` packet precycle connecting exact `F0,F1,F2,F3` to the
   high-passive terminal absorber.  Commit `08d0efe` proves direct packet
   support and terminal-slide support are disjoint.
4. The resulting four-boundary Schur rank and the complete downstream
   `ProtocolClaim 6900` assembly.

The next decisive computation should therefore quotient the physical
strong-capacity section by `(REC)` and propagate its `u0` tails through the
low-passive connecting map.  Re-expanding the superseded sharp-pivot SCC is
lower information value unless that quotient forces us back to it.

## Reproduction

```bash
prlimit --as=1073741824 --cpu=180 -- \
  python3 -B \
  .experiments/full187_all_noncapacity_pascal_hermite_slide_6900.py
```

Recorded run:

```text
exit 0; elapsed 26.1 s; peak RSS 25,212 KiB
canonical sha256 df38112d08a773ca1e66d9a0055c92db6a8d772561dec493206a8d464b8a3672
script sha256    d9c351812caded22dd2cf90abfa6892b830180854d68fdff641bcf4037c7bcae
```
