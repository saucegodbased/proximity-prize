# Full187 maximal complete-depth Pascal/Hermite slide

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production and the
accepted 6806 submission are unchanged.

## Verdict

The descending Pascal slide from commit `7504148` extends far beyond the
331,879 origins which actually need it for local licensing.  Using every
legal lower-active contact degree and every complete all-node Hermite jet
available in its strict coefficient window cancels

```text
17,793,064 / 20,415,725 = 87.1537209675%
```

of all terminal top provenance terms.  The residual is exactly

```text
2,622,661 provenance terms
126,315 physical (r,s,f,q) blocks
98,862 distinct row shapes.
```

Every residual origin is in the strong agreement-Hermite/error-value capacity
class.  This is checked against the literal target predicate, not inferred
from the percentage.

The projection is blockwise, not row-key diagonal.  Of the 415,253 row shapes
hit by canceled provenance, 94,165 are also hit by residual higher-Hasse
provenance.  Those coordinates must not be called zero after aggregation.
What is zero is the complete fixed-stream homogeneous coefficient for every
prescribed `(r,s,f,q)` block.

## Construction

For each of the 187 shapes `(r,s)` and every `0<=f<60`, put

```text
width(r,s,f) = 60g-wf-(w-1)r-(w-2)s,
A(r,s,f)     = floor(width(r,s,f)/N),
Q(r,s,f)     = min(A(r,s,f)-1, 59-f).
```

All 11,220 blocks have `A>=1`; the complete depth ranges from 1 through 41.
Use the physical source coefficient

```text
P_f(X) Y^f R^r S^s Z^(L-f-r-s).
```

Its active degree is at most `59+21=80<J=82`, its total degree is `L`, and
its top passive exponent agrees exactly with the terminal stream.  Prescribe
all node jets `H_q(P_f)` for `0<=q<=Q(r,s,f)` by the descending recurrence
from `7504148`:

```text
H_q(P_f) = -binom(J-r-s,f) u1^(J-r-s-f) H_q(C)
           - sum_(k>f) binom(k,f) u1^(k-f) H_q(P_k).
```

The source strip contains the canonical all-node Hermite representative
because

```text
(Q+1)N <= A*N <= width.
```

No received value is inverted.  Higher jets of each `P_k` are not assumed
zero: the executable inserts an independent formal symbol for every such jet
and lets later lower-`f` prescriptions adapt to it.

Exact formal replay:

```text
physical correction blocks                         11,220
prescribed block/Hasse coefficients                215,895
adversarial unprescribed higher-jet symbols         169,965
maximum sparse formal expression size                   60
minimum unused fringe after A complete node jets    76,876
```

The 76,876 fringe occurs at `(r,s,f,A,Q)=(0,0,0,41,40)`.  It is not used to
pretend there is another complete jet.

## Exact interpretation

At fixed `(r,s,f,q)`, the top `u0`-free source contribution factors as

```text
commonCoefficient * contactY^f * R^r * S^s.
```

The recurrence makes `commonCoefficient=0` before expanding `contactY` into
its `E`, `Z*R`, and `-Z^2*S/2` monomials.  Therefore it cancels all local
choices `(aE,cS)` in that homogeneous block simultaneously, even when those
terms later share row keys with other streams or Hasse orders.

For every block, `q<=Q` is canceled.  Any surviving origin has

```text
q >= A(r,s,f).
```

The older noncapacity audit proves—and this executable independently checks
on all 2,622,661 residual origins—that such an origin satisfies the strong
mixed CRT inequality.  Thus the top diagonal is reduced to a physical
capacity quotient rather than the earlier sharp-pivot/cycle graph.

## Interaction with the q26 ninth-difference bypass

For charge 13 at `(r+s,f,q)=(21,8,26)`, the y=8 strip has exactly 26 complete
node jets, so this maximal projection cancels q=0 through 25 and stops at
q=26.  Commit `d1620d8` gives a genuine structural bypass of that first
fringe using a ninth finite difference across derivative/contact layers.

That bypass must be integrated by replacing the affected complete-depth
prescriptions, not blindly superposed on them: several of its physical jets
lie inside the new q<=Q projection for shifted streams.  The prior
`50096c7` compatibility statement was made against the weaker noncapacity-
only projection `7504148`; it is not automatically a compatibility proof for
this stronger 87% projection.  This conflict has been sent back for an exact
aggregate-row re-audit.

## Remaining gate

This result does not prove a terminal kernel or a packet lift.

- The 2,622,661 residual terms have individual strong-capacity licenses, but
  physical source coordinates are reused.  A simultaneous section must be
  constructed on those physical blocks rather than counting row witnesses.
- Any correction term selecting at least one `u0` loses passive carrier grade.
  Those error-supported tails form the coefficient-sensitive connecting map;
  they are retained.
- Exact packets `F0,F1,F2,F3` live at low passive `Z`, while these terminal
  slides live around `Z=2621...2703`.  Commit `08d0efe` proves their direct
  supports are disjoint.  A causal passive-raising precycle is mandatory.

The two highest-information next tasks are therefore the residual physical
capacity section and the low-Z-to-terminal connecting bridge.  Re-running the
superseded sharp row graph is not useful unless one of those gates forces it.

## Reproduction

```bash
prlimit --as=1073741824 --cpu=180 -- \
  python3 -B \
  .experiments/full187_complete_depth_pascal_hermite_slide_6900.py
```

Recorded run:

```text
exit 0; elapsed 59.7 s; peak RSS 107,300 KiB
canonical sha256 84f03942ec345d6a9efc0c0ec01b191e688b89260ad1f3ae00ccacc86423e02a
script sha256    e6de6ca5273bcae6e369b7ffd779c815a393c6e7e3494ee8853f7c3ab1d46969
```
