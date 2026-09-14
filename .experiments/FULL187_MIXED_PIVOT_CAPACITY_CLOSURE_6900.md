# Full187 mixed sharp-pivot / strong-capacity closure

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production,
submission, score, and radius files are unchanged.

## Verdict

The 70,543 live rows which stopped the sharp-pivot-only induction are **all**
covered by the strong Hermite/error-value capacity branch once the literal
full 187-shape source is used:

```text
covered within the terminal-safe 103 shapes       63,094
requiring one of the other 84 shapes                7,449
covered within the full 187 shapes                 70,543
uncovered                                               0
```

The 7,449 extra witnesses do not violate the terminal deletion.  Each has a
legal lower-active representative

```text
P(X) Y^f R^r S^s Z^(L-f-r-s)
```

of active degree only 22 through 44, strictly below `J=82`.  It lands in the
same complete passive row as the original terminal remainder, uses no
received-direction factor, and has exactly the strong-capacity coefficient
width.

This changes the earlier result from “70,543 unsupported exponent rows” to
“zero unsupported exponent rows in the mixed basis.”  It is a genuine
support/window/source-legality improvement, but it is **not yet a global
reducer**.  A raw capacity correction has other contact tails, and the
smallest example already forms a two-cycle with a sharp pivot.  Those cycles
must be eliminated as blocks (their first literal `2 x 2` determinant is
nonzero), or otherwise oriented, before claiming confluence or packet
containment.

## Starting STOP and exact replay

The prior sharp-only audit begins with 70,056 pivot origins and 8,164 distinct
rows.  Transitive expansion through the sharp order-two basis reaches:

```text
sharp-pivot rows in the closure                   49,048
live successor edges                           3,444,163
contact-truncated successor terms              7,242,188
distinct live successors without a sharp pivot    70,543
```

Every sharp remainder has strictly greater shifted contact weight, but a
strictly increasing weight was not enough because those 70,543 rows lacked a
second sharp pivot.  The new audit retains that exact closure and searches
the independent strong-capacity origins, rather than modifying the old row
counts.

## Mixed capacity witnesses

For a source shape `(r,s)` and a contact choice `(f,aE,cS,q)`, put

```text
contactWeight = q + f + 2*aE + cS,
depth         = 60 - contactWeight,
width         = D - w*f - (w-1)*r - (w-2)*s.
```

The strong branch is licensed by

```text
g*depth + (N-g) <= width,
```

which is exactly the target specialization of the proved mixed
agreement-Hermite/error-value CRT.  For every escaping row the executable
finds such a witness in the full 187-shape source.  Deterministic minimum-
active-degree witnesses use only coefficient-Hasse order zero or one:

```text
q=0: 49,805 rows
q=1: 20,738 rows.
```

This is substantially simpler than the original provenance, whose pivot
origins reach Hasse order 12 in the safe 103 face (and 15 in the full face).
The chosen capacity depths range from 1 through 51.

## Why the other 84 terminal shapes are legal here

The terminal-safe restriction deletes an unsafe `(r,s)` only at the
intersection

```text
active grade = J=82,  total grade = L=2703.
```

Suppose an escape row has a capacity witness `(r,s,f,aE,cS,q)`.  In the
terminal notation its last coordinate is

```text
h = J-r-s-f.
```

Replace terminal `y=J-r-s`, `z=L-J` by

```text
y' = f,
z' = L-f-r-s.
```

Then the source active degree is `f+r+s<J`, its total grade remains `L`, and
the complete passive output is unchanged:

```text
z' = L-f-r-s = (L-J) + h.
```

Taking all `f` copies of `Y` as contact factors uses received-direction
exponent zero.  The other contact coordinates are literally

```text
(T,E,R,S)
  = (q+f-aE+cS, aE, f-aE-cS+r, s+cS),
```

the same row that escaped the sharp basis.  Its X window is the certified
`width(f,r,s)`.  Thus the source is legal independent of whether `(r,s)` was
deleted at the terminal corner.

For the 7,449 rows that specifically need a non-103 shape, the chosen active
degree histogram spans exactly 22 through 44; none is remotely at the deleted
active grade 82.

## The exact remaining hazard

Row coverage is not tail confluence.  The smallest sharp escape is

```text
e = (T,E,R,S,passive) = (0,3,0,8,71),
```

coming from sharp parent

```text
p = (2,2,0,9,71).
```

Its minimum capacity witness is `(r,s,f,aE,cS,q)=(0,8,3,3,0,0)`, with
margin 181,952.  In the two-row span `(e,p)`, the sharp generator has
coefficients `(1,-1/2)` while the raw capacity source has `(1,-3/2)`.  Hence
the naive arrows `p -> e` and `e -> p` make a two-cycle.  Their coefficient
matrix has nonzero determinant, so the cycle is locally eliminable as a
block; nevertheless, an acyclic one-row-at-a-time proof is false.

The next exact task is therefore bounded and testable:

1. build strongly connected components of the mixed sharp/capacity tail
   graph with source provenance and coefficient windows;
2. check each diagonal block over the target field (or prove its Pascal/
   Hasse determinant symbolically);
3. orient the component graph and replay all outgoing tails;
4. apply the resulting correction section to exact `F0,F1,F2,F3`, with the
   fourth row equal to the partial-locator `F3`, never pure `Z1`.

## Scope guard

What is now exact:

- every sharp-only escape has a strong-capacity source row;
- every selected source row respects the exact half-open X window;
- all formerly unsafe-shape witnesses have a legal lower-active realization;
- all full passive row coordinates and source grades agree literally.

What remains open:

- simultaneous choice of the CRT correction maps;
- every other contact and boundary tail of those choices;
- block invertibility/termination for all mixed components;
- the induced four-packet Schur map and the downstream 6900 count.

## Reproduction

```bash
prlimit --as=1073741824 --cpu=180 -- \
  python3 -B .experiments/full187_mixed_pivot_capacity_closure_6900.py
```

Recorded run: exit zero in about 83 seconds, about 110 MiB peak RSS.

```text
canonical sha256 0f5b9e80cf07f8161b4e89d02763d26c35d03d255b274261ae64359ed067cdc9
script sha256    603e44314eee915e47dc1cc9a1205d1b0a2dde4bf561078d59d2b35438e4edd5
```
