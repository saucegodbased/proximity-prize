# k=0 two-error rank-adaptivity gate

Date: 2026-09-14 UTC. Scope: lower-6900 exact-`G` research only. This is a
small exact discriminator, not a target theorem, candidate, or submission.

## Verdict

**GREEN for conormal gain in the tested two-error patterns; RED for a single
fixed maximal-contact bordered minor.**

The one-error algebraic-closure certificates in `9665cbc` and `605c468`
suggest adjacent carrier charts. Before extrapolating their fixed contact
pivots, this gate adds the smallest second error while retaining the same
literal full-cutoff source:

```text
F_101,
(n,w,g,m,B,s,U,L,k,n0)=(6,2,4,3,3,1,4,6,0,1),
D=12,
source columns=815,
contact quotient rows=750.
```

After the usual safe normalization,

```text
u0=(0,0,0,0,1,1),
u1=(0,0,0,1,b,c),
Q_G(4)=4,
Q_G(5)=10.
```

At the boundary point `X=6`, exact modular ranks are:

```text
direction pattern        contact rank   augmented rank   conormal gain
matched       (4,10)          724             728              4
first only    (0,10)          726             730              4
second only   (4, 0)          726             730              4
both          (0, 0)          722             726              4
generic       (7,13)          724             728              4
```

Thus the desired rank-four phenomenon survives these first two-error tests,
but the old contact rank is not constant even inside one normalized family.
In particular, a fixed `730 x 730` minor selected in either single-mismatch
chart must vanish on the both-mismatch point: there the entire augmented map
has rank only 726. The executable checks this directly. A smaller matched
chart also fails to be a universal determinant, despite the intrinsic
boundary gain remaining four.

This is not a counterexample to the current route. It is a counterexample to
the tempting proof schema

```text
choose one maximal contact pivot once;
append four fixed boundary columns;
factor the resulting determinant uniformly across every error pattern.
```

The target proof must be rank-adaptive (quotient/dual-module language), or
provide a family of minors indexed by the live mismatch pattern. This makes
the linear factor-through route more attractive: rank defect says a boundary
functional lies in the dual image of the contact map, producing compatible
local dual equations without choosing a fixed contact basis. Those equations
still have to be connected to the exact-G partial-locator/Hasse source; that
is the open theorem.

## Reproduction

```text
prlimit --as=8589934592 --cpu=600 -- \
  python3 -B .experiments/k0_two_error_adjacent_probe_6900.py
```

The deterministic run takes about 30 seconds and peaks below 70 MiB. It uses
exact finite-field linear algebra, no random sampling, floating point,
`decide`, or `native_decide`.
