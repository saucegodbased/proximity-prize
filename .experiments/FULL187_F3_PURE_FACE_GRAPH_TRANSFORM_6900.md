# Full187 F3 pure face: exact graph transform and scalar-dual STOP

Date: 2026-09-14

## Decision

The necessary `R=S=Z=0` face of every Full187 F3 lift has now been reduced
exactly to one graph-fatpoint shifted-Padé problem.  Put

```text
a = G-W = 49342,
F(V) = G^-60 K(GV) = sum_(n=1)^82 C_n V^n.
```

Then the literal source and contact conditions are equivalent to

```text
deg C_n < n*a,
C_0 = 0,
C_1 = Rloc,                    deg Rloc = a-1,
G^(n-60) | C_n                 for 60 <= n <= 82,
F in (E,V-A)^60,               A = G^-1 mod E^60.
```

Already modulo `E`, the center has the target-exact closed form

```text
A = N^-1 X E' mod E,
```

because `G E = X^N-1`.  The executable checks this on the frozen target.

This is a **GREEN compression**, not a membership result.  It removes all
319,331,010 agreement constraints and replaces the original two-line system
by one 83-coefficient shifted graph module.  The remaining source dimension
is 122,266,337 against 149,567,730 error conditions.  With `A_1=B` fixed,
the correction space has dimension 122,216,995, so the exact codomain deficit
is 27,350,735.

The first attractive scalar-dual shortcut is now rigorously **STOPPED**.  If
`P(t)` has degree `d`, Euler/Hasse combination of the graph conditions gives

```text
E^(60-d) | sum_n P(n) A_n.
```

Whenever one unrooted lane has free width at least
`(60-d) deg(E)`, that lane alone is onto the quotient and the scalar
condition cannot distinguish the target.  A degree-`d` polynomial can kill
at most `d` distinct lanes.  The exact census proves:

```text
E-adic orders k=1,...,16: every scalar projection is surjective;
k=17: 43 individually-surjective lanes and root budget 43;
k=18: 42 individually-surjective lanes and root budget 42.
```

In particular, the apparent 24-component shortcut

```text
P(t)=product_(n=2)^59 (t-n)
```

kills all 58 low correction degrees and leaves the target plus degrees
60,...,82, but gives only an `E^2` congruence.  Before its 58 roots there are
78 individually-surjective correction lanes; at least 20 survive.  Thus this
projection is automatically solvable and cannot be a target dual.  A real
certificate must retain several coupled Hasse rows, i.e. use a genuine
multirow shifted approximant/Popov computation rather than another scalar
Euler polynomial.

## Exact dimensions and convention

Including `A_1` as a formal source coordinate:

```text
raw A_1,...,A_82 dimensions       441,597,347
agreement divisibility conditions 319,331,010
post-agreement dimensions          122,266,337
error conditions                   149,567,730
deficit                              27,301,393
```

For actual membership, `A_1=B` is fixed, so only `A_2,...,A_82` vary:

```text
raw correction dimensions          430,903,638
agreement divisibility conditions  308,686,643
post-agreement correction dims      122,216,995
error conditions                    149,567,730
deficit                              27,350,735
```

These are dimension counts, not an independence claim.  The transformed
module is the exact object on which target membership or a nonzero vector
dual must next be certified.

## Why the transform is exact

For `n<60`, write `A_n=G^(60-n) C_n`; for `n>=60`, set
`C_n=G^(n-60)A_n`.  In both cases the strict source inequality becomes
`deg C_n<n(G-W)`.  Substitution `Y=GV` gives

```text
K(X,GV)=G^60 F(X,V).
```

Since `gcd(G,E)=1`, multiplication by `G^60` is a unit at the error fat
scheme.  Moreover `(E,GV-1)=(E,V-A)` for any inverse lift of `G`.  Hence the
error contact condition is exactly `F in (E,V-A)^60`; no coefficient window,
CRT tail, or high-degree divisibility has been discarded.

## Reproduction

```bash
python3 .experiments/full187_f3_pure_face_graph_transform_6900.py
```

The run constructs the literal target locators, checks `GE=X^N-1`,
`gcd(G,E)=1`, the inverse formula, every dimension identity, and the complete
60-order scalar-surjectivity census.  It uses far below the 4 GiB experiment
ceiling and makes no production edits.
