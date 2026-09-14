### Lower 6900: universal projective high-tail cut, and complete direct A57 STOP

Status first: the live verified best remains **68.10** and this checkout's
accepted production root remains **68.06**. There is no 69.00 candidate,
build, comparator run, or submission. The results below materially sharpen
the exact remaining theorem, but do not yet close it.

#### 1. Correction: the compiled scalar cutoff is 133120, not 132103

Commit `1a2a9cb` rewires the universal endpoint to the already compiled
unconditional `WeightedScalarList133119` theorem. Therefore any surviving
large bad family has canonical received-direction degree

```text
deg(U1 interpolant) >= 133120.
```

The earlier 132103 boundary was stale. The new endpoint adapter compiles in
seconds with axioms only `[propext, Classical.choice, Quot.sound]`.

#### 2. New projective breakthrough: every received-row direction is high

Commits `c23c7c2` and `80d7549` prove an exact projective strengthening. For
any nonzero constants `(a,b)`, let `V` be the canonical interpolant of

```text
a*U0 + b*U1.
```

If `deg V <= 133119`, change affine seed chart. For `a != 0`, away from the
one pole `a*gamma-b=0`, use

```text
T_gamma = (a*gamma-b)^(-1) * (a*P_gamma - V).
```

These polynomials have degree at most 133119, agree with the fixed word U1,
and are injective above code degree. At code degree, the two interpolants
would reconstruct both received rows on each regular agreement set and
contradict the retained bad-row witness. The existing weighted scalar list
bounds regular seeds by

```text
242068243281965801.
```

One projective pole is genuinely possible, so the exact method cap is

```text
242068243281965802 < 254684620614660120.
```

The exported unconditional dichotomy is

```text
bad family below MCA
  OR
every nonzero a*U0+b*U1 has canonical degree >=133120.
```

This is fully formal, generic over the original arbitrary received rows and
agreement sets, and axiom-clean. It strengthens the previous separate
two-high-row condition to linear independence of the two coefficient tails
at degrees >=133120.

#### 3. Complete direct Full187 A57 route remains structurally RED

The projective result was immediately tested against the exact first Full187
window obstruction instead of being assumed to solve it.

Commit `8848d88` enumerates every one of the 24 direct `u0`-free physical
predecessors visible to the A57 dual. The legal hostile direction

```text
U1 = X^133120
```

gives exact image prefix `[0,255162]`, rank 255163, and suffix defect 6981.
All 3,420,276 normalized Hasse weights are nonzero, and Lean separately
kernel-checks that coefficient 255163 is always missed.

Commit `d2f08c1` then grants the stronger projective premise and every mixed
positive-`U0` direct channel independently. With

```text
U0 = X^133121, U1 = X^133120,
```

every nonzero constant combination has degree at least 133120. Even granting
all 300 independently adjustable mixed windows

```text
U0^k * U1^(t-k) * V_(t,k), 0<=k<=t<24,
```

the full direct envelope misses coefficient 255186 and has defect at least
6958. The theorem compiles axiom-clean with no `sorry`, `decide`, or
`native_decide`.

Therefore neither the frozen-target A57 Hankel GREEN nor the new projective
cut can be promoted into a universal direct-surjectivity theorem. Re-entry
requires an indirect source, an actual-RHS confinement theorem, or a
whole-family count for deficient multiplication maps.

#### 4. Other route decisions

Commit `3febb93` finished the ratio-faithful F193 survivor analysis. At the
next `J+2` dual projection, the `S` family is the unique inclusion-minimal
family spanning all four survivor coordinates, but this is only a necessary
projection, not quotient containment. The numerical F193 route is stopped;
it is not being scaled or promoted.

A tempting pure-face shortcut was also rejected before commit: reducing one
remainder modulo `E^60` cannot discard the 60 coupled low-row quotient
variables by replacing the congruence with one modulo `E`. No result depends
on that invalid simplification.

#### 5. New scalar frontier under audit

An exact low-memory replay of the existing weighted architecture finds

```text
W=133221: total 250960796897673279  (GREEN)
W=133222: total 258391532555862528  (RED)
```

at the current retained/MCA thresholds. This would raise the projective cut
to 133222 if the 33-module W133224 formal stack is safely retargeted. That
formal retarget is not yet claimed. It also does not by itself close A57: the
corresponding hostile mixed monomial pair still leaves a direct-envelope
defect of 4612.

Current high-value work is therefore: (1) preserve the projective invariant
on the exact same DataEleven low-`E0` witness, (2) test whether it yields a
new source-owned consequence rather than another disconnected rank lower
bound, and (3) formalize the W133221 scalar frontier only if the retarget
remains mechanical and verifier-safe.
