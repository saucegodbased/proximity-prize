# K0 affine seed translation and exact zero-seed transport

Date: 2026-09-14 UTC. Scope: lower-6900 k0 relative last-face route.
Verdict: **GREEN for eliminating seed zero as a separate obstruction;
STOP for uniform target relative separation.**

## Algebra

For an arbitrary boundary seed `gamma`, choose

```text
c = gamma - 1,        W = Z - c,        u0' = u0 + c*u1.
```

Then

```text
u0' + u1*W = u0 + u1*Z,        W|_(Z=gamma) = 1.
```

Thus this is a coordinate change of the same affine anchor, not a change to
the received family or its boundary point. The inverse replaces `c` by
`-c`. Expanding a source monomial gives

```text
W^z = (Z-c)^z = sum_{j=0}^z binom(z,j) (-c)^(z-j) Z^j.
```

The k0 source width and its active/derivative caps do not depend on the
passive exponent `z`, while its total cap is downward-closed in `z`.
Consequently every term in this expansion is source-legal whenever the
original monomial is legal. Translation consumes no X degree, active degree,
or derivative reserve.

It is also triangular with leading coefficient one. Modulo the preceding
passive cap, translation fixes the newly attached top-face coordinate: all
terms with `j<z` land in the old packet. Therefore the relative last-face
domain and its connecting boundary map are carried isomorphically between
seed coordinates.

`.experiments/K0AffineSeedTranslation6900.lean` formalizes the affine-anchor
identity, canonical normalization to seed one, passive-total downward
closure, the polynomial translation automorphism, and its evaluation law.
It compiles axiom-cleanly; printed axioms are only `propext`,
`Classical.choice`, and `Quot.sound`.

## Exact seed-42 to seed-zero transport

The exact F101 m8 control from commit `c1db74f` has boundary seed 42. The
canonical first raw-1 relative killer has relation-support hash

```text
e72e75718f1c0926a6da43e6d5306e5eeec845aa18fffd13c483418e2fd241ee
```

and repaired boundary normal `(71,5,97,79)`. To express precisely the same
relation at boundary seed zero, the audit uses

```text
W = Z + 42,        u0_zero = u0_42 + 42*u1.
```

It reconstructs the relation from the exact contact RREF before translating
it. The result is:

```text
contact rows / prefix columns / rank / nullity
  15390 / 11505 / 11187 / 318

original relation support                  10193
translated relation support                10173
all translated monomials in L11 source      true
inverse translation recovers original       true
translated literal contact support             0
translated candidate specialization zero    true
translated boundary normal              (71,5,97,79)
translated conormal                    (97,88,63,1)
conormal pairing                                  84
```

The 20-term support reduction is ordinary coefficient cancellation; no term
was discarded. The translated relation hash is

```text
afd643b84dfd4a451a4829b68d2c5d70917c5e20f8c8a1121ed13208bcf712eb
```

and the full receipt is:

```text
canonical
  7e56cc2489e908ab104b8f7abf0ef7f66b1d5a905615a296c2f0de8ace1b246c
script SHA-256
  2f58a1f3c3b1fb8c9183245135682b98e3f8812c3ab234c31cc6807a32522cef
runtime 411.303 s; peak RSS 2,433,496 KiB
```

This exact transport confirms that the contact implementation, source
support, boundary evaluator, and conormal pairing are covariant under the
affine seed change. In particular, the vanishing direct boundary gradient of
high positive powers at seed zero is a coordinate artifact: after
translation, the lower seed powers generated inside the old packet carry the
same relative boundary class.

## Target implication and remaining STOP

The literal target last-face analogue remains

```text
X^2 Y^48 Z^3709,        48 + 3709 = 3757.
```

At a zero boundary seed its direct gradient vanishes, but one may normalize
the boundary seed to one. Expanding the translated `Z^3709` uses only lower
seed powers and hence stays inside the target source; all non-leading terms
are absorbed by cap 3756. No characteristic-dependent division is used.

This removes the previous `gamma=0` caveat. It does **not** construct the
target relative repair. The exact remaining hypothesis is unchanged except
that it may be proved at normalized seed one:

```text
For every packet-compatible target conormal, a cap-3757 raw last-face vector
has old-correctable contact and a nonzero relative boundary pairing.
```

Equivalently, the canonical relative connecting boundary map must separate
the packet-compatible conormal space. The finite transported relation proves
this for one F101 receipt only; it is not a uniform 6900 result.

## Reproduction

```text
/usr/bin/prlimit --as=4200000000 \
  python3 .experiments/k0_seed_translation_transport_6900.py
lake env lean -j1 -M2500 .experiments/K0AffineSeedTranslation6900.lean
```

