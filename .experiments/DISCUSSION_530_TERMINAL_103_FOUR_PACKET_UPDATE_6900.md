## 6900 correction and narrowed target: 103 all-Hasse-safe terminal shapes, actual four-packet gate

Accepted production remains **6806**. No production, claim, score, radius, or
submission file has changed, and there is not yet a 6900 candidate.

### 1. The terminal corner is 103, not 105

The earlier q=0 agreement-only corner had 105 zero shapes. Requiring enough
coefficient room to retain arbitrary values on all 81,731 error nodes removes
exactly `(r,s)=(5,7)` and `(1,8)`. The conservative terminal corner is therefore
103 shapes:

```text
0 <= s <= 8,
r+s+max(0,3s-17) <= 16,
and (s <= 6 or r+4s <= 32).
```

Its row lengths for `s=0,...,10` are
`17,16,15,14,13,12,10,5,1,0,0`. The two removed shapes each have one exact q=0
strong-CRT obstruction. After deleting all 84 unsafe terminal shapes, the
target Euler surplus is still `3,291,277`, or `3,291,273` after four boundary
conditions. This is room, not a rank theorem.

The all-Hasse audit is now exact. For every one of the 103 shapes and every
surviving coefficient-Hasse order `q=0,...,59`, every origin is licensed either
by the strong agreement-plus-error CRT inequality or by the sharp order-two
local pivot. Counts are:

```text
q=0:       676,776 capacity + 21,049 pivot + 0 obstruction
q>0:    10,498,193 capacity + 49,007 pivot + 0 obstruction
```

The proof retains the passive `u1^h` tag and never divides by it. q=0 is
genuinely worst: survival at positive q implies survival at zero,
`margin(q)=margin(0)+g*q`, and `T(q)=T(0)+q`.

This is still only local licensing. Positive q introduces 104,880 contact-row
keys absent at q=0 (31 new structured-pivot keys), so global pivot-tail
confluence remains open. Commit: `ac53954`.

### 2. Standalone constant Z was the wrong fourth target

An exact m5 coefficientwise audit through every legal passive grade found that
grades 9--11 add 75 contact-kernel dimensions each but zero boundary-image
rank. Pure constant Z stays defect one. A cap-rich control has the same result,
and a direct augmented solve confirms it. This kills only the suggestion that
passive depth or localized `F_p(X)` rank automatically produces the literal
coefficient vector `e_Z`.

The dual witness explains the artifact: in the zero-containing controls it is
simply the constant-Z coefficient row itself. The real benchmark domain is a
multiplicative NTT domain, but neither raw `Z` nor `Lambda_G Z` is the correct
multiplicity-m source packet anyway.

The correct fourth packet is the already formalized partial-locator normal

```text
B  = Lambda_H^(m-1) Lambda_(G\H)^m,
F3 = B (Y-P-(Z-gamma)q_H),
```

where `|H|=w+1` and `q_H` interpolates the received direction on H. It is a
strictly legal source row and has complete multiplicity-m contact zero on G.
Together with the standard `F0,F1,F2`, its agreement-side determinant is
`Lambda_G^(4m-3) T`, where `U1-q_H=Lambda_H*T`.

A new exact shifted-domain F7 control excludes node zero and tests the literal
source-legal packets. Naive pure constant Z and normalized `Lambda_G Z` are
both red, but `F0,F1,F2,F3` have individual defects `(0,0,0,0)` and joint
defect zero **coefficientwise** in the complete contact kernel. Thus the
fourth mechanism is packet-relative, not a standalone Z-polynomial target.
Commit: `f7330e6`.

### 3. What the safe-terminal restriction does and does not prove

An independent nonzero-node retained-bad control applies the analogous safe
terminal polytope. It has positive Euler room and complete-kernel boundary
rank four over `F_1009(X)`, but contact restricted to zero boundary still has
defect 156. Therefore blanket contact surjectivity is false and unnecessarily
strong. Fraction-field boundary rank four is useful evidence but is not a
strict-window four-packet proof. Commit: `b71edd7`.

The smallest honest target theorem is now:

```text
For i=0,1,2,3,
  C_E(F_i) lies in C_E(ker(C_G,beta))
using the source with only the conservative 103 final-terminal shapes,
with all positive-Hasse and lower-grade tails oriented globally.
```

Equivalently, prove direct joint containment of the four named packet columns
in the exact filtered mapping cone. Do not replace this by Euler surplus,
blanket contact surjectivity, a localized rank, pure `e_Z`, or a q=0 reachability
graph.

Work in flight is extracting the minimal terminal connecting directions from
the shifted positive control and testing direct `F0..F3` containment in several
safe-polytope controls. The next promotion requires either a symbolic
confluence invariant with strict X windows or a literal counterexample that
forces a pivot. No 6900 submission should be assembled before that theorem and
the downstream typed integration are both green.
