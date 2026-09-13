# Full187 high-`V` divergent inversion audit

Date: 2026-09-13.  Scope: research only; no production edit.

## Literal normalization and the two endpoint facets

Use the faithful discriminator `Q=H^2`, with `L=Lambda_G`, `H=Xi_E`, and
`LH=Omega_N`.  At an error, `V=1+local`; at an agreement, `V=local`.
For a covariant monomial

`p L^(60-b-2c-3d) V^b J1^c J2^d`,

the active lex-head allowance for `p` is

`49342 b + 49343 c + 49344 d`,

whereas the pure-seed endpoint allows only

`16951 b + 16952 c + 16953 d`.

The gap is about 32391 per covariant degree.  For a pure `V^b` coefficient,
the corrected exposed-error charge is `H^(60-3b)`, so its residual tight-facet
margin is

`16951 b - (60-3b)81731 = 262144 b - 4903860`.

It is negative at `b=18` and positive first at `b=19` (margin 76876).  Thus
high `V` is a real escape from the old blanket-`H^60` argument.

## Six deliberately divergent mechanisms

These were generated before ranking.

1. **Cross-`b` binomial packets.**  Replace an isolated `V^b` term by a
   packet centered at the error value, morally `V^s(V-1)^r`.  Pascal
   cancellation can make many error Taylor coefficients vanish while each
   expanded coefficient lives in a different source strip.

2. **`H`-adic Newton/Hermite basis.**  Solve the error conditions in the
   weighted basis `H^(60-3j)(V-1)^j`, instead of coefficientwise in `V`.
   This is the honest algebra suggested by the contact bifiltration.  Failure
   mode: converting `1` into a homogeneous locator expression consumes an
   inverse of `L`, moving the cost to the tight endpoint.

3. **Frobenius inverse packet.**  Since `LH=Omega_N=X^N-X` and `Omega_N'` is
   constant, `A=(Omega_N')^-1 H'` satisfies `LA=1 mod H`.  Therefore
   `H^a L^(60-s-r)V^s(V-LA)^r` is a literal polynomial version of idea 1.
   Failure mode: the low-`V` coefficient contains the huge factor `A^r`.

4. **Triangular normal-coordinate syzygies.**  Use
   `J1+L'V=LW` and `J2+2L'J1+LL''V=L^2P` to cancel passive-seed leaders before
   imposing error flatness.  This can transfer burden from the tight facet to
   the wider active facet.  Failure mode: the compensating `L'`/`L''`
   coefficients themselves consume most or all of the transferred width.

5. **Checkerboard endpoint cancellation.**  Combine several inverse packets
   with shifted `(s,r)` so that the low-`V` endpoint of one cancels an interior
   coefficient of another, then alternate which endpoint is exposed.  This is
   the main loophole in every single-packet STOP.  It should be modeled as a
   sparse Popov/Hermite system, not dismissed coefficientwise.

6. **Higher-Hasse inverse jets.**  Differentiate `LH=Omega_N` repeatedly and
   build order-2/order-3 local units from `H',H'',...`; the constant/additive
   full-domain polynomial may make these inverse jets unusually structured.
   Failure mode: denominator clearing or repeated use of a degree-81730 inverse
   representative recreates the low-end source overrun.  A win would require a
   compressed representative or cancellation shared across orders.

7. **Dual inversion (attacker).**  Instead of constructing the packets, seek a
   residue-at-infinity functional that annihilates every source-legal packet
   but not the desired linear RHS.  If that functional vanishes on a proposed
   enlarged family, its kernel directly identifies the cross-`b` combination
   worth constructing.

## Post-generation ranking

The quickest decisive falsifier is idea 3.  The strongest construction lane
is idea 5, followed by idea 6.  Ideas 1 and 2 are organizing languages rather
than complete constructions; idea 4 is promising only if its derivative
coefficients are shared across many RHS rows.

## Exact STOP for the natural Frobenius inverse packet

Let `deg H=81731` and use the natural inverse representative
`A=(Omega_N')^-1 H'`, of degree 81730.  Contact order 60 requires

`a+r >= 60`.

Even granting the relaxed total-`V` cap

`s+r <= 66`, 

the low-`V` packet endpoint has multiplier `H^a A^r` and would require

`81731a + 81730r < 16951s`.

There is no nonnegative integer triple satisfying these three inequalities.
This is proved by `omega`, and the corresponding polynomial `natDegree`
statement is proved in
`Full187HighVInversePacketEndpointStop6900.lean`.  That file also proves
directly from `(LH)'=c` that `c^-1 H'` is an inverse of `L` modulo `H`.

Verdict: **STOP only for a single first-order inverse packet using the natural
`H'` representative.**  Do not promote this to a STOP for cross-packet
cancellation.  The next information-rich test is a truncated Hermite/Popov
matrix whose columns are several shifted packets and whose rows include both
source endpoints.  A surviving kernel vector is a construction; full row
rank gives the correct multi-packet STOP.
