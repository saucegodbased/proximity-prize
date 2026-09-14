# m47 high-Y adjacent-seed PC transpose: exact STOP

Date: 2026-09-14 UTC. Scope: lower 6900 only. This is a formal identity and
structural obstruction following the exact target-ratio retest in `d251e34`.
It changes no production file, candidate, or submission.

## Verdict

The two-band F11 repair does not produce a scalable recurrence. The actual
literal PC transpose equation for `Y^48 Z^z` is now formal, including the
agreement/error split and the strict contact truncation. Adjacent external
seed bands are merely consecutive Krylov tests for multiplication by the
outer passive-seed variable:

```text
V_z(i)   = trunc_47(local_i(X^a Y^48 Z^z)),
V_(z+1)(i) = Z * V_z(i),

sum_(i in G) eta_i(V_z(i)) + sum_(i in E) eta_i(V_z(i)) = 0.
```

Here the displayed `Z` is `Polynomial.X` in the outer seed polynomial. A
contact dual is only K-linear, not K[Z]-linear, so the first equation does
not imply the second.

Expanding the raw band gives the exact coupled PC equation

```text
0 = sum_(i in G) sum_(f=0)^48 sum_(h=0)^(48-f)
      eta_i(trunc_47(passiveColumnTerm(i,a,48,0,0,z,f,h)))
  + sum_(i in E) sum_(f=0)^48 sum_(h=0)^(48-f)
      eta_i(trunc_47(passiveColumnTerm(i,a,48,0,0,z,f,h))).
```

`passiveColumnTerm` retains the literal node-dependent coefficient

```text
u0_i^(48-f-h) u1_i^h binom(48,f) binom(48-f,h)
```

and lands at seed degree `z+h`. Thus this is not an independent-shape
coefficient model and no agreement or error term has been silently dropped.

After the per-shape Hasse/CRT bridge and earlier-PC elimination, the quotient
pairing gives only

```text
W_X(Y^48)=47*180413-131071*48 = 2,188,003,
cost(Y^48)=6,291,408,

((q_z U_z) mod A)=0  or  deg((q_z U_z) mod A)<6,291,408
```

for each `z=0,1,2` separately. There is no cross-seed relation among
`q_0,q_1,q_2` in this conclusion.

The failure to close at three bands is exact over every field. For any
nonzero seed polynomial `V`, coefficient extraction at degree
`deg(V)+3` defines a linear functional `ell` with

```text
ell(V)=ell(ZV)=ell(Z^2 V)=0,
ell(Z^3 V)=leadingCoeff(V) != 0.
```

All four source seed exponents `0,1,2,3` fit the target cap beside active
degree 48. Hence adjoining `Z^2` does not create an order-three seed
recurrence; it supplies one more independent moment and leaves the next one
uncontrolled. A recurrence would require a separately proved polynomial
relation for the particular packet-compatible dual. The honest passive seed
ring itself has none.

## Exact finite reconciliation

The frozen target-ratio retest in commit `d251e34` independently confirms
the structural STOP. In both deterministic m5/m6 controls, the all-anchor
packet has boundary gain one, not three, and adjoining the full legal
high-Y consecutive-seed family changes contact and augmented ranks equally:

```text
m5 packet contact/aug/gain = 713/714/1
z=0,0..1,0..2 increments  = 10/10, 20/20, 30/30

m6 packet contact/aug/gain = 979/980/1
z=0,0..1,0..2 increments  = 12/12, 24/24, 36/36.
```

Every tested high-Y family is boundary-zero and injective. The m4
`Y^5` pair killed a chamber-specific residual line; its target analogue is
not a relative killer and should not be scaled.

## Formal artifact

`.experiments/K0HighYAdjacentSeedStop6900.lean` proves:

```text
passiveGlobalSourceMonomial_seed_succ
localSeedSubstitution_seed_succ
seedContactTruncation_X_mul
splitContactBandMoment_eq_pc_expansion
splitContactBandMoment_seed_succ
y48_three_adjacent_band_pc_transpose
y48_three_band_filtered_quotient_iff
exists_seed_dual_annihilating_three_shifts_not_fourth
y48_four_seed_shifts_fit_target_cap
```

It compiles under the task-local sub-8-GiB wrapper in about five seconds.
Printed axioms are only `propext`, `Classical.choice`, and `Quot.sound`; no
`decide`, `native_decide`, rank oracle, or generated table is used.

```text
Lean source SHA256 bad77f2ea5caa76252d6f127b209e93d6f7f5d03f350f3519b8be709c594f921
Lean object SHA256 7b3ae7caa322cac332c32b267dfc7ffb4010fdfacf6833326022934639f85743
```

## Process decision

Freeze the high-Y two/three-band transport. The next structurally different
edge is the zero-active-cost family `X^a Z^z`: it has the full `47g` X
window, so its per-seed quotient numerator is forced to zero rather than
merely into a 6.3-million-degree cokernel. The open question is whether the
literal compatible-dual equation identifies any boundary-relevant contact
component with that zero-cost numerator. That question should be answered
before adding more positive-cost seed bands.
