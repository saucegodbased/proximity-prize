# Orbit-LCM quotient versus the W133225 weighted scalar theorem

Date: 2026-09-15 UTC.  Exact same-witness/formal-interface audit.  No ECCC
paper route, O2 retuning, source grid, candidate, or submission.

## Binary result

The orbit-LCM **degree reduction is GREEN**, but direct reuse of
`WeightedCutoff2ScalarListW1332256900` on the canonical quotient is
**formally RED**.

At every original agreement node, canonical division

```text
B_gamma = Lambda*C_gamma + R_gamma
```

gives

```text
C_gamma(x_i) = (centre_i - R_gamma(x_i))/Lambda(x_i).       (1)
```

The remainder is seed-dependent.  More strongly, the new compiled theorem

```text
sharp_division_quotient_no_common_received_word
```

proves on the literal sharp `Good/E0/scalar/centre` witness that division by
**any** degree-at-most-112230 multiple `D` of that same `E0` cannot leave all
quotients `scalar_gamma / D` agreeing with one seed-independent received word
on their original agreement sets.  A full orbit LCM has degree at most

```text
6 * 18414 = 110484 < 112230,
```

so the theorem applies once the LCM/divisibility object is supplied.

This closes the audit decisively: the fixed `received : I -> K` premise of the
formal W133225 theorem is not merely unproved for the canonical quotient; its
existence is contradicted by the already formal proper-residual/common-word
argument.  Scalar injectivity also cannot simply be transported through
division.  Therefore there is no mechanical adapter from orbit quotient
degree to the existing scalar theorem.

## 1. Same-witness field repair

The previous `HighESharpProjectiveResidualPackage` kept its sharp `E0` and the
bound `deg E0 < 18415`, but dropped three orbit facts returned for that exact
witness:

```text
forall i, E0(domain i) != 0,
IsCoprime E0 (sigma E0),
IsCoprime E0 (sigma^2 E0) OR IsCoprime E0 (sigma^3 E0).
```

The enclosing leaf also contained a separate existential
`cross_no_adjacent_hard_corner`, but its hidden witnesses were not
definitionally tied to `sharpPackage.E0`.  Reopening that existential later
would silently permit witness reselection.

The sharp wrapper now stores the three facts directly as

```text
E0_root_free
E0_adjacent_coprime
E0_mixed_coprime
```

and its only constructor fills them with the original `hroot/hcopadj/hmixed`
from the same destructuring that builds `P.E0`, `P.Good`, and `P.scalar`.
The module and its existing W133226 scalar adapter rebuild under the library
shim.  Printed axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

## 2. Exact branch map

Put

```text
E_j = sigma^j(E0),
e   = deg E0,
t   = max(deg c, deg d),
q   = deg Q,
s   = t+q,
W   = 131071+e-s,
ell = deg lcm(E_0,...,E_5).
```

The subtraction is nontruncated because the same leaf has
`e+t+q <= 18705`.  Write `h2` for `gcd(E0,E_2)=1` and `h3` for
`gcd(E0,E_3)=1`.  Adjacent coprimality is always present.

The exclusive routing is:

| branch | retained facts | LCM lower bound | quotient cap at `W>=133382` |
|---|---|---:|---:|
| k2 | `not h2`, `h3` | `ell >= 2e` | `deg C <= 128760` |
| k3 | `h2`, `not h3` | `ell >= 3e` | `deg C <= 126449` |
| k6 | `h2`, `h3` | `ell = 6e` | `deg C <= 119516` |

For the degree lower bounds, adjacent gives the coprime pair `E0,E1`.
Adding shift two makes `E0,E1,E2` pairwise coprime by conjugation.  Adding
both shifts one, two, and three makes all six pairwise coprime.  The stored
disjunction excludes `not h2` and `not h3` simultaneously.

The exact arithmetic is short.  From `W>=133382`,

```text
e-s = W-131071 >= 2311.
```

Hence

```text
W-2e <= 131071-(e+s)       <= 128760,
W-3e <= 131071-(2e+s)      <= 126449,
W-6e <= 131071-(5e+s)      <= 119516.
```

All are below 133225.  They are sharp from only these inequalities at
`(e,t,q,W)=(2311,0,0,133382)` and `ell=k*e`.  The three theorems
`quotient_cap_k2/k3/k6` and the endpoint equality are kernel checked in
`OrbitLcmWeightedCutoff2ReuseGate6900.lean`.

## 3. Exact quotient and residue formulas

Normalize the orbit LCM `Lambda` to monic.  Coefficient Frobenius permutes
the six conjugates, so uniqueness of the monic LCM gives
`sigma(Lambda)=Lambda`.  The new same-witness root-free field implies
`Lambda(x_i) != 0` at every original node.  Since each scalar `B_gamma` is
Frobenius fixed, uniqueness of Euclidean division gives fixed polynomials

```text
B_gamma = Lambda*C_gamma + R_gamma,
deg R_gamma < ell,
deg C_gamma <= W-ell.
```

The sharp residual identity is

```text
E0*selected_gamma
  = a + gamma*b + Q*(c+gamma*d)*B_gamma.             (2)
```

Because `E0 | Lambda`, reduction of (2) gives the literal pole residue

```text
Q*(c+gamma*d)*R_gamma = -(a+gamma*b)  mod E0.        (3)
```

Thus `R_gamma` is not an ignorable Euclidean artifact: it is the moving
proper-pole residue.  If two residues were equal for distinct seeds, subtract
(3).  Then `E0` would divide both

```text
b + Q*d*R,
a + Q*c*R,
```

and therefore their determinant combination `a*d-b*c=N0`, contradicting
`IsCoprime E0 N0` and `e>0`.  The residue motion is genuine.

At an agreement node `B_gamma(x_i)=centre_i`, evaluation of the Euclidean
decomposition gives exactly (1).  The theorem
`quotient_eval_eq_movingCentre` formalizes this field identity.

## 4. Why neither scalar theorem premise transports

The exported scalar theorem requires, literally,

```text
received : I -> K
forall gamma in Good,
  A <= #{i | C_gamma(node_i)=received_i},
Set.InjOn (gamma |-> C_gamma) Good.
```

It constructs both primary and helper polynomial kernels from the one fixed
pair `(nodes,received)` before it ever sees `Gamma`.  Its nonactive and active
consumers use the same fixed values.  There is no unused moving-centre hook.

Equation (1) violates the first premise.  The compiled same-witness theorem
strengthens this to an outright negation of every possible common
`quotientWord` for the full sharp `Good`.

Division also does not preserve injection.  Any two distinct polynomials of
degree below `deg Lambda` have the same zero quotient.  The generic theorem
`quotient_collision_of_distinct_small_remainders` formalizes that fact.
Existing stronger target work already bounds a fixed quotient fibre by four,
but `4 * 263611056734952886` is far above the retained mass; a finite-fibre
bound is not the injection required by the scalar adapter.

A target-scale local model shows why the numerical overlap does not rescue
this inference.  At the upper endpoint choose

```text
e=18414, s=0, W=149485, ell=6e=110484,
n=262144, A=180413, 2A-n=98682.
```

Split the nodes into `Z,X,Y` of sizes `98682,81731,81731`.  Let
`R0=0`, let `R1` be the degree-98682 locator of `Z`, take `C0=C1=0`, and
set `B_i=R_i`.  Define one received word to be zero on `Z union X` and
`R1` on `Y`.  Then `B0` and `B1` are distinct fixed polynomials, each has
exactly A common-word agreements, while their orbit-LCM quotients collide.
Choosing seeds 0 and 1 and

```text
Q=c=1, d=a=0, b=-R1, selected_0=selected_1=0
```

makes (2) exact and gives `N0=R1`, coprime to any `E0` root-free on these
nodes.  This is a bounded logical countermodel to automatic injectivity, not
a benchmark counterexample or a huge-family construction.

## 5. Minimal new theorem that would actually close this bridge

There are two honest options.

### A. Corrected-quotient adapter

Construct seed-dependent polynomials `J_gamma` and prove all three facts

```text
deg(C_gamma+J_gamma) <= 133225,
(C_gamma+J_gamma)(x_i) = one fixed received_i on every agreement,
gamma |-> C_gamma+J_gamma is injective on Good.
```

Then the compiled theorem
`corrected_quotient_family_card_lt_retained` applies immediately and gives
the needed strict bound.  Orbit division by itself supplies none of these
facts.  Taking `J=0` is formally impossible by
`sharp_division_quotient_no_common_received_word`; taking the obvious
interpolant of `R_gamma/Lambda` has no known degree bound below 133225.

### B. A genuinely moving-centre weighted theorem

Prove a new orbit-pole-aware cutoff-two theorem directly for the same sharp
family:

```text
B_gamma = Lambda*C_gamma+R_gamma,
deg C_gamma <= d_k,
Q(c+gamma*d)R_gamma = -(a+gamma*b) mod E0,
B_gamma(x_i)=centre_i on agreement_gamma,
```

with the k2/k3/k6 pole graph and proper determinant retained, concluding
`Good.card < sharpRetainedBudget`.  Its source must keep either the original
fixed-centre scalar `B` and reclaim LCM pole degree, or add the seed/residue
coordinates explicitly.  It cannot call the current fixed-values kernel on
`C` unchanged.

The highest-information next experiment is therefore a source-existence
canary for this exact moving-centre/pole-aware theorem at the worst k2 cap
128760.  If that source is not positive at the endpoint, the orbit route is
not a 6900 bridge; further LCM arithmetic or quotient-fibre sharpening should
stop immediately.

## Formal receipt

Changed/added:

* `TwoSourceSharpProjectiveHighEIncidenceFrontier6900.lean` — same-witness
  root-free/adjacent/mixed orbit fields;
* `OrbitLcmWeightedCutoff2ReuseGate6900.lean` — three exact caps, moving-centre
  formula, quotient-collision lemma, literal same-witness no-common-word
  theorem, and the sufficient corrected-quotient adapter.

Both rebuilt with the task library shim under the 8 GiB cap.  Every printed
theorem uses only `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`,
`admit`, `decide`, `native_decide`, local axiom, or opaque declaration occurs.

