# Fixed-`T,C` cross-candidate eliminants: exact pair/triple STOP

Date: 2026-09-15 UTC. Scope: lower 6900, the near-identity branch only.
No production edit and no external material was consulted.

## Verdict

**STOP for every pairwise or three-wise incidence argument which consumes
only**

```text
T B_gamma - C = H_gamma R_gamma,
deg B_gamma <= 149485,
deg R_gamma <= 51673,
deg T <= 82601,
deg C <= 231508,
deg H_gamma = 180413,
```

with fixed `T,C`, split `H_gamma`, and the same-centre agreement semantics.
The short residual is genuine, but it does not lower the common-support
degree:

* the sharp pair cap remains exactly `149485` and is attained with constant
  residuals;
* even a genuinely non-collinear triple can have `149484` common agreement
  nodes while all residual degrees are at most `30929`;
* the target pair and triple moments require caps `124302` and `85642`,
  respectively.  Thus the exact missing reductions are `25183` and `63842`
  roots, not a mechanical use of the `51673` residual bound.

At one candidate above the branch allowance,

```text
L = 875068543039974,
```

both exact balanced moment inequalities remain feasible, even if every
triple is optimistically treated as non-collinear.  Therefore neither route
can prove the required `<=875068543039973` count from this interface.

## 1. Cheapest pair eliminant

For two candidates, subtraction is exact:

```text
H_1 R_1 - H_0 R_0 = T (B_1-B_0).
```

Before cancellation, both sides have the same worst degree:

```text
deg(T)+deg(B_i) = 82601+149485 = 232086,
deg(H_i)+deg(R_i) = 180413+51673 = 232086.
```

Cancelling the known fixed factor `T` gives exactly `B_1-B_0`, still of
degree `149485`.  A Sylvester determinant or resultant is not cheaper: it is
a presentation of this same subtraction relation, and any resultant of two
polynomials with even one common agreement root is already zero.  Higher
subresultants merely encode the degree of their common locator.

The cap is tight under all the scoped hypotheses.  Choose pairwise disjoint
node sets

```text
|G|=149485, |S_0|=|S_1|=30928.
```

Their union uses only

```text
149485+2*30928=211341 <= 261852
```

near-identity nodes.  Write the same letters for their monic split locator
polynomials and set

```text
T=S_1-S_0,       C=-G S_0,
B_0=0,           B_1=G,
H_0=G S_0,       H_1=G S_1,
R_0=R_1=1.
```

Because `S_0,S_1` are monic of the same degree,
`deg T<=30927`.  Direct expansion gives

```text
T B_i-C=H_i R_i  (i=0,1).
```

Define the common centre to be zero on `G union S_0` and `G(x)` on `S_1`.
The definitions agree because the sets are disjoint and `G` vanishes on its
own roots.  The two candidates therefore have exactly `149485` common
agreements, despite residual degree zero and comfortable `T,C` degrees.

The Lean theorem `pair_tight_factorization_schema` checks the polynomial
identity without treating this construction as a full benchmark leaf.

## 2. Cheapest three-wise eliminant and a tight non-collinear control

The naive residual determinant

```text
det [1, B_i, R_i]_(i=0,1,2)
```

does vanish at a triple-common agreement node, when it is nonzero as a
polynomial, but its degree is at most

```text
149485+51673=201158,
```

which is worse than the pair cap.  The cheapest general improvement comes
instead from affine independence: two independent scalar differences of
degree at most `W` with `k` common roots descend to two independent
polynomials of degree at most `W-k`; hence `k<=W-1=149484`.  This one-root
improvement is best possible even with the new residual factorization.

Here is an exact construction over the target base field.  Inside any
`261852` identity nodes choose pairwise disjoint sets

```text
|G|=149484,
|S_0|=|S_1|=|S_2|=30929.
```

This consumes only

```text
149484+3*30929=242271
```

nodes.  The target evaluation nodes are nonzero; equivalently, choose the
sets away from zero.  Since `S_1,S_2` are coprime and `X` is a unit modulo
`S_2`, polynomial CRT supplies `T` satisfying

```text
T   = -S_0  (mod S_1),
X T = -S_0  (mod S_2).
```

Take the canonical remainder modulo `S_1 S_2`.  Then

```text
deg T < 2*30929 = 61858.
```

Define the exact quotients

```text
R_1=(S_0+T)/S_1,       deg R_1 <=30928,
R_2=(S_0+X T)/S_2,     deg R_2 <=30929.
```

Choose the sets away from zero; disjointness then also ensures these
quotients are nonzero.  Now put

```text
C=-G S_0,
B_0=0,       B_1=G,       B_2=G X,
H_i=G S_i,  R_0=1.
```

The three fixed-coset identities follow immediately:

```text
T B_0-C = G S_0,
T B_1-C = G(S_0+T)   = H_1 R_1,
T B_2-C = G(S_0+XT)  = H_2 R_2.
```

All exact caps are respected:

```text
deg B_2=149485,
deg C=180413<=231508,
deg T<=61857<82601,
max deg R_i<=30929<51673,
deg H_i=180413.
```

Define the centre as `0` on `G union S_0`, `G(x)` on `S_1`, and `xG(x)`
on `S_2`.  Thus all three scalars agree with one fixed centre on their
respective split supports.  Their triple intersection is exactly `G`, of
size `149484`.

This is not a disguised scalar pencil: the three scalar points are

```text
0, G, G X.
```

For nonzero `G`, `GX` is not a field-scalar multiple of `G`, since
cancellation would imply `X` is constant.  Lean checks both the three
factorizations and this non-collinearity in
`triple_tight_factorization_schema` and `zero_G_GX_not_collinear`.

This is a countermodel to a stronger cross-candidate lemma, not a claimed
construction of the entire target `DataEleven` leaf.  It pinpoints exactly
what the standalone fixed-`T,C` interface fails to remember.

## 3. Exact endpoint incidence test

Let `m_x` count how many candidate supports contain node `x`.  For `L`
candidates with at least `A` agreements on `n` nodes, discrete convexity
minimizes `sum choose(m_x,j)` by balancing `L*A` among the nodes.

At

```text
n=261852, A=180413, L=875068543039974,
L*A = n*602912107050818 + 34326.
```

The balanced pair lower bound and the `W` upper bound are

```text
lower = 47591994933874506071083261395510024,
upper = 57233692300440485282555645190869235,
gap   =  9641697366565979211472383795359211.
```

For triples, grant the route the unrealistically favorable assumption that
every triple is non-collinear, so every triple intersection is capped by
`W-1`.  Even then:

```text
lower =  9564596648111348394087669441241708354028170714710,
upper = 16694356231494484971121925123769440135503762450416,
gap   =  7129759583383136577034255682527731781475591735706.
```

The wrong leading signs explain the large slack:

```text
n*W       - A^2 =       6594095651 > 0,
n^2*(W-1) - A^3 = 4377354409424539 > 0.
```

At this exact `L`, a pair cap must be at most `124302`, and a uniform triple
cap at most `85642`, to reverse the respective inequalities.  A hypothetical
triple cap `51673` would indeed close decisively, but the non-collinear CRT
control above falsifies it by `97811` roots.

## 4. Re-entry condition

Do not continue with more pair determinants, three-row minors, resultants, or
subresultants of the displayed fixed-coset equation.  Reopen only if the
actual sharp leaf proves an additional same-witness condition which excludes
the CRT construction, strong enough to force either

```text
pair common support <=124302
```

or

```text
non-collinear triple common support <=85642
```

with a separately affordable exceptional-triple count.  Such a condition
must come from target incidence/provenance beyond fixed `T,C`, splitness,
same-centre agreement, and the `51673` residual degree.

## Verification

`.experiments/FixedTCrossCandidatePairTripleStop6900.lean` compiles through
the `-M3500` capped runner in about three seconds.  Printed dependencies are
only `propext`, `Classical.choice`, and `Quot.sound`; the source contains no
`sorry`, `admit`, `native_decide`, or unsafe declaration.
