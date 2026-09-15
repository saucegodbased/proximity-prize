### 6900 update: corrected terminal gate is GREEN; target bottleneck narrowed to one structured CRT map

Branch: [`saucegodbased:codex/6900-live-research`](https://github.com/saucegodbased/proximity-prize/tree/codex/6900-live-research)

Accepted/verified floor remains **6810**. There is no 6900 candidate or submission yet.

#### Plain-language summary

The earlier goal, “make every relation on the new passive face lift,” was too
strong and is false. The useful question is only whether the full source can
supply the *one boundary direction* missing from an old rank-three stage.
That endpoint is now GREEN in multiple exact controls, including faithful
target-ratio and source-positive chambers. The remaining target theorem is a
global weighted interpolation/CRT statement, not more parameter tuning.

#### What is newly exact

1. **Corrected last-three detector.** Commit `86beda4` replays the literal
   contact

   ```text
   Y = u0 + u1 Z + eps R - eps^2 S + eps^3 T
   ```

   with compressed weight `eps=q+3E` and the accepted boundary convention
   `S=Hasse_2(P)=P''/2`. In the primary m8 chamber, the old boundary image has
   rank 3; one legal passive successor raises it to 4; and the terminal
   coefficients `eps^5,eps^6,eps^7`, modulo pure contact duals, detect exactly
   that missing one-dimensional syndrome. Three nonvacuous adversarial/scaled
   controls pass too. Peak RSS was about 3.1 GiB under a 4.2 GB hard cap.

2. **Direct prescribed-syndrome endpoint.** Commit `e95712a` checks six varied
   finite receipts plus an independent larger chamber. Every one has old/full
   boundary rank `3 -> 4`, even though only a small fraction of the associated
   face kernel lifts. This confirms that full face strictness is unnecessary.
   The attractive six-cell witness in one control is
   `M(X) Z^(L+1-g) (QZ-Y)^g`, but its exponent `g` is far above target active
   cap 64, so that formula itself is explicitly **not** a target proof.

3. **Faithful first-positive endpoints.** Commit `2c6cf3b` uses
   `Q=Xi_E^2`, a genuine off-agreement mismatch, and all target-ratio
   inequalities. Boundary rank becomes 4 exactly at the first cap with
   positive global source margin, despite the preceding face having maximal
   obstruction. A second independent structured receipt behaves the same.

4. **Production local face cap.** Commit `643f53a` formally proves the exact
   passive homogeneity and injectivity of the production weighted-kernel face.
   It certifies the local numbers `91,368 - 24,948 = 66,420` and the target
   associated surplus `23,088,879`, with only standard axioms. This remains a
   local/associated certificate; it does not silently assert global lifting.

#### Projection correction and new target

The corrected terminal indices are `eps^44,eps^45,eps^46`, so their
complementary head is **low** order `eps^0,...,eps^43`. Older lemmas about
the opposite projection `eps>=3` cannot be used here. This mismatch is now
prominently documented rather than papered over.

Commit `a766ee3` formally computes the correct low-head capacity:

```text
target source                         65,061,789,117,960
one-node low-head rank cap (m=44)            213,740,910
source - n*cap                         9,030,892,006,920
after one extra full low-head block    9,030,678,266,010
```

Commit `f14a44f` gives the axiom-clean bridge: if the old low-head constraints
and one valid extra probe are jointly surjective, and that probe reads out the
four boundary coordinates, then the boundary map on the old head kernel is
surjective; the quotient-aware terminal detector then kills every compatible
boundary covector.

The promising local readout is currently being checked/formalized. For

```text
Phi(F)=F(x+eps,u0+u1 Z+eps R-eps^2 S+eps^3 T,R,S,Z),
```

the `eps^3*T` coefficient recovers `F_Y`; the `eps^0` derivatives in `R,S,Z`
recover `F_R,F_S,F_Z+u1 F_Y`, so subtraction recovers all four boundary
partials. This explains why retaining `eps^3` makes an ordinary low-head
probe sufficient. I am not counting this as proved until the exact local
factorization and global joint map are checked.

#### Honest remaining uncertainty

The one load-bearing theorem is now:

```text
actual capped raw source
  -> (all n old low-head contact blocks, one extra valid probe)
```

must have the required joint surjectivity (or the weaker exact relative
surjectivity onto the four probe rows). The 9.03-trillion margin shows that
capacity is not the issue, but dimension alone never proves surjectivity.
The proof must respect the weighted X taper and the `(B,s,U,L)` caps. Work is
now split between formalizing the local readout, testing the joint map in
exact controls, and mining the accepted nodal/HRS/CRT machinery for the
target-uniform global argument.
