# k=0 full-centered pure family: exact one-syndrome STOP

Date: 2026-09-14 UTC. Scope: exact-G lower 6900, profile
`(m,B,s,U,L,D)=(47,16,8,64,3757,47g)`. This changes no production or
submission file.

## Verdict

**RED:** the pure full-centered family

```text
C_k = Lambda_G^(m-k) A_G^k,       2 <= k <= 47,
A_G = Y-P-(Z-gamma)Q_G,
```

together with every legal global-X multiplier and passive-seed shift, does
not represent the literal F3 error syndrome in the complete error-contact
target. A single error with nonzero direction mismatch already obstructs
membership.

The obstruction is exact and local, not a source-dimension shortage. After
projecting complete contact to its contact-constant coordinate, every pure
carrier is divisible by the square of one affine passive-seed polynomial,
whereas the literal F3 trace is nonzero and affine. Equality in the complete
contact target would imply equality after this projection, so the scalar
failure is decisive.

The premise that `A_G` is a unit because its selected-seed value `delta_e`
is nonzero is false in the literal target ring. The passive seed is a genuine
polynomial variable, not an adically completed or truncated variable.
In `K[W]`, the units are nonzero constants; `delta_e+epsilon_e W` is a unit
exactly in the matched case `epsilon_e=0`.

This stops only the requested `k>=2` pure family. It does not stop a coupled
family containing a linear `A_G` trace, R/S companions, or other complete
source columns.

## 1. Literal local traces

Put `W=Z-gamma`. At an error node `e`, write

```text
lambda_e  = Lambda_G(e) != 0,
delta_e   = u0(e)+gamma*u1(e)-P(e) != 0,
epsilon_e = u1(e)-Q_G(e),
eta_e     = u1(e)-q_H(e),
b_e       = Lambda_H(e)^(m-1) Lambda_(G\H)(e)^m != 0.
```

The contact-constant projection of the full-centered factor is

```text
a_e(W) = delta_e + epsilon_e W.
```

Consequently a legal shifted pure carrier has trace

```text
X^j W^z C_k |_e
  = e^j W^z lambda_e^(m-k) a_e(W)^k.                  (PURE)
```

All positive-contact Taylor terms disappear under this projection. Thus
every finite linear combination of `(PURE)` with `k>=2` belongs to the
principal ideal

```text
(a_e(W)^2)  subset K[W].                              (SQ)
```

This remains true if the coefficients are allowed to be arbitrary
polynomials in `W`, which is strictly more freedom than the source gives.
Changing `j`, `z`, `k`, or the locator scalar cannot remove the common
square.

The literal partial-locator row is

```text
F3 = Lambda_H^(m-1) Lambda_(G\H)^m
       * (Y-P-(Z-gamma)q_H).
```

Its contact-constant error trace is exactly

```text
F3 |_e = b_e (delta_e + eta_e W).                     (F3)
```

The constant coefficient `b_e delta_e` is nonzero. Hence `(F3)` is a
nonzero polynomial of degree at most one.

If `epsilon_e!=0`, then `a_e` has degree one. Every nonzero element of
`(a_e^2)` has degree at least two, so `(F3)` is not in `(SQ)`. This includes
the special case `eta_e=epsilon_e`: then F3 has one copy of `a_e`, not two.

Therefore one mismatched error proves

```text
C_E(F3) notin span C_E({X^j W^z C_k : k>=2}).          (STOP)
```

Since complete-contact equality implies contact-constant equality, no
higher contact coordinate can repair `(STOP)` inside this family.

## 2. Smallest exact counterexample

Over `Q`, take one error trace with

```text
delta=1, epsilon=1, eta=0, b=1.
```

These values are compatible with the anchor relation
`eta=epsilon+H*T` by taking `H(e)=1,T(e)=-1`. Then

```text
a(W)=1+W,                 F3(W)=1.
```

Every `k>=2` family combination is `(1+W)^2 p(W)` for some polynomial
`p`. Evaluating at `W=-1` gives zero, while F3 evaluates to one. The Lean
receipt proves this for an arbitrary finite index set, arbitrary powers
`k_i>=2`, and arbitrary polynomial coefficients.

## 3. Exact m47 source windows

The family is not failing because it was accidentally source-illegal. For
the target-uniform worst case `deg Q_G=g-1`, the maximum weighted X degree
of `C_k` is

```text
(47-k)g + k(g-1) = 47g-k.
```

Thus the strict `D=47g` window permits precisely the uniform shifts

```text
0 <= j < k.                                             (XWIN)
```

For a fixed lower degree `d=max(w,deg Q_G)<g`, the exact larger window is

```text
0 <= j < k(g-d).
```

Neither window affects the common local factor `a_e^2`.

The other source caps are also green. Expanding `A_G^k` uses active degree
at most `k` and total passive-seed-plus-active degree at most `k`. Hence

```text
2 <= k <= 47 <= U=64,
0 <= z <= 3757-k,
slope=curvature=0
```

fits the literal active, seed, slope, and curvature caps. The millions of
available `(k,z)` columns therefore still live in the same proper ideal at
one mismatched node.

The two omitted exponents explain why the square is unavoidable:

* `C_0=Lambda_G^m` hits weighted degree `mg` and violates the strict source
  cutoff;
* `C_1=Lambda_G^(m-1)A_G` has only one residual factor but carries a nonzero
  first boundary jet, so it is not an automatic zero-boundary correction.

Any revival must cancel the boundary jet of a linear-residual carrier using
other source shapes without reintroducing its error syndrome. That is the
coupled recurrence problem, not a pure-power argument.

## 4. Exact scope

Stopped:

```text
literal F3 one-syndrome correction by pure C_k, k>=2          RED
repair by arbitrary legal X shifts                           RED
repair by arbitrary legal passive-seed shifts                RED
claim that delta!=0 makes A_G a unit in the target K[W]       FALSE
```

Still open:

```text
zero-boundary combinations retaining a linear A_G trace       OPEN
R/S/osculating or complete-source coupled recurrence          OPEN
rank-adaptive four-boundary theorem                            OPEN
globally matched epsilon=0 adjacent-carrier branch             OPEN
```

When `epsilon_e=0`, `a_e=delta_e` really is a scalar unit and the square
obstruction disappears at that node. This does not help the mismatch branch:
one node with `epsilon_e!=0` is enough for `(STOP)`. If every error is
matched, the proof is in the separate globally-matched branch and still
requires its own complete-contact argument.

## 5. Formal receipt

`.experiments/K0FullCenteredOneSyndromeStop6900.lean` proves:

```text
sum_ge_two_powers_eq_square_mul
affine_F3_not_square_multiple
affine_F3_not_in_ge_two_family
one_error_full_centered_family_counterexample
target_worst_full_centered_weight
target_uniform_X_shift_legal
target_uniform_X_shift_illegal_at_k
target_full_centered_shape_caps
```

It compiled under the task-local 8 GiB cap in under three seconds. Printed
axioms are only `propext`, `Classical.choice`, and `Quot.sound`. It contains
no `sorry`, `admit`, `decide`, or `native_decide`.

