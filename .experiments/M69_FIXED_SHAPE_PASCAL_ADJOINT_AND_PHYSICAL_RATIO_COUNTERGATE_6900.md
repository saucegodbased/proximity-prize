# m69 fixed-shape Pascal adjoint and physical-ratio countergate

Date: 2026-09-14 UTC. Scope: target 6900 research only. Production,
submission, score, and radius files are unchanged.

## Outcome

The hoped-for direct adapter from the literal Full187 fixed-shape source to
the recurrence in commit `255c4f4` is **false without an additional coupling
theorem**.

The prefix-dual calculation itself is correct. On the benchmark's complete
multiplicative NTT domain, a covector `mu` annihilating an RS prefix of length
`f` has a unique polynomial `H`, `deg H < 262144-f`, such that

```text
mu(i) = node(i) * H(node(i)).
```

The common factor is exactly `node(i)`; there is no channel-dependent anchor
and hence no hidden `X^2` in a valid adjacent calculation.

What failed was the identification of the physical transpose covector with
one fixed `lambda(i) * W(i)^k`. For one fixed physical shape `(r,s,q)`, the
literal Pascal source sends source contact `k` to output contact `y` with

```text
choose(k,y) * W(i)^(k-y).
```

Therefore an output-annihilator tuple `lambda_y(i)` produces

```text
mu_k(i) = sum_{y in Y, y<=k}
            choose(k,y) * W(i)^(k-y) * lambda_y(i).
```

The new Lean countergate proves this exact primal/transpose pairing and shows
that the source-annihilator condition is equivalent to prefix orthogonality
of every such `mu_k`.

## The decisive triangular obstruction

The deficient contacts for each fixed `(r,s,q)` form a consecutive interval

```text
Y = {a, a+1, ..., a+m-1}.
```

For the first `m` source contacts, write `k=a+h` and `y=a+d`. Then

```text
mu_h(i) = sum_{d=0}^h
  choose(a+h,a+d) * W(i)^(h-d) * lambda_d(i).
```

The coefficient of `lambda_h` is `choose(a+h,a+h)=1`. The Lean theorem

```text
exists_prefixPascalAdjointFrom_preimage
```

proves, by induction, that this transform is surjective for every field,
every `W`, every node set, and every finite length `m`. Thus the first square
block of `mu_h` covectors can be prescribed independently. Their extracted
short dual polynomials can likewise be independent subject to their
individual prefix-dual bounds.

Already at the first adjacent step, Lean proves the exact formula

```text
mu_(a+1) = W * mu_a + a * W * lambda_a + lambda_(a+1).
```

Consequently

```text
mu_(a+1) = W * mu_a
```

holds if and only if

```text
a * W * lambda_a + lambda_(a+1) = 0
```

pointwise. The literal source definition does not contain this equation. A
formal one-node counterexample takes `lambda_a=0`, `lambda_(a+1)=1`, giving
`mu_a=0`, `mu_(a+1)=1` for every `W`.

The file also defines the general correction

```text
PascalCorrection_k := mu_(k+1) - W * mu_k
```

and proves that its pointwise vanishing is exactly the extra premise needed
to recover an adjacent relation. If it vanishes and `E(i)W(i)=N(i)`, the
extracted polynomials satisfy

```text
N * H_k = E * H_(k+1)
```

at every NTT node. Only then do the existing no-wrap, coprime-factorization,
and corrected square-recurrence theorems apply.

## What later source contacts actually add

Triangular surjectivity applies only to the first square block
`k=a,...,a+m-1`. The actual m69 fixed-shape source also has:

```text
direct shared-tail contacts k > max(Y), through k=68;
one terminal contact K = 94-r-s.
```

Those contacts have no new output covector on the diagonal. They impose
additional prefix-orthogonality conditions on the extrapolated combinations

```text
mu_k = sum_{y in Y} choose(k,y) W^(k-y) lambda_y.
```

These are the only currently identified source constraints capable of
coupling the freely selectable first block. They do **not** definitionally
say `PascalCorrection_k=0`, and no theorem currently derives correction
vanishing from them. In particular, terminal orthogonality is another RS
prefix-membership equation for `mu_K`, not an equality `mu_(k+1)=W mu_k`.

The viable next problem is therefore a simultaneous rational Padé/dual-code
theorem using all later direct and terminal prefix constraints. Continuing to
apply the fixed-covector adjacent recurrence to the physical Pascal adjoint
would be unsound.

## Physical `W=N0/E0` boundary

The DataEleven leaf supplies a factored cross

```text
(B*E0)(node(i)) * physicalW(i) = (B*N0)(node(i)),
```

where

```text
physicalW(i) = d(node(i))*U0(i) - c(node(i))*U1(i)
```

and `E0` is nonzero at every benchmark node. Hence the normalized function

```text
W(i) := N0(node(i)) / E0(node(i))
```

is globally defined and satisfies `E0(i)W(i)=N0(i)`. The new generic Lean
theorem proves that this normalized `W` equals the physical wedge at every
node where `B(node(i)) != 0`.

At a root of `B`, the factored cross is `0=0` and says nothing about the
physical wedge. A formal scalar counterexample has `b=0`, `e=n=1`, and
`z=0`: `b*e*z=b*n`, while `e*z != n`. Therefore the actual leaf does not
currently supply the global physical identification required by a full-node
Pascal source adapter.

The existing DataEleven theorem separately proves that all four target source
constants vanish at `B`-roots. That fact is useful, but it does not make the
polynomial source operator invariant under changing `physicalW` at those
nodes. A punctured-source theorem or an explicit argument absorbing the
`B`-root coordinates is still required.

Because the legacy DataEleven dependency contains a copied `V6` valuation
block, directly importing it together with current Mathlib triggers the known
`Valuation.Integers.integralClosure` declaration collision. The physical
ratio theorem is therefore compiled as a generic lemma whose hypotheses are
exactly the factorization, root-free denominator, and cross fields already
exposed by `DataElevenHighEClosedLeaf`. Combining the modules in a production
root still requires the existing library-shim cleanup.

## Formal artifacts

`M69Full187PrefixDualSourceAdapter6900.lean`:

- exact full-NTT nodal polynomial and barycentric weight;
- prefix-dual existence and uniqueness on `IRSProfile.domain`;
- conditional fixed-covector adjacent/no-wrap/coprime/square recurrence;
- now explicitly marked conditional and nonphysical for the multi-output
  Full187 Pascal source.

`M69FixedShapePascalAdjointCountergate6900.lean`:

- literal finite fixed-shape Pascal primal map;
- exact transpose pairing identity;
- source annihilator iff every Pascal adjoint kills its assigned prefix;
- short NTT dual extraction for every source contact;
- unit-lower-triangular first-block surjectivity;
- first correction formula, explicit counterexample, and general correction;
- conditional bridge from correction-zero to the no-`X^2` adjacent relation.

`M69DataElevenPhysicalRatioBoundary6900.lean`:

- globally defined normalized ratio for root-free `E0`;
- cancellation and physical equality off the common-factor roots;
- explicit zero-common-factor counterexample.

All three files compile with one Lean worker and a 4.5-GiB allocator cap.
Every printed axiom set is contained in

```text
[propext, Classical.choice, Quot.sound].
```

There is no `sorry`, `admit`, `decide`, `native_decide`, unsafe declaration,
or generated finite table in the artifacts.

## Exact remaining edge

This work does not close `NoDataElevenHighEClosedLeaf6900` from commit
`7068012`. It closes and corrects the algebraic source-adjoint interface, but
leaves two real physical obligations:

1. prove a simultaneous theorem from all direct-tail and terminal Pascal
   prefix constraints that kills every output-annihilator tuple (or directly
   realizes the terminal targets); and
2. attach that theorem to the actual DataEleven leaf, including a sound
   treatment of the `B`-root coordinates where normalized and physical `W`
   are not identified.

Until those are proved, commit `255c4f4` remains a valid conditional
recurrence theorem but is not a theorem about the literal Full187 source.
