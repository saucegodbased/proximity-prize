### Lower-6900 correction: the fixed-lambda m69 recurrence is not the physical Pascal transpose

Scope first: accepted production is still 6806 and the live verified best is
6810. There is no 6900 candidate, build, comparator run, or submission. This
update retracts endpoint credit from one conditional research lane before
more work is built on it.

The exact NTT prefix-dual lemma is sound: a covector `mu` annihilating an RS
prefix of length `f` has a unique short polynomial `H` with

```text
mu(i) = node(i) H(node(i)),   deg H < 262144-f.
```

The failed step was identifying every physical source-facing covector with
one fixed `lambda(i) W(i)^k`. For a fixed Full187/m69 shape `(r,s,q)`, the
literal source coefficient from contact `k` to output contact `y` is

```text
binom(k,y) W(i)^(k-y).
```

Therefore an output-dual family `(lambda_y)` produces

```text
mu_k(i) = sum_(y in Y, y<=k)
            binom(k,y) W(i)^(k-y) lambda_y(i).
```

The `lambda_y` are independent. The first square Pascal block is unit lower
triangular, and a new Lean theorem proves it can realize arbitrary
`mu_a,...,mu_b`. Source-prefix orthogonality therefore gives one short dual
polynomial per `mu_k`, but no adjacent relation between them.

An exact target chain makes the failure concrete:

```text
(r,s,q)=(0,0,26), Y={41,42}, terminal T=94,
width_41=26*262144+258842,
width_42=26*262144+127771.
```

Both channels have the same Hasse depth/order, so there is no diagonal
normalization escape. Set

```text
lambda_41=53,
lambda_42=-42 W.
```

The terminal transpose vanishes pointwise because

```text
53*binom(94,41)=42*binom(94,42),
```

yet

```text
mu_42-W mu_41 = 2131 W != 0
```

in characteristic `2130706433` for nonzero `W`. Thus even the stronger
condition `mu_94=0` does not restore the fixed-power recurrence. The actual
terminal condition asks only for prefix orthogonality, so it cannot imply
more. The executable extends this construction to all 9,405 multirow chains
in the exact 9,900-chain census.

Consequences:

1. The earlier no-`X^2` recurrence and geometric Padé/UFD lemmas remain valid
   conditional algebra, but they do not model simultaneous physical m69
   confluence and now receive zero endpoint-completion credit.
2. The unconditional individual interpolation result for at least 3,276
   numerator zeros remains valid in its stated one-output scope. Its proposed
   1,125 improvement depended on the invalid physical recurrence adapter and
   is withdrawn as a simultaneous-source claim.
3. Reciprocal monomials in the allowed endpoint range remain promising. For
   `W=X^-2151`, all 9,900 literal shared-tail chains pass by a different
   mechanism: invariant coordinates split the map into Pascal blocks, and
   every terminal coordinate has enough distinct source contacts. The exact
   minimum slack is five over all chains. This is a scoped monomial theorem,
   not an arbitrary-rational theorem.
4. The correct hard problem is now the simultaneous rational Pascal/dual-code
   theorem using every later direct-tail constraint. A rank-sensitive target
   basis reduces the raw 140,153 deficient coordinates to the exact defect
   rank 54,498 and lowers the maximum chain length from 29 to 23, but that
   basis is not yet attached to the actual leaf.

The endpoint integration has separately been checked: a universal proof that
no `DataElevenHighEClosedLeaf` exists composes in one Lean environment to

```text
ProtocolClaim 6900 10461695 33554432
```

with only `propext`, `Classical.choice`, and `Quot.sound`. What remains is not
the final arithmetic. It is the physical producer side: derive the literal
m69 system from every leaf, solve the genuine joint four-boundary Pascal
system including common-factor roots and passive tails, and turn that source
section into a leaf contradiction.

Formal/checkable local commits are `39c05e1`, `b58b762`, and `a742238`.
Neither Lean artifact uses `sorry`, `admit`, `decide`, `native_decide`, or an
unsafe declaration. The correction scripts stay below 70 MiB RSS.
