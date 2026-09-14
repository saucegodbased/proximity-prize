# Target charge-13 transposed four-residue gate: implemented boundary

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production, score,
radius, and the accepted 6806 submission are unchanged.

## Verdict

**GREEN** for an executable, target-prime, target-domain implementation of
the exact 11-stream / 33-principal-row charge-13 operator, including all 47
same-row positive-Hasse collisions, tapered half-open coefficient windows,
and independently checked primal and transpose-dual exits.

**GREEN** for extracting the current fourth packet as the exact factored
partial-locator F3 and for instantiating its literal error-contact syndrome.
Pure `Z1` is rejected as a packet.

**BLOCKED** for a four-packet Full187 result. The missing object is the
coefficientwise lower-charge reduction `Rlt13`, including all nonprincipal
contact rows and pivot tails. The principal 33 rows are not a subcomplex, so
the executable deliberately labels its current primal/dual receipts as
principal-block certificates only.

Commit `bd2f679` independently proves that the isolated eleven-stream block
is raw-injective. Consequently it cannot be a kernel producer by itself; any
useful class must come from cross-origin and/or multi-grade quotient
cancellation at the final passive grade.

Artifact:

```text
.experiments/full187_target_charge13_transposed_four_residue_gate_6900.py
```

## Actual target instance

The executable constructs, rather than samples, the fixed instance

```text
(p,N,w,g,e,m,D,q,t,J,L)
  =(2130706433,262144,131071,180413,81731,60,
    10824780,21,10,82,2703).
```

It takes the first `g` powers of the target NTT root as G, the remainder as
E, and the first `w+1` G nodes as H. It then computes

```text
Xi_E,                 Q=Xi_E^2,
Xi_H,                 q_H=Q mod Xi_H,
U0=0 on G and 1 on E,
U1=Q on G and X^81730 on E,
gamma=0,              P=0.
```

The script checks all E roots of Xi_E, every nonroot on G, all H interpolation
equalities for q_H, every nonzero U1 value, and the root-count proof excluding
a degree-at-most-w all-node direction. The actual q_H has degree 131071.
Selected reproducibility hashes (little-endian field elements) are

```text
Xi_E  46233922775a346c245a21eafe648feb09a7754c3883aa6abeda8756721bacfb
Xi_H  0e84d39abe49a8b08b0310a82c955bf2a1e864bed1fc5e54dfec3ce2fe2e50b1
Xi_R  e7ce2b877e409f427dc20fdadfe99beffd5ae98a2b976b977e570d55d3564dd2
Q     e88b97214614eb4cd8cf88d4beeb2527ca677cd37a367600c9f490c3d199a51c
q_H   5a68a0661d42b264844faaa43f012517e7f56fa506a6a5aca327baff97608a3d
U1    11861bb608f45e2b1ff11843e5a984ba228be8f5b7aaed943cb60622408e334c
```

## Exact physical principal operator

There are eleven physical inputs, not 33 independently chosen inputs:

```text
c_s(X) Y^61 R^(21-s) S^s Z^2621,
0 <= s <= 10,  deg c_s < 76979+s.
```

Their total dimension is 846824. Exact provenance shows that the three
families in the advertised principal rows are

```text
A_s/kappa_A = c_s - 2 Hasse_1(c_(s+1)),
B_s/kappa_B = c_s - 6 Hasse_1(c_(s+1))
                  + 12 Hasse_2(c_(s+2)) - 8 Hasse_3(c_(s+3)),
C_s/kappa_C = c_s - Hasse_1(c_(s+1)),
```

with missing upper streams zero and

```text
(kappa_A,kappa_B,kappa_C)=(603758703,693269975,642373467),
kappa_C=54*kappa_A,       4*kappa_B=kappa_C  (mod p).
```

The executable uses literal Hasse derivatives
`Hasse_j(sum c_a X^a)=sum binom(a,j)c_a X^(a-j)`. In particular it does not
implement B as a composition power of `1-2 Hasse_1`; that would be wrong
because `Hasse_1 o Hasse_1=2 Hasse_2`. The taper identity

```text
width(s+j)-j = width(s)
```

is asserted at every occurrence. All three polynomial bands are replayed as
upper-unitriangular invertible maps. After target-node evaluation, the A,
B, C families are multiplied by `kappa_A U1^54`, `kappa_B U1^53`, and
`kappa_C U1^53`, respectively.

The exact symbolic provenance receipt is
`.experiments/full187_charge13_transpose_interface_spec_6900.py`; its
integration-time canonical hash is
`28bc1b68d416740d0d8532b2f651e5fe44edaaf6d8a58f343f58a6475a2748ca`.
It independently counts 33 q=0 heads plus 47 colliding positive-Hasse
origins in the principal rows.

The all-charge collision audit
`.experiments/full187_terminal_hasse_collision_blocks_6900.py` enumerates all
72,850 structured q=0 origins at target parameters and checks every tapered
positive-Hasse family. Its integration-time canonical hash is
`f7e2e7022ec6c2aabc569a254714feefe7b9bcc937d0c91aa0e48ad1625cda76`.

## Executable transpose exits

A is used as a fixed upper-unitriangular pivot. The solver unscales A,
performs the inverse target NTT, enforces all eleven strict windows, and
back-substitutes

```text
c_10=dA_10,
c_s=dA_s+2 Hasse_1(c_(s+1)).
```

It then literally recomputes all B and C rows. There are three exact exits:

1. If A has a coefficient at frequency `k >= width(s)`, it emits the Fourier
   functional

   ```text
   lambda_j=N^-1 omega^(-jk) (kappa_A U1(omega^j)^54)^-1.
   ```

   This annihilates every legal coupled source column and pairs to that
   illegal coefficient.
2. If B disagrees with the A-derived source, it emits
   `e_B^T(proj_B-M_B M_A^-1 proj_A)`.
3. C has the analogous transposed Schur functional. If neither defect occurs,
   the script returns all eleven legal coefficient vectors and replays all 33
   outputs.

The actual-p, actual-N self-check recovers a stream-3 polynomial of degree
three after its order-1/2/3 collisions; all three triangular inverses agree.
It then emits a B-Schur dual at the first error node with pairing one and a
strict-window Fourier dual at frequency 76979 with pairing one. This is a
test of the operator/certificate path, not a packet result.

## Exact F3 status

Commit `f7330e6` corrected the fourth target: it is not pure Z. Here it is
instantiated as

```text
B  = Xi_H^59 Xi_(G\H)^60,       deg B=10693708,
F3 = B*(Y-P-(Z-gamma)q_H) = B*(Y-Z q_H).
```

The boundary is already exactly extractable in factored polynomial form:
its Y coefficient is B, its Z coefficient is `-B*q_H`, and its scalar
coefficient is zero. The complete error-node contact is also exact:

```text
trunc_<60 C(B(x+T)) *
  (C(contactY+1)
   + C(U1(x)-q_H(x)-(q_H(x+T)-q_H(x))) * Zseed).
```

At selected seed gamma=0 its scalar is B(x). The executable evaluates this
at all 81731 errors, proves every value nonzero, and records hash

```text
44284a2ae31b90315699b3f0a14947ea2007114bbd7460485287f2543d5de332.
```

Thus the raw exact F3 boundary and error syndrome are available. What is not
available is `Rlt13(F3)`: its coefficientwise normal form after all prior
agreement/contact eliminators.

## Exact blocker

The raw charge-13 census has 48,516,523 provenance occurrences and
10,011,293 distinct all-grade row shapes per node. Only 80 occurrences land
in the 33 principal rows. Every source coefficient also has nonprincipal
outputs, and an admitted dual must satisfy their transpose equations as well
as every prior-source equation.

The repository supplies no linear map which performs that reduction with
all of the following simultaneously:

```text
physical origin and passive-grade provenance;
strict tapered coefficient windows;
agreement-Hermite and error-value CRT choices;
positive-Hasse and sharp-pivot remainders;
literal F0,F1,F2,F3 contact and boundary keys;
a replayable correction witness for every discarded row.
```

This is not a request for the dense 187-channel matrix. It is precisely a
missing symbolic polynomial-module representation and reducer. Commit
`ad56851` (`full187_order2_pivot_remainder_closure_6900.py`) already shows
that head-only sharp-pivot closure is false, with 70,543 live successor rows
outside the pivot set. Commits `a64361e` and `7fe2418` prove useful scalar
mixed-CRT capacity, but do not construct this source-coupled map.

The final-grade constraint is sharp: `bd2f679`
(`SOURCE_CONTACT_SHELL_HILBERT_AND_CHARGE13_AUDIT_6900.md`) records prefix
margin -117,797,284 at passive depth 2620 and +9,757,693 at depth 2621.
Thus cross-grade cancellation is not optional bookkeeping; it is the first
place a complete kernel is dimension-forced.

The executable exposes the required API as four generic 33-vector reduced
columns named exactly `F0,F1,F2,F3`. Supplying pure Z1 is explicitly rejected.
Once the missing reducer supplies those four columns *and* certifies all
nonprincipal tails, the existing solver emits either four checked principal
lifts or a named transposed separator. Until then, neither exit is a Full187
certificate.

## Reproduction

```text
prlimit --as=4294967296 --cpu=1200 -- \
  python3 -B \
  .experiments/full187_target_charge13_transposed_four_residue_gate_6900.py \
  --self-check-target-operator
```

Final pre-commit replay: exit 0, 30.00 seconds, 253.37 MiB peak RSS. The
target-instance-only run exits 0 in 7.05 seconds at 149.41 MiB. No small
prime, ambient 187-channel matrix, production file, or submission artifact is
used.

```text
script SHA256 ebd359bd06642255c8fa34a56a5b9b295a2689bc5aea1b85b63cb49cd323b654
```

Decision:

```text
GO    implement Rlt13 as a provenance-preserving symbolic polynomial reducer;
GO    use the exact factored F3/error syndrome already emitted here;
STOP  pure Z1, 33 independent sources, or principal-only promotion;
STOP  any ambient 187-channel dense target matrix or small-prime extrapolation.
```
