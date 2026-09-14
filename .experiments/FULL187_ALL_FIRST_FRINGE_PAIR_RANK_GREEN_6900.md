# Full187 all first-fringe adjacent pairs: exact GREEN

Date: 2026-09-14.  Scope is the lower-6900 top `u0`-free map after commit
`2d678e8`.  No production files are changed.

## Verdict

Every first unsupported scalar Hasse layer can be controlled after the already
fixed complete jets by coupling two adjacent contact-degree coefficient
polynomials.  Across all 187 streams:

```text
physical first-fringe blocks                  9,482
distinct adjacent fringe pairs                  219
same complete depth                           4,789
depth drops by one                            4,693
one-polynomial bandwidth                          1  (always insufficient)
minimum successful adjacent bandwidth             2
nominal dimension surplus             22,681..22,901
exact failed pair maps                             0
```

This is a global first-layer result, not yet a simultaneous solution of later
Hasse layers: the same finite coefficient fringes participate in many lower
contact equations.

## Uniform reduction

Let `Omega=X^N-1`, let `A` be the complete depth of `P_f`, and write adjacent
strict windows

```text
width(P_f)     = A*N  + a,
width(P_(f+1)) = A'*N + b.
```

Always `A-A'` is zero or one, and always `a+b>N`.  Variations which preserve
the fixed complete jets are `Omega^A V_f` and `Omega^A' V_(f+1)`.

If `A'=A`, their first-fringe maps are ordinary weighted evaluations of
`W_a` and `W_b`.  If `A'=A-1`, expanding at a domain root gives

```text
H_A(Omega^(A-1)V) / H_1(Omega)^A
 = H_1(V)/H_1(Omega) + (A-1) H_2(Omega)/H_1(Omega)^2 V.
```

Since `Omega=X^N-1`, the induced coefficient operator is diagonal:

```text
X^j -> N^(-1) * (j + (A-1)(N-1)/2) * X^j.
```

The executable proves every one of these diagonal weights is nonzero over the
entire relevant strict fringe.  Thus in both cases the rank is exactly that of

```text
W_a + U1*W_b -> R=F_p[X]/(X^N-1).
```

This local triangular factor is the piece a naive reverse-HRS dual omits.  For
the future multiplicity proof, dual jets must be paired in reverse Hasse order
with weights

```text
v_j^(-1) H_(s-i)(g/A_j)(alpha_j).
```

## One common family of Hankel minors

Quotient by `W_a`; the remaining row count is `m=N-a`.  In coefficient basis
the adjacent map is Toeplitz.  Reverse its columns.  Because
`W=N/2-1`, in both depth-parity cases

```text
a-b+1 = N/2 (mod N).
```

Therefore all 9,482 gates are leading Hankel minors of the same cyclic
sequence

```text
s_t = coefficient_(N/2+t mod N)(U1).
```

Only 219 sizes occur:

```text
54,086..54,195 and 185,159..185,268
```

(one integer in the displayed union is unused).  Incremental exact FLINT
Berlekamp--Massey was run on the `2m` prefix for every used size.  At every
checkpoint its complexity is exactly `m`, its remainder degree is `m-1`, and
the connection endpoints are nonzero.  By the Hankel/Berlekamp--Massey
criterion, every selected `m x m` determinant is nonzero.  Hence all 219
rectangular maps have full row rank.

The worst nominal-surplus case is also the largest minor:

```text
(r,s,f,q)                (0,0,0,41)
(a,b)                    (76,876,207,949)
m                        185,268
surplus                   22,681
complete-depth drop       41 -> 40
result                    full row rank
```

The opposite endpoint is the previously audited `(11,10,58,1)` pair with
`m=54,086`; it also passes.

## Relation to the global lacunary identity

At the graph points, the complete contact system is multiplicity-60
vanishing of

```text
F=C(X)Y^82 + sum_(f<60) P_f(X)Y^f
```

in `I^60`, where `I=(Omega,Y-U1)`.  The formal identity

```text
(Y-U)^60 * sum_(i=0)^22 binom(59+i,i) U^i Y^(22-i)
 = Y^82 + sum_(f<60) c_f U^(82-f)Y^f
```

explains the Pascal recurrence and organizes the desired global solution.
The strict X-windows prevent simply taking the displayed constant-jet lifts;
the adjacent Hankel maps are the first Popov/window-reduction steps for moving
that identity into the allowed module.

The target-specific BM connection polynomial is not yet a theorem-sized
certificate.  For both endpoint sizes its gcd with each of
`XiE,XiH,XiR,Q,qH` is constant; it matches no tested prefix/suffix (forward or
reversed) and no salient consecutive-root geometric locator.  Thus this audit
does not falsely identify the opaque Padé connection with a known locator.
The next decisive task is a global shifted approximant/Popov reduction of the
lacunary identity, or an exact simultaneous multi-`f`, multi-`q` confluence
gate retaining the corrected hyperderivative weights.

## Reproduction

```bash
cd /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work
prlimit --as=3221225472 --cpu=1200 -- \
  python3 -B .experiments/full187_all_first_fringe_pair_rank_6900.py
```

Recorded receipt:

```text
exit 0; peak RSS 230,984 KiB
checkpoint sha256 e292c39af4bcac39f23fd7b9a479ce3cfd0d18e89f2fa012fa7db8ce74e49cf9
cyclic sequence  23c8bd5a73a3bfcb8b062e0dd04c9f4b986a4f8611881f8f02bf3007e8223935
canonical        f663e83cd3354fa55f64272daf308b3518faa01661befbf1b6a64ca9235e955a
script           0e9a95b6aeb038d4812d37c914982fc4650e7690d0abefd66261ba5ebb89916d
```
