# m69 reciprocal all-defect interval gate: GREEN, scoped

Date: 2026-09-14 UTC

## Outcome

The robust full-source profile

```text
(M, slope, curvature, J, L) = (69,24,10,94,2369)
```

does not merely improve the first Full187 window defect.  In the reciprocal
monomial model, every literal Pascal defect throughout the full descending
construction is covered by at most the cubic higher-contact predecessor.

The exact census is:

```text
defective homogeneous strata                  13,093
total literal rank defect                     54,498
rank-insensitive deficient physical shapes     6,930
rank-insensitive deficient coefficients      140,153
```

The physical sets are deliberate supersets: for each defective stratum the
gate retains every absent raw associated direction, even when another choice
of a saturated target minor could avoid it.

## First descending defect

The unique first defect is

```text
(A,n,H,d,Jraw,Jlegal,defect) = (63,44,24,1,{14},{},1).
```

Its omitted physical coefficient is

```text
(y,r,s,q) = (39,14,10,15)
width      = 4,191,058 = 15*262,144 + 258,898
quotient   = 3,246.
```

This is far smaller than the old m60 A57 quotient `54,108`.

## Exact reciprocal-monomial coverage

For `R=X^(-e)` in `F[X]/(X^262144-1)`, the `t`th predecessor shifts its
coefficient prefix cyclically by `-t*e`.  Across every deficient shape, the
initial fringe belongs to exactly 189 values in the five ranges

```text
127729,
127731..127821,
127823,
258802..258896,
258898.
```

For the old endpoint `e=2049` and the improved endpoint `e=2151`, exactly
3,546 shapes cover by power two and 3,384 require power three.  There are no
failures.

The gate also sweeps every integer

```text
2049 <= e <= 18414,
```

which contains the complete hard-corner reciprocal-monomial range.  Of the
16,366 exponents, 15,073 cover every shape by power two and 1,293 require
power three.  Again there are no failures.

The mechanism has a short arithmetic proof.  Since
`W=131071=262144/2-1`, fringes alternate between a low interval near `127.8k`
and a high interval near `258.8k`.

- If the initial fringe is high, the unshifted interval and the power-two
  suffix overlap because `262144-2e <= 258802`.
- If it is low, the power-one wrapped prefix and power-three suffix overlap
  by the same inequality after subtracting `e`.

`M69ReciprocalCyclicIntervalCover6900.lean` proves these two overlap/coverage
lemmas with no nonstandard axioms.

## Exact receipts

```text
defects      f9efb41d3fbdd9ca367289cb5cf0467cb849dcc36951efade8bab14be741c4e0
shapes       e789d4d983053ed615c9c706c87a004f6c96f2c66cc51d6625507cafb0dedeeb
coefficients 3897a7fa22779bbba328c4a75abeab46c4e193cc05b70e99b60623283aa94f35
```

## Scope and remaining blockers

This is not yet the missing 6900 theorem.

1. A general root-free rational function `N0/E0` acts by a dense cyclic
   operator, not a monomial shift.  Dimension counts do not prove the four
   prefix images are jointly onto; this needs a dual divisibility/wrap theorem
   or a counterexample.
2. The windows for different missing physical coefficients share underlying
   source freedom.  Local surjectivity must be upgraded to simultaneous
   triangular confluence.
3. In the actual leaf, `E=B*E0` and `N=B*N0`.  Cancellation is currently
   proved only off the content roots of `B`; an all-node adapter must absorb
   or avoid those exceptional nodes.

The result therefore promotes m69 to the leading direct architecture, while
keeping the arbitrary-rational rank and actual-leaf adapter as explicit hard
blockers.

## Reproduction

```bash
cd /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work
prlimit --as=2147483648 --cpu=300 -- \
  python3 -B .experiments/m69_reciprocal_all_defect_interval_gate_6900.py

prlimit --as=2147483648 --cpu=300 -- \
  lake env lean .experiments/M69ReciprocalCyclicIntervalCover6900.lean
```

Recorded Python run: exit 0, peak RSS 40,440 KiB.
