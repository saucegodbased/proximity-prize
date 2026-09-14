# Full187 q26 ninth-finite-difference bypass

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production,
submission, score, radius, and the accepted proof are unchanged.

## Verdict

The first failure of the direct low-Y Hermite slide is **not an intrinsic
q=26 obstruction**. It is only an obstruction to asking the single `y=8`
coefficient window for a complete 27th all-node jet.

There is an exact uniform bypass using nine other legal source layers per
physical charge-13 stream. It trades one unit of coefficient-Hasse order for
one unit of Y-contact order and one unit of source R exponent. The scalar
identity is the ninth finite difference of a degree-at-most-eight polynomial;
it is structural, integral, and does not depend on a fitted numerical minor.

```text
GREEN  every one of the 495 original f=8,q=26 provenance terms cancels;
GREEN  every correction uses only a complete depth-26 Hermite section;
GREEN  minimum strict correction width exceeds 26N by 207,989;
GREEN  all T/E/R/S/Z rows and target-field scalar signs match exactly;
STOP   all other contact and boundary tails remain in the quotient map;
STOP   this is not yet containment of the four packet columns.
```

Executable:

```text
.experiments/full187_q26_ninth_difference_bypass_6900.py
```

## 1. The obstruction being bypassed

The eleven physical charge-13 streams are

```text
C_s(X) Y^61 R^(21-s) S^s Z^2621,                  0 <= s <= 10,
deg C_s < 76979+s.
```

Their top contact with `(f,q,h)=(8,26,53)` contributes, for every
`aE+cS<=8`, to

```text
(T,E,R,S,Z)
  = (34-aE+cS,
     aE,
     29-s-aE-cS,
     s+cS,
     2674).
```

The direct `y=8,z=2674` correction would have to prescribe its order-26 jet.
Commit `249b160` proves that this is impossible uniformly: its window is
strictly below `27N`, and already `C=1` forces a nonzero coefficient at
degree `27N-1`.

The construction below never prescribes that jet.

## 2. Trade Hasse order for contact order

For `1 <= k <= 9`, introduce the legal source

```text
P_(k,s)(X) Y^(8+k) R^(21-s-k) S^s Z^2674.          (SOURCE-k)
```

Its invariants are

```text
active degree       (8+k)+(21-s-k)+s = 29 < J=82,
total degree         29+2674 = 2703 = L,
minimum R exponent   21-10-9 = 2,
X-window             7023742+s-k,
minimum X-window     7023733 = 26N+207989.
```

Thus the all-node Hermite CRT in

```text
A_26 = F_p[X]/(X^N-1)^26
```

has a canonical representative of degree `<26N` inside every strict source
window. Prescribe its first 26 node jets by

```text
H_(26-k)(P_(k,s))(x)
  = binom(61,8) (-1)^k binom(9,k)
      U1(x)^53 H_26(C_s)(x),                       (JET-k)

H_j(P_(k,s))(x) = 0
  for 0 <= j < 26 and j != 26-k.                  (ZERO-k)
```

Only orders 17 through 25 are used. No division by `U1`, and no unsupported
order-26 correction jet, occurs.

Take all `8+k` Y factors in `(SOURCE-k)` as contact factors, with `h=0`, and
take coefficient-Hasse order `26-k`. The output is literally

```text
T = (26-k)+(8+k)-aE+cS = 34-aE+cS,
E = aE,
R = (21-s-k)+(8+k)-aE-cS = 29-s-aE-cS,
S = s+cS,
Z = 2674.
```

This is the complete five-coordinate row of the original term, not a
projection of it. Its contact truncation is also identical:

```text
(26-k)+(8+k)+2aE+cS = 34+2aE+cS < 60.
```

## 3. Why all 45 local contact choices cancel

After factoring the common node value

```text
U1(x)^53 H_26(C_s)(x) (-1/2)^cS,
```

the original scalar is

```text
binom(61,8) * multinomial(8; aE,cS,8-aE-cS).
```

The `k`th correction scalar is

```text
binom(61,8) (-1)^k binom(9,k)
  * multinomial(8+k; aE,cS,8+k-aE-cS).
```

For fixed `(aE,cS)`, the function

```text
f |-> multinomial(f; aE,cS,f-aE-cS)
     = f falling (aE+cS) / (aE! cS!)
```

is a polynomial in `f` of degree `aE+cS<=8`. Its ninth forward difference is
zero over the integers. Consequently

```text
sum_(k=0)^9 (-1)^k binom(9,k)
  multinomial(8+k; aE,cS,8+k-aE-cS) = 0.          (FD9)
```

This proves the cancellation in every characteristic in which the displayed
contact formula makes sense; the executable separately checks every scalar
modulo the actual prime `p=2130706433`, including `(-1/2)^cS`.

The nine finite-field jet coefficients, for auditability, are

```text
k=1..9:
1195733744, 1609184323, 1927120401,
 305379048, 1825327385,  203586032,
 521522110,  934972689, 1316585101.
```

There are `11*45=495` independent original provenance occurrences. Each has
nine correction occurrences, and every one of the 495 grouped scalar sums is
zero. The exact row audit also finds 495 distinct target rows.

## 4. Complete tail classification

The construction does not pretend that the 99 new physical source
polynomials produce only the selected rows.

### Jets below 26

Every jet below 26 other than `26-k` is literally zero by `(ZERO-k)`. This
suppresses `6,850,547` otherwise syntactically legal contact occurrences.

At the one prescribed jet of each source, the full-Y, same-Z contributions
sum as another ninth difference. They vanish through the whole original
filtration

```text
aE+cS <= 8.
```

Any same-Z residual starts strictly at the next contact degree
`aE+cS=9`. The executable counts 1,111 such independent
`(s,aE,cS)` residuals, versus the 495 canceled degree-at-most-eight groups.
Thus the bypass is triangular in contact degree; it does not leak back into
the block it eliminates.

For every contact with `f'<8+k` there are exactly two cases:

1. `h=8+k-f'`: the `U0` exponent is zero and the passive coordinate is
   `Z=2674+(8+k-f')>2674`. These are strict later-passive tails.
2. `h<8+k-f'`: the `U0` exponent is positive. Since the frozen target has
   `U0=0` on agreement nodes, these are error-node-only tails belonging to
   the error-value side of the mixed CRT prefix.

At the prescribed jets, the exact provenance census is

```text
desired degree<=8 correction occurrences       4,455
same-Z degree>=9 occurrences                    5,665
larger-Z full-node occurrences                 49,390
error-node-only occurrences                   214,797
```

### Jets 26 and above

The canonical degree-`<26N` representatives have determined, generally
nonzero higher jets. They are retained. The conservative syntactic census is

```text
same-Z higher-Hasse occurrences                 78,639
larger-Z full-node occurrences                 706,211
error-node-only occurrences                  3,810,114
```

Every same-Z higher-jet term has strictly larger shifted contact weight
`T+3E` than its selected `q=26-k` head. Every `f'<8+k` term remains in the
same strict larger-Z/error-only dichotomy above. This is exactly the data a
subsequent block reducer must replay; it is not silently quotiented away.

Finally, every boundary column of every `P_(k,s)` remains part of the source
map. The present receipt makes no statement about its beta image.

## 5. Packet and assembly scope

The fourth packet is still the literal partial-locator packet

```text
F3 = B*(Y-P-(Z-gamma)*q_H),
```

never pure `Z1`. The finite-difference bypass is an exact source/contact
operation and is independent of which RHS is later reduced, but proving
packet containment still requires composing it with the complete mixed
sharp/CRT reducer and carrying all classified contact and boundary tails.

What changed is precise:

```text
before: f=8,q=26 was the first hard STOP of the direct Hermite slide;
after:  f=8,q=26 has an exact uniform filtered quotient step;
next:   orient its degree>=9, later-passive, error-only, higher-q, and beta
        tails together with the existing mixed reducer.
```

## 6. Reproduction

```bash
prlimit --as=1073741824 --cpu=120 -- \
  python3 -B \
  .experiments/full187_q26_ninth_difference_bypass_6900.py
```

Recorded run:

```text
exit 0; elapsed 3.6 s; peak RSS 26,616 KiB
canonical sha256 5a381f6ec4be969a858d812405a0eafd075eed50cbb3bf2cc2d845e7f23e6d06
script sha256    ca8699a105398096bf8d0413abbc90e9bc1fbcd52d5558dfc2e34964d8396b2a
```

Decision:

```text
GREEN_UNIFORM_F8_Q26_NINTH_DIFFERENCE_BYPASS
```
