# Full187 F3 bare-`(V-1)^60` factor countergate

Date: 2026-09-14 UTC. Scope: lower-6900 research only. No production,
claim, score, or accepted-6806 file was edited.

## Verdict

The tempting polynomial

```text
K3 = B * V * (V-1)^60,
V  = Y-Z*q_H,
B  = Xi_H^59 Xi_(G\H)^60,
```

is **not** a complete-contact kernel element in the literal problem. The
reason precedes every weighted-degree/taper question: outer `Z` is passive,
not a contact variable.

At an error node, after setting the genuine contact coordinates
`T=E=R=S=0`, the received graph gives

```text
V = 1 + Z*(U1-q_H).
```

Therefore

```text
B*V*(V-1)^60
  = B*(U1-q_H)^60 Z^60 + B*(U1-q_H)^61 Z^61
```

in contact order zero. On the frozen target's first error node, the exact
values modulo `2130706433` are

```text
U1-q_H             = 1994091055
B                   = 1307960934
coefficient of Z^60 = 1121158590
```

All are nonzero. One coordinate is enough to refute membership in the
complete contact kernel.

## Consequence

A factorized F3 route must use the full error-graph factor

```text
V - (1 + Z*(U1-q_H))
```

or supply another exact identity cancelling all its passive-`Z` terms. The
bare `(V-1)^60` construction is frozen and must not be used as evidence that
only coefficient taper remains.

The executable receipt is
`full187_f3_bare_vminus1_factor_countergate_6900.py`.
