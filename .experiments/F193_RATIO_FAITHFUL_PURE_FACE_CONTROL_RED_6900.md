# F193 ratio-faithful pure-face fixed-boundary control: RED

Date: 2026-09-14 UTC. Scope: a semantic control for the running connector
gate, not a Full187 theorem or production change.

In the exact chamber

```text
(p,N,g,e,w,m,D)=(193,64,44,20,31,4,176),
w < 2e < g < e+w,
```

take the same agreement/error partition and partial-locator boundary as the
full connector experiment:

```text
B=H^3 R^4,  deg B=D-w-1=144.
```

Freeze the coefficient of `Y` to `B`, the constant coefficient to zero, and
allow every legal pure correction in `Y^2,...,Y^5`. The literal all-node
order-four contact map has

```text
correction lane widths/rank gains  114,83,52,21
total correction columns/rank      270/270
contact rows                        640
reduced B*Y residue support          62
decision                            RED.
```

Therefore a possible GREEN result for the full pure-plus-slope first shell
cannot be interpreted as pure bivariate membership. It would certify a real
connecting-map effect: translated slope columns cancel contact that no legal
fixed-boundary pure correction can cancel. This control prevents an invalid
specialization inference between the two gates.

Reproduce under the standard experiment cap:

```bash
prlimit --as=1073741824 --cpu=120 -- \
  python3 -B .experiments/f193_ratio_faithful_pure_face_control_6900.py
```

Recorded receipt:

```text
residue sha256    a4a1e04a9e89018e906f2f38f19afa73c26833c582ce3d6da79006c686e7d859
canonical sha256  77411abede17bb4e187cc01abbea5f3120d4ee8ef7018dbb665538b36ec01b09
peak RSS          35048 KiB
```
