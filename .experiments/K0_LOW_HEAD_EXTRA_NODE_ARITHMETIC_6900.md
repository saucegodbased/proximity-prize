# K0 low-head extra-node capacity

## Result

The target k0 source has overwhelming capacity for an `(n+1)`-point
low-epsilon-head argument.  Keep the source cutoff at the original `47*g`,
but retain only contact coefficients of epsilon order `<m-3`, i.e. local
order 44.  The exact closed local rank is

```text
rankBound(44,3757,16,8,64) = 213,740,910.
```

Against the unchanged target source of `65,061,789,117,960` columns this gives

```text
low-head all-node margin              9,030,892,006,920
after one extra low local node block  9,030,678,266,010
after one extra full local block      9,030,643,815,900
after four scalar boundary rows        9,030,892,006,916
```

The low-head margin contains 42,251 complete low local blocks plus residue
124,818,510.  Capacity is therefore not the bottleneck for adding one
off-domain point.

## Exact comparison

The full order-47 local rank is 248,191,020, so omitting the last three
epsilon orders removes 34,450,110 dimensions per node.  Consequently

```text
2,371,080 + 262,144 * 34,450,110 = 9,030,892,006,920.
```

The same invariant is strongly positive in the scaled profiles whose exact
full-kernel boundary image became rank four at their first positive cap:

| profile | full margin | low-head margin | after extra low block |
|---|---:|---:|---:|
| B2 structured `(n,w,g)=(12,5,8)` | 1 | 4,129 | 4,022 |
| B2 faithful `(16,7,11)` | 14 | 5,518 | 5,411 |
| B4 minimal faithful arithmetic `(10,5,7)` | 186 | 45,816 | 40,644 |

All three use `m=3B-1`, `2s=B`, and `U=4B`.  The two faithful rows also lie
in `2e<g<e+w`.  The B4 row is arithmetic only; the forbidden 97,536-column
dense endpoint matrix was not run.

## What remains unproved

This margin is **necessary capacity, not surjectivity**.  The missing theorem
must identify the literal low-head contact map with a Hermite/CRT evaluation
map (or prove the required rank directly), then show that evaluation at one
new point is onto modulo the original `n` node contacts.  Dimension alone
does not establish that independence.  A second bridge must explain how the
three omitted epsilon layers recover the four formal boundary coordinates.

This distinction matters: the complete passive-face connecting map can be
nonstrict even when the later full contact kernel has boundary rank four.

## Formal and executable receipts

- `.experiments/K0LowHeadExtraNodeArithmetic6900.lean` proves the exact
  order-44 closed rank and all target margin equalities.  The rank computation
  uses kernel-checked `decide`; arithmetic uses `norm_num`.  There is no
  `native_decide`.  A standalone `lake env lean -j1` build passes and reports
  only `propext`, `Classical.choice`, and `Quot.sound`.
- `.experiments/k0_low_head_extra_node_arithmetic_6900.py` independently
  checks target and scaled arithmetic.

Python receipt:

- Canonical output SHA-256:
  `64899223f24afd26f54cedc519c3d5c5378e4863db45e5816ed5369153c19e1f`
- Script SHA-256:
  `f8cc5a22db5d91868644f7d50c07560d922b3f784accd8f3eb654cc99fe23a76`
- Runtime: `0.022s`
- Peak RSS: `39,548 KiB`
- Address-space cap: `4,200,000,000` bytes
