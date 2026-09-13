# Full187 high-V sparse Hermite discriminator (6900)

## Scope

This is an exact finite-field **discriminator**, not a proof about the target
field.  It tests whether mixed high-`V` rows can conceal the low error layers
that defeated every single Taylor-unit product.  It preserves the exact
strict X-multiplier widths after scaling

```text
(m,g,e,w) = (60,11,5,8),  D = 660.
```

The useful ratios are retained closely:

```text
(g-w)/e = 3/5       versus 49342/81731,
w/e     = 8/5       versus 131071/81731.
```

All ranks are exact over `F_257`.  Error nodes are `0,...,4`; the degree-11
agreement locator has roots `20,...,30`, so it is a unit at every error.

For each high-V lane, the source row is

```text
p_b(X) L(X)^max(60-b,0) V^b,
dim p_b = max(0, 660 - 8b - 11 max(60-b,0)).
```

The local transfer used by the discriminator is

```text
V = 1 + E + T R.
```

Thus the coefficient in passive degree `R^r` and error degree `E^j` is
`binom(b,r) binom(b-r,j) T^r`, and it must vanish through X-Hasse depth
`60-r-3j`.  Keeping only `r=0` is the top-E test.  Adding just `r=1` is the
smallest passive-layer discriminator.

## Six schedules fixed before rank computation

1. `fifo_contiguous_low`: `b=14..34`.
2. `returns_contiguous_high`: `b=62..82`.
3. `even_stride_crossdock`: `b=14,16,...,54`.
4. `triple_stride_crossdock`: `b=14,17,...,74`.
5. `two_hub_low_high`: `b=14..23` and `b=73..82`.
6. `just_in_time_boundary`: `b=42..62`.

These represent, respectively, adjacent finite differences, post-saturation
returns, stride-two and stride-three packets, a low/high meet-in-the-middle
packet, and a packet centered where the `L` inventory reaches zero.

## Exact pivot results

At passive depth `r_max=0`:

| schedule | columns | rank | nullity | held-out payload gain |
|---|---:|---:|---:|---:|
| fifo contiguous low | 1512 | 1512 | 0 | 0 |
| returns contiguous high | 1764 | 1760 | 4 | 1 |
| even stride | 2142 | 2142 | 0 | 0 |
| triple stride | 2332 | 2332 | 0 | 0 |
| two hub | 955 | 955 | 0 | 0 |
| just-in-time boundary | 3243 | 3150 | 93 | 1 |

The top-E system therefore leaves only two apparent escape packets, both at
or beyond locator saturation.  The payload gain of one verifies that each
kernel contains a combination nonzero at a held-out point; the nullity is not
merely duplicate columns.

Adding only the first passive layer (`r_max=1`) kills both survivors:

| schedule | rows | columns | rank | nullity | payload gain |
|---|---:|---:|---:|---:|---:|
| returns contiguous high, `b=62..82` | 6200 | 1764 | 1764 | 0 | 0 |
| just-in-time boundary, `b=42..62` | 6200 | 3243 | 3243 | 0 | 0 |

The other four schedules were already injective in the `r=0` row subset, so
they remain injective after `r=1` rows are added.

## Countergate and surviving loophole

For all six precommitted high-V schedules, a mixed combination satisfying the
top-E constraints and the first passive Hermite constraints is zero in this
ratio-faithful scaled system.  This is a decisive scheduling countergate:
the high-V kernel seen in the top channel is an artifact of omitting the first
passive direction, not a robust carrier.

It does **not** prove target injectivity.  A target-sized proof still has to
show that its exact local error expansion contains this `T R` minor with a
unit coefficient, and must cover supports outside the six schedules (or prove
a structural reduction to them).  The discriminator says where to spend the
next proof effort: extract that first-passive minor rather than search more
top-E-only packets.

## Reproduction

```text
python3 -m py_compile .experiments/full187_highV_sparse_hermite_discriminator_6900.py
prlimit --as=4294967296 --cpu=900 -- python3 \
  .experiments/full187_highV_sparse_hermite_discriminator_6900.py
prlimit --as=4294967296 --cpu=900 -- python3 \
  .experiments/full187_highV_sparse_hermite_discriminator_6900.py \
  --schedule returns_contiguous_high --r-max 1
prlimit --as=4294967296 --cpu=900 -- python3 \
  .experiments/full187_highV_sparse_hermite_discriminator_6900.py \
  --schedule just_in_time_boundary --r-max 1
```

The script stays below a 4 GiB address-space cap on all recorded runs.
