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
dim p_b = max(0,
  min(660 - 8b, 660 - 10b) - 11 max(60-b,0)).
```

The first term is the active `Y^b` cutoff.  The second is the pure-seed
`Z^b Q^b` cutoff, with `deg Q=2e=10`.  The pure-seed cutoff is the binding
one.  It cannot cancel between distinct `b`, because its seed degree is
exactly `b`.  Omitting this endpoint gives invalid source widths and false
apparent kernels; the implementation takes the minimum explicitly.

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

Already at passive depth `r_max=0`:

| schedule | columns | rank | nullity | held-out payload gain |
|---|---:|---:|---:|---:|
| fifo contiguous low | 504 | 504 | 0 | 0 |
| returns contiguous high | 100 | 100 | 0 | 0 |
| even stride | 714 | 714 | 0 | 0 |
| triple stride | 634 | 634 | 0 | 0 |
| two hub | 185 | 185 | 0 | 0 |
| just-in-time boundary | 1059 | 1059 | 0 | 0 |

The follow-up structural schedule contains every lane of nonzero scaled
source width, `b=14..65`.  (The pure-seed cutoff gives width zero from `b=66`
onward in this scale.)  Its exact result is:

| schedule | rows | columns | rank | nullity | payload gain |
|---|---:|---:|---:|---:|---:|
| all source-legal high-V, `b=14..65` | 3150 | 1889 | 1889 | 0 | 0 |

## Countergate and surviving loophole

For all six precommitted schedules—and even their union with every other
nonzero-width pure-V lane—the top-E constraints alone are injective in this
scaled system.  There is therefore no scaled scheduling escape to be rescued
by adding passive layers.

It does **not** prove target injectivity.  A target-sized proof still has to
promote the scaled rank to the actual locator pair.  In particular, the actual
locators satisfy the special full-domain derivative identity, whereas the
five/eleven-root test pair is generic.  Also, rounding makes the target's tiny
positive `b=66` width disappear in this scale.  These are the two remaining
loopholes, not an observed mixed-row kernel.

## Corrected-width process audit

An earlier local run used only the active cutoff.  It reported spurious
nullities 4 (`b=62..82`) and 93 (`b=42..62`), both removed by `r=1`.  Those
columns are not literal source rows: their pure-seed coefficients exceed the
source cutoff.  The current tables supersede those ranks.  This caught a
general process rule for Full187 experiments: compute the minimum width over
**every seed tail before doing a rank experiment**.

## Reproduction

```text
python3 -m py_compile .experiments/full187_highV_sparse_hermite_discriminator_6900.py
prlimit --as=4294967296 --cpu=900 -- python3 \
  .experiments/full187_highV_sparse_hermite_discriminator_6900.py
prlimit --as=4294967296 --cpu=900 -- python3 \
  .experiments/full187_highV_sparse_hermite_discriminator_6900.py \
  --schedule all_source_legal_highV --r-max 0
```

The script stays below a 4 GiB address-space cap on all recorded runs.
