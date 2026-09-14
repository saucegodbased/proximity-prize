# k0 passive-cap consumer headroom

Date: 2026-09-14 UTC. Scope: lower-6900 exact arithmetic only. No production
module, score, candidate, or submission is changed.

## Verdict

`L=3757` is the first source-positive passive cap for the current
`(m,B,s,U)=(47,16,8,64)` profile, but it is **not** a hard consumer ceiling.
Under the already published exact-stratum 52-chart ledger, the largest
strictly affordable cap is

```text
L = 7595,
```

which leaves 3,838 additional passive layers beyond 3757. Each added layer
costs `33,423,863,316,480` in the all-strata consumer. At the endpoint the
consumer remains strictly below the MCA allowance by `24,092,300,144,664`.

This materially changes the proof search. A theorem that is false at the
knife-edge first-positive cap may be repairable by buying one or more passive
layers. It does **not** mean that a larger cap automatically has boundary
rank four: dimension margin alone is insufficient, and every caller/source
side condition must be rechecked before production is retargeted.

## Exact source margins

The literal accepted source-count and blockwise local-rank formulas give:

| curvature cap | passive cap | source margin |
|---:|---:|---:|
| 8 | 3756 | -20,717,799 |
| 8 | 3757 | 2,371,080 |
| 8 | 3758 | 25,459,959 |
| 8 | 7595 | 88,617,488,682 |
| 7 | 3788 | 479,478 |
| 7 | 7595 | 86,148,077,430 |
| 6 | 5107 | 12,113,822 |
| 6 | 7595 | 40,160,156,246 |

Thus both the current full-curvature profile and the already-audited
reduced-curvature profile can buy substantial passive depth while retaining
positive source margin and this consumer inequality.

## Exact scope and next gate

The computation uses

```text
chart(L) = 588*64^4 + 1560*64^3*L,
strata   = 262144-180413+1 = 81732.
```

The strict endpoint is obtained by integer division against
`254684620614660120`; `L=7595` passes and `L=7596` fails this ledger.

Before selecting a new cap, the following must be checked:

1. every other exact-strata caller/projection inequality, not just the chart
   total;
2. the full raw contact/rank theorem at the new literal parameters;
3. whether small exact arbitrary-direction defects disappear after a bounded
   number of extra passive layers; and
4. whether that repair admits a uniform relative connecting-map proof.

The executable receipt is
`.experiments/k0_passive_cap_consumer_headroom_6900.py`. It performs only
integer arithmetic, imports the literal accepted formulas, and uses
negligible memory.
