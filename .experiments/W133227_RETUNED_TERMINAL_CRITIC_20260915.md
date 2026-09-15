# Adversarial audit: retuned W=133227 full-node terminal

Scope: exact `N=262144`, `W=133227` arithmetic and its compatibility with
the existing W=133226 extended-L proof interfaces.  This is not an audit of a
ProtocolClaim and does not assert a route through the full interval ending at
`W=149485`.

## Reproduction

The independent replay gives:

* Johnson common-node cap `v=68774`, with positive strict-gate margin
  `10,334,991,219`;
* primary `(k,m,B,M,D,T)=(62,555,100129215,751,248,124)`, target rank
  `1,576,573,974`, columns lower bound `413,290,236,187,774`, and kernel lower
  bound `828,347,518`;
* helper `(650,5850,1055416050,7922,2600,1300)`, target rank
  `18,955,743,249,621`, columns lower bound
  `4,976,670,503,834,689,697`, and kernel lower bound
  `7,536,145,406,042,273`.

For both sources, the analytic fast rank equals the direct slow rank and the
pair-polynomial evaluator equals the direct pair sum.

The helper's **relaxed** band values, which are the conservative values the
Lean consumer needs, are:

| lower profile `(J,D)` | relaxed band | kernel minus band |
|---|---:|---:|
| `(212,11)` | `7,497,455,027,235,928` | `38,690,378,806,345` |
| `(64,55)` | `7,530,237,671,841,768` | `5,907,734,200,505` |
| `(211,54)` | `5,397,945,737,749,352` | `2,138,199,668,292,921` |

The immediately weaker profiles `(212,10)` and `(63,55)` are red.  The exact
column-difference bands are smaller than the relaxed bands, so no direction
reversal is being hidden here.

The active-plus-cleanup totals replay exactly:

| terminal | total |
|---|---:|
| `J<=210, D<=54` | `257,594,909,348,270,371` |
| `J<=211, D<=53` | `247,802,459,078,295,781` |
| `D<=10` | `217,921,169,336,120,626` |
| `J<=63` | `71,035,248,046,890,473` |

Thus the worst total is below the exact identity-core floor
`263,611,557,201,523,206` by `6,016,647,853,252,835`.

## Semantic checks

The terminal complement is exhaustive.  Negating the four terminal clauses

```text
J<=210 and D<=54;  J<=211 and D<=53;  D<=10;  J<=63
```

implies one of `(J>=212,D>=11)`, `(J>=64,D>=55)`, or
`(J>=211,D>=54)`, exactly the three band profiles above.

The derivative-skinny box `(M,S,T)=(751,21,21)` is loose but valid.  From
`D<=10`, the existing nested-weight lemma gives actual `T<=5` and `S<=10`;
both are at most 21, while the ambient primary source gives `J<=751`.  The
loosened value 21 is used to make reduced-agreement absorption large enough;
it is not an inferred equality.  The jet-skinny box `(64,63,63)` is valid from
`J<=63`.  All curve/surface absorption gates and all characteristic
projection gates are positive/strict as required.

The source shapes satisfy the currently visible generic hypotheses:
`B=m*180413`, helper stage delta `180413-(133227-2)=47188`, helper stage max
`1300=D/2`, `1301*2>D`, and all source/contact and flag parameters are below
the field characteristic.

## What remains unverified

1. There is no W=133227 Lean producer/consumer chain yet.  Exact target-rank,
   column, band, source, aggregation, cleanup, and endpoint modules still have
   to be instantiated and compiled axiom-clean.
2. The arithmetic is for exact `N=262144`.  Any claim that it handles every
   smaller identity-node set needs an explicit monotone/generalized semantic
   theorem; the current W=133226 endpoint interface requires cardinality
   equality.
3. This local retuning is not a high-window breakthrough.  The present
   two-arm search remains green only through approximately `W=133232`; at
   `W=133233` it needs a richer terminal staircase or another source.  Even a
   staircase repair near 133233 does not address disappearance of the current
   order-two source kernel much higher in the interval.
4. It is not yet joined to the actual sharp-leaf allowance argument or a
   `ProtocolClaim6900`.

## Process verdict

Confidence that the stated W=133227 arithmetic can be formalized using the
existing interfaces: about **90%**.  Confidence that this particular fixed
retuning scales to the whole open allowance interval: below **10%**.

For the complete 6900 objective, a defensible status is roughly **30% complete
and 70% uncertain**.  We are closing a local endpoint, not yet closing the
global proof.  The next information-maximizing action is a horizon test of a
general terminal-staircase/source family at several widely separated W values
(especially the upper endpoint) before spending time formalizing many
successive one-degree receipts.  Kill that route immediately if it lacks a
positive source or a terminal ledger at the upper endpoint; then prioritize a
genuinely new structural/high-order source rather than another local retune.
