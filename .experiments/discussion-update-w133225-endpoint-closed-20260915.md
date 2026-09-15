6900 research update: the W=133225 hard endpoint is now closed end-to-end.

Branch: https://github.com/saucegodbased/proximity-prize/tree/codex/6900-live-research
Milestone commit: `82b9e14` (with scalar closure in `4e54147`).

What is new since the previous hard-L update:

* The exact primary source `(m,B,W,k)=(547,98685911,133225,61)` is now formal, rather than assumed.
* The exact target rank is bounded by `1483883217`; the conservative source-column lower bound is `388991586012407`; at 262143 nodes this leaves kernel dimension at least `1987858376`.
* The source theorem constructs an actual nonzero polynomial in the nested `(J,RT,T)=(740,244,122)` box with order-547 contact at every node.
* The universal specialization theorem turns that contact into vanishing on every degree-at-most-133225 polynomial with at least 180413 agreements, using the exact identity `98685911 = 547 * 180413`.
* The full scalar consumer now combines the already-closed hard-L active count with the semantic nonactive cleanup. It proves
  `Gamma.card <= 263447357007129510`, strictly below the retained hard core floor `263611557201785349`, with headroom `164200194655839`.
* `WeightedHardEndpointClosedW1332256900.hard_endpoint_coreFloor_contradiction` constructs the source internally from the received word and reaches the contradiction. There is no remaining “assume Q exists” premise at this endpoint.

Verifier-safety audit:

* every new module was compiled separately under the capped runner;
* printed axioms are only `propext`, `Classical.choice`, and `Quot.sound`;
* no `sorry`, `decide`, or `native_decide` occurs in the new source chain;
* the large finite sums are proved symbolically, so there is no hidden kernel evaluator or native axiom.

Parallel work now underway:

1. The complementary small-identity-node branch (`|Z| <= 262142`) has both product bands compiled axiom-clean. Its current margins are `9651698026837` and `351886167375037`; source/escape integration is in progress.
2. At W=133226, the extended L-terminal arithmetic is green at all 262144 nodes. A soundness correction enlarged the derivative-skinny loose box from `(744,5,5)` to `(744,7,7)` so its agreement `all` coordinate dominates the small-family threshold uniformly. Formal terminal/consumer integration is in progress.
3. An independent critic is auditing the actual protocol adapter and the remaining scalar-degree window. These endpoints are not being called a ProtocolClaim prematurely.

Honest state: this is a substantial formal milestone, but not yet a 6900 candidate. The immediate remaining work is to finish the small-Z semantic branch, finish the W=133226 semantic stack, and then close or structurally bypass the remaining scalar-degree window before assembling `ProtocolClaim 6900`.
