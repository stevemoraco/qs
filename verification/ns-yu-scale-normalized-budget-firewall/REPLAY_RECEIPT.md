# NS Yu scale-normalized budget firewall — replay receipt

Date: 2026-08-14

- source: `verification/ns-yu-scale-normalized-budget-firewall/NSYuScaleNormalizedBudgetFirewall.lean`
- verified source head: `94f50d884112535bcc5d8daa2deb4ec4bfc53c78`
- Git blob: `c0ea80cc32846093e885f9315ff3f16c3cdd0a58`
- SHA-256: `3b91ff3d6736c8a95683b96c985a37c4de62be2ab94ddf35c34afd794c441aab`
- workflow run/job: `31846753265 / 94914687702`
- AXLE environment: Lean 4.30
- AXLE request: `47dc100d-b7e5-4550-b3bd-8453bb71a6d8`
- cached response: false
- result: success, zero Lean/tool errors or warnings, zero failed declarations
- all eight axiom reports: `{propext, Classical.choice, Quot.sound}`
- evidence artifact: `9236158302`
- artifact ZIP digest: `sha256:82856591aad89e8c836e786e66074643af03574315b74666c8d5e2a7515147dd`

Failed-first chronology:

1. `31846461424 / 94913819466`: ordered-semifield geometric-sum lemma required `CanonicallyOrderedAdd R`, unavailable for the reals; request `a06fb477-bf63-4af8-88f5-10a631db24dd`; artifact `9236061367`, digest `sha256:1d098d8c191ff53c86286567d7984ffe52a86af566f22ab74281cba9b0172a03`.
2. `31846583276 / 94914179164`: the field identity was correct, but `div_le_div_iff₀` was supplied one positive-denominator argument instead of two; request `9d3cb287-a8f3-4154-a588-4343268f97ef`; artifact `9236101444`, digest `sha256:8a0827353a00c996eaa815ec816d4b637b85751cb62c574a37aedb46d61eb539`.
3. The corrected source passed cleanly on the third replay above.

Finite real arithmetic and interval packing only. No Navier--Stokes or PDE theorem.
