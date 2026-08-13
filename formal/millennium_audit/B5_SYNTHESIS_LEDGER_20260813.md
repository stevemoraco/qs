# B5 synthesis ledger — 2026-08-13

## Cross-lane theorem

🟢 PROVED · ✅ LEAN-VERIFIED · 🧩 BRIDGE

For `q : ℕ → ℝ`, cutoff `N`, `delta>0`, `M>0`, `eps<M/2`, prefix `delta ≤ q n` for every `n<N`, and uniform tail `|q n-M|≤eps` for every `n≥N`, the explicit constant `c=min delta (M/2)` satisfies `c>0` and `c≤q n` for every `n`.

**Derivation.** Split at `N`. Prefix indices use `c≤delta≤q n`. Tail indices use `|q n-M|≤eps<M/2`, hence `M/2<q n`, and `c≤M/2`.

**Assumptions.** One finite-prefix lower bound; one tail estimate uniformly quantified over all later indices; `delta>0`; `M>0`; strict `eps<M/2`.

**Critic verdict.** 🧱 Strictness is sharp: the verified witness `M=2, eps=1, q=1` satisfies `eps≤M/2` and the error bound but not the strict conclusion `M/2<q`. The theorem constructs none of its problem-specific hypotheses.

**Lean status.** ✅ LEAN-VERIFIED under Lean v4.30.0 / Mathlib v4.30.0, PR-merge replay run `31684794329`, head `488c182efc654b8d5590cf11bc2982a3d1756842`. `#print axioms` reports `[propext, Classical.choice, Quot.sound]` for the bridge and sharpness theorems.

**Provenance.** `fbb67d40ec1dd9d2bfe85b770ab8f32cabf35b73`, `76727617dbd25caba3d8cc7b3c1a41da98e3df7b`, `488c182efc654b8d5590cf11bc2982a3d1756842`; prior B5 verifier `49a26ba638fb7d3f29a72153ce7d614d0e7e09d7`.

## Six hostile-surviving lanes

### RH
🟡 CONDITIONAL · 🧱 OBSTRUCTION · 🚧 MISSING. Finite deficit/Bregman and prime-prefix bookkeeping survive, but they do not supply the analytic critical-integral/residual identity or a uniform infinite tail. The new bridge closes only the final finite-prefix/tail patch once a positive reference margin and uniform tail estimate are proved. **Exact gap:** prove or refute the analytic residual identity with the correct function space and uniform tail. **Provenance:** `5467e600feadd2032502c86ab2f9e5a039eb51ec`.

### P versus NP
🟢 PROVED finite selector counting · 🧱 OBSTRUCTION · 🚧 MISSING. `selector_cover_capacity` survives, while the hostile external audit shows unrestricted input transport can encode the answer bit and weak existential size bounds can be vacuous. **Assumptions needed:** a genuine polynomial-time/circuit interface and an asymptotic capacity bound that does not presuppose the target. **Critic verdict:** the current external audit build defect is not a mathematical disproof. **Exact gap:** reproducible pinned replay plus a legitimate computational-model lower bound. **Provenance:** `3b40618c20e4f7cb9c9c0f59d66de90ef7ffece7`.

### BSD
✅ LEAN-VERIFIED finite information frontier · 🧱 OBSTRUCTION · 🚧 MISSING. Residue observations and density/counting certify target labels only after selector correctness (`ResidueObservations.determine`) is proved; coarse observations alone are underdetermined. **Exact gap:** derive selector correctness from actual arithmetic, then connect it to the full analytic-rank/Mordell–Weil-rank and leading-term statement. **Provenance:** `4a202f7c8fad2f30a4c33fef8f9c844dd1348b82`.

### Hodge
✅ LEAN-VERIFIED finite firewalls · 🔴 REFUTED components · 🟡 CONDITIONAL salvage · 🚧 MISSING. The audited E7/Spencer bookkeeping contains finite incompatibilities; the surviving cyclic/stable-closure lemma is only conditional on a genuine algebraic-cycle generator/decomposition theorem. **Exact gap:** formalize actual Hodge/Chow realization and prove such a generator theorem. **Provenance:** `df70ad9ad616cbbaf5e69cbbfe2c361a0ed9cc9e`.

### Navier–Stokes
🟢 PROVED finite scaling arithmetic · 🧱 OBSTRUCTION · 🚧 MISSING. Concentration certificates show why profile-dependent scales and weaker energy proxies do not yield endpoint compactness. **Assumption needed:** one coercivity/compactness modulus uniform over the admissible solution class. The new bridge applies only after such a positive all-scale margin is obtained. **Exact gap:** prove the uniform endpoint estimate sufficient for global smoothness, or construct a valid blowup. **Provenance:** `e832133f25f4432ffba007f99359989d1bb16734`.

### Yang–Mills
🟢 PROVED scalar/indexed gap arithmetic · ✅ LEAN-VERIFIED generic bridge · 🟡 CONDITIONAL · 🚧 MISSING. The half-gap logic now works uniformly over a regulator tail and patches finitely many exceptional regulators. **Assumptions needed:** a constructed 4D quantum Yang–Mills theory, positive continuum reference mass `M`, and a uniform regulator error `<M/2`. **Exact gap:** prove those constructive-QFT and regulator-to-continuum statements. **Provenance:** current B5 branch plus prior verifier `49a26ba638fb7d3f29a72153ce7d614d0e7e09d7`.

## Duplicate collapse and verdict

Finite-prefix algebra, pointwise scaling examples, residue density without selector correctness, failed E7/Spencer bookkeeping, and scalar half-gap arithmetic are banked. Further work should target the six missing interfaces above rather than reproduce these shadows.

🚧 MISSING: no exact official Millennium theorem or disproof is closed end-to-end. No FIVE-ALARM.
