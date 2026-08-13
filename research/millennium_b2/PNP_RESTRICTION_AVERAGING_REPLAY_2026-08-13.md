# PNP restriction-averaging replay — 2026-08-13

**✅ LEAN-VERIFIED finite theorem · 🔴 upstream statement refuted · 🚧 P-vs-NP bridge missing**

## Verified object

The corrected file `verification/pnp-restriction-averaging/PNPRestrictionAveraging.lean` includes the necessary hypotheses `hν : ∀ r x, 0 ≤ ν r x` and `hη : 0 ≤ η`.

After repairing the Mathlib pin to `c44e0c8ee63ca166450922a373c7409c5d26b00b` and replacing the obsolete proof step `Finset.filter_sum` by `Finset.sum_filter`, GitHub Actions run `31706298406`, job `94467598357`, completed successfully at branch commit `3445e24345e8172ec6adb42d1d698e60f6a23373`.

The explicit-hole/escape-hatch scan passed. `lake env lean PNPRestrictionAveraging.lean` passed. The theorem axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`; no theorem reports `sorryAx`.

Therefore the corrected finite restriction-averaging theorem and companion finite lemmas are **✅ LEAN-VERIFIED**.

## Critic verdict

This verifies a finite averaging lemma only. It does not formalize circuits, P, NP, or a complexity lower bound, and it does not prove any Millennium statement.

## Exact remaining gap

**🚧 MISSING / 🧩 BRIDGE:** a circuit-independent local restriction hardness theorem in the needed size/depth regime, followed by a complexity-preserving transfer to a superpolynomial lower bound for an NP language.

## Provenance

- upstream flawed source: `Stevemoraco/RH-Lean` `ba99f4cbdd8842ae63817890c8538685130bc2ab`;
- corrected downstream source: `Stevemoraco/qs` `6b5f836968a60bbbbe1d2fd9a524e38cc476144f`;
- isolated-branch repairs: `26675caf59e0cb5952feccd7b35d9ec0f2fb9c21`, `9eb0b672a4a1279b31c2d8295d0c19b382c31dee`, `3445e24345e8172ec6adb42d1d698e60f6a23373`;
- successful replay: run `31706298406`, job `94467598357`.

FIVE-ALARM OFF.
