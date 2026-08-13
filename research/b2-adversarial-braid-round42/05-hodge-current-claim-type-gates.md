# Hodge conjecture — two current direct proof claims fail independent coefficient and Tate-twist type gates

Date: 2026-08-13 UTC

Status legend: 🟢 PROVED, 🔵 LEAN-SOURCE, ✅ LEAN-VERIFIED, 🟡 CONDITIONAL, 🟠 SUSPECT, 🔴 REFUTED, 🧱 OBSTRUCTION, 📚 SOURCE-VERIFIED, 🧩 BRIDGE, 🚧 MISSING.

**Status:** 📚 SOURCE-VERIFIED against the latest publicly displayed Shimizu version and Bouali arXiv record; 🟢 PROVED two independent categorical type contradictions; 🔴 REFUTED AS WRITTEN the displayed load-bearing corridors in both current direct Hodge claims; 🧱 neither manuscript supplies a valid universal algebraic lowering correspondence or a correctly typed logarithmic-Picard bridge; 🔵 LEAN-SOURCE finite logical cores staged separately; ✅ LEAN-VERIFIED pending replay. **NOT A PROOF OR DISPROOF OF THE HODGE CONJECTURE. FIVE-ALARM OFF.**

## 1. Shimizu: transpose does not reverse the Tate twist

The latest Preprints.org record for Yoshinori Shimizu, *Proof of the Hodge Conjecture*, is still version 1, posted 17 September 2025. It claims the Rational Hodge Conjecture and Standard Conjectures B,C,D,I.

Let `X` be a smooth projective complex `n`-fold. A correspondence

`Z in CH^(n+r)(X x X)`

acts on cohomology with degree `+2r`. In Chow-motive notation it carries a Tate twist of sign `+r`.

Transposition exchanges the two geometric factors:

`Z^t in CH^(n+r)(X x X)`.

It preserves codimension and therefore preserves the correspondence degree/Tate twist `+r`. It does **not** turn the morphism into one of degree `-r`.

The proposed Standard-Conjecture-B operator is a scalar multiple of the transpose of the `r`-fold Lefschetz correspondence. The original and its transpose both lie in

`CH^(n+r)(X x X)`

and both shift cohomology upward by `2r`.

But the inverse Hard Lefschetz map

`(L^r)^(-1): H^(2n-k)(X) -> H^k(X)`,

with `r=n-k>0`, has degree `-2r` and would require a cycle in

`CH^(n-r)(X x X)`.

The codimensions differ by `2r`. A scalar factorial normalization changes coefficients only and cannot change the Tate twist.

### Smallest instance

For a surface (`n=2`) and `r=1`, the inverse `H^3->H^1` requires codimension `1`; the transposed Lefschetz correspondence has codimension `3` and shifts `H^3` toward `H^5`, not `H^1`.

Thus the displayed inverse-Lefschetz construction is ill-typed before its action is computed.

## 2. Bouali: rational logarithmic cohomology cannot equal integral Picard

Johann Bouali's arXiv record *Hodge conjecture for projective hypersurface* claims the Hodge conjecture for smooth projective hypersurfaces through analytic logarithmic de Rham classes.

The banked source audit records the displayed definition

`Omega^1_(X,log,0)=O_X^* tensor Q`

and the later identification

`H^1(X,Omega^1_(X,log,0))=Pic(X)`.

The left-hand side is naturally a `Q`-vector space. Its underlying additive group is divisible: every class has a half.

Take

`X=P^1_C`.

Then

`Pic(P^1_C)=Z`,

and the generator `O(1)` has no half. Equivalently there is no integer `m` with `2m=1`.

Hence no additive-group isomorphism can identify the displayed left side with the integral Picard group. At best a corrected statement could involve `Pic(X) tensor Q`, after proving all required exactness and support functoriality. That correction changes the object used in the surface-support step.

## 3. Independence of the two failures

The Shimizu obstruction is a graded/Tate-twist error in algebraic correspondences. It persists over rational coefficients and does not involve Picard torsion.

The Bouali obstruction is a coefficient-category error. It already appears on `P^1` and does not depend on Standard Conjecture B.

Repairing one manuscript gives no bridge for the other.

## 4. Claim + counterexamples + salvage

### Claims killed as written

1. Transposing the positive Lefschetz correspondence and multiplying by a scalar yields its negative-degree inverse.
2. Cohomology of the rationalized logarithmic coefficient object is the integral Picard group.

### Counterexamples

1. `n=2,r=1`: codimension `3` cannot induce the required codimension-`1` lowering action.
2. `X=P^1_C`: a divisible `Q`-vector-space group cannot be isomorphic to `Pic(P^1)=Z`.

### Best salvage

- Shimizu: construct an actual cycle in `CH^(n-r)(X x X)` inducing inverse Hard Lefschetz. Universally doing so is Standard Conjecture B itself.
- Bouali: state and prove the exact rationalized Picard identification, including derived tensor/exactness issues, support maps, splitting, and every downstream restriction argument.

## 5. Assumptions and critic verdict

### Assumptions

- Standard cohomological action convention for Chow correspondences on a smooth projective `n`-fold.
- Transposition preserves cycle codimension.
- Cohomology of a sheaf/complex of `Q`-vector spaces is a `Q`-vector space.
- `Pic(P^1_C)=Z` via degree.
- Source formulas are read literally; no unprinted negative Tate twist or coefficient correction is supplied.

### Critic verdict

🟢 **SURVIVES.** Both failures are source/target type mismatches, not disagreements about a difficult estimate.

🔴 **REFUTED AS WRITTEN:** the named proof corridors establish the universal Rational Hodge Conjecture.

🟡 **CONDITIONAL:** distinct repaired constructions could still exist, but each repair contains an unresolved theorem of the original difficulty.

## 6. Lean status

- 🔵 LEAN-SOURCE: `verification/b2-round42/HodgeClaimTypeFirewalls.lean` formalizes positive-versus-negative degree incompatibility and the failure of 2-divisibility in `Z`.
- ✅ LEAN-VERIFIED: pending clean replay.
- Chow groups, motives, Tate twists, cohomology, Picard schemes, logarithmic de Rham complexes, and the Hodge conjecture are not formalized.

## 7. Exact remaining gap

🚧 MISSING — a universally defined negative-degree algebraic Lefschetz correspondence and a separately correct algebraic-cycle generation theorem with coefficient, support, specialization, and rationality arrows proved end to end.

## 8. Provenance

- Exact round parent: `stevemoraco/qs@e345ef906a7b809e3c47e949e556b6417247ed06`.
- Shimizu source audit: `stevemoraco/RH@16a37553fbd9f987a4e6e2aa4d6754da4e11c429`.
- Bouali coefficient audit: `stevemoraco/RH@ec59038d85565ced4e4c05c5d75f894a098a9126`.
- Current Shimizu public record checked 2026-08-13: Preprints.org manuscript `202509.1435`, latest version shown as v1.
- Current Bouali public record checked 2026-08-13: arXiv `2312.09268`.

**FIVE-ALARM OFF.**
