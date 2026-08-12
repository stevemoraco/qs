import Mathlib

/-!
B4 AUTO19 run8 — P vs NP uniformity/quantifier firewall.

Status at commit: 🟢 PROVED (logical core) · 🔵 LEAN-SOURCE · 🟡 compile pending.
Official Millennium status: no P versus NP claim.

Exact theorem identities:
* `pointwise_exponent_choices_exist`
* `no_single_exponent_bounds_all_indices`
* `pointwise_choice_does_not_uniformize`
* `fixed_exponent_lower_bound_refutes_fixed_exponent_collapse`

Assumptions: none beyond the displayed abstract predicate in the terminal theorem.
Provenance: current PNP hardness-magnification bank, especially the fixed/growing-exponent
frontier mirrored in qs PR #152 and the selector-uniformity firewalls in prior B4 banks.
Audit: no `sorry`, `admit`, `sorryAx`, custom axiom, `opaque`, or `unsafe` in this source.
Compile status at commit: pending independent runner replay.
Exact remaining gap: prove an unrestricted circuit lower bound with the correct uniform
quantifiers; pointwise or input-dependent exponent/decoder choices cannot be promoted to a
single fixed family without a theorem.
-/

namespace B4Auto19Run8.PNP

theorem pointwise_exponent_choices_exist :
    ∀ n : ℕ, ∃ k : ℕ, n ≤ k := by
  intro n
  exact ⟨n, le_rfl⟩

theorem no_single_exponent_bounds_all_indices :
    ¬ ∃ k : ℕ, ∀ n : ℕ, n ≤ k := by
  rintro ⟨k, hk⟩
  have h := hk (k + 1)
  omega

theorem pointwise_choice_does_not_uniformize :
    (∀ n : ℕ, ∃ k : ℕ, n ≤ k) ∧
    ¬ (∃ k : ℕ, ∀ n : ℕ, n ≤ k) := by
  exact ⟨pointwise_exponent_choices_exist, no_single_exponent_bounds_all_indices⟩

theorem fixed_exponent_lower_bound_refutes_fixed_exponent_collapse
    {Upper : ℕ → ℕ → Prop}
    (collapse : ∃ k : ℕ, ∀ n : ℕ, Upper k n)
    (lower : ∀ k : ℕ, ∃ n : ℕ, ¬ Upper k n) :
    False := by
  rcases collapse with ⟨k, hk⟩
  rcases lower k with ⟨n, hn⟩
  exact hn (hk n)

#print axioms pointwise_exponent_choices_exist
#print axioms no_single_exponent_bounds_all_indices
#print axioms pointwise_choice_does_not_uniformize
#print axioms fixed_exponent_lower_bound_refutes_fixed_exponent_collapse

end B4Auto19Run8.PNP
