import Mathlib

/-!
# Indexed-decoder localization firewall: finite core

This file proves only two exact pieces of finite bookkeeping used in a hostile
audit of a proposed block-localization theorem:

* coordinatewise compression recovers the active block under a one-active-block
  restriction;
* the explicit gate ledger for occupancy, compression, a recursive one-hot
  encoder, and one indexed decoder.

It does not formalize Boolean circuit size, minimum restricted complexity,
Fan--Li--Yang, Chen--Li--Yang, a circuit lower bound, or P versus NP.
-/

namespace PNPIndexedDecoderLocalizationFirewall

/-- Coordinatewise OR, represented propositionally. -/
def compress {J I : Type} (x : J → I → Prop) : I → Prop :=
  fun i => ∃ j, x j i

/-- If every block except `active` is zero, coordinatewise OR recovers the
active block exactly. -/
theorem compress_eq_active
    {J I : Type} (x : J → I → Prop) (active : J)
    (outside_zero : ∀ j, j ≠ active → ∀ i, ¬ x j i) :
    compress x = x active := by
  funext i
  apply propext
  constructor
  · rintro ⟨j, hji⟩
    by_cases hja : j = active
    · simpa [hja] using hji
    · exact False.elim (outside_zero j hja i hji)
  · intro hai
    exact ⟨active, hai⟩

/-- Exact size of the recursive one-hot encoder ledger for `2^r` inputs.
At a recursion node one OR forms the occupancy flag and one OR is used for
each lower output bit. -/
def encoderCost : ℕ → ℤ
  | 0 => 0
  | r + 1 => 2 * encoderCost r + (r + 1)

theorem encoderCost_closed (r : ℕ) :
    encoderCost r = (2 : ℤ) ^ (r + 1) - (r : ℤ) - 2 := by
  induction r with
  | zero => norm_num [encoderCost]
  | succ r ih =>
      rw [encoderCost, ih]
      push_cast
      rw [pow_succ]
      ring

/-- Gate-count ledger for `N=k*b` input bits:

* `N-k`: block occupancy ORs;
* `N-b`: coordinatewise block compression;
* `2k-r-2`: recursive one-hot encoder for `k=2^r` blocks;
* `d`: one shared indexed decoder.

The identity is over integers to expose every surplus term without truncated
natural subtraction.
-/
theorem indexed_decoder_gate_ledger (N k b r d : ℤ) :
    (N - k) + (N - b) + (2 * k - r - 2) + d =
      2 * N + k - b - r - 2 + d := by
  ring

/-- If the one-hot encoder is instantiated at `k=2^r`, its exact closed
cost agrees with the term in the gate ledger. -/
theorem encoderCost_at_power (r : ℕ) :
    encoderCost r =
      2 * ((2 : ℤ) ^ r) - (r : ℤ) - 2 := by
  rw [encoderCost_closed, pow_succ]
  ring

#print axioms compress_eq_active
#print axioms encoderCost_closed
#print axioms indexed_decoder_gate_ledger
#print axioms encoderCost_at_power

end PNPIndexedDecoderLocalizationFirewall
