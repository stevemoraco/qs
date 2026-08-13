import Mathlib

/-!
# Indexed-decoder router normalization firewall: finite core

This file proves only finite bookkeeping used in a hostile audit of a proposed
block-localization theorem:

* coordinatewise compression recovers the active block under a one-active-block
  restriction;
* a subtraction-free closed form for the gate count of a specific pruned
  dyadic-OR one-hot encoder;
* integer ledgers for the unnormalized and normalized router constructions.

The encoder theorem is about the stated construction, not minimum circuit
complexity. This file does not formalize Boolean DAG syntax or evaluation,
Fan--Li--Yang, Chen--Li--Yang, a circuit lower bound, or P versus NP.
-/

namespace PNPIndexedDecoderLocalizationFirewall

/-- Coordinatewise OR, represented propositionally. -/
def compress {J I : Type} (x : J → I → Prop) : I → Prop :=
  fun i => ∃ j, x j i

/-- If every block except active is zero, coordinatewise OR recovers the
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

/-- Gate count of the explicit pruned dyadic-OR encoder on 2^r occupancy
inputs. Internal dyadic source wires remain exposed across the recursion.

This is an exact count for that construction. It does not assert that every
encoder, or even every OR-only encoder, needs this many gates. -/
def prunedDyadicEncoderCost : ℕ → ℕ
  | 0 => 0
  | r + 1 => 2 * prunedDyadicEncoderCost r + 2 * r

/-- Subtraction-free closed form for the pruned construction. -/
theorem prunedDyadicEncoderCost_closed_add (r : ℕ) :
    prunedDyadicEncoderCost r + 2 * r + 2 = 2 ^ (r + 1) := by
  induction r with
  | zero => norm_num [prunedDyadicEncoderCost]
  | succ r ih =>
      simp only [prunedDyadicEncoderCost, Nat.succ_eq_add_one]
      calc
        2 * prunedDyadicEncoderCost r + 2 * r + 2 * (r + 1) + 2 =
            2 * (prunedDyadicEncoderCost r + 2 * r + 2) := by ring
        _ = 2 * 2 ^ (r + 1) := by rw [ih]
        _ = 2 ^ ((r + 1) + 1) := by rw [pow_succ]

/-- The previously banked encoder expression exceeds the pruned expression
by exactly r gates. This is scalar bookkeeping only. -/
theorem encoder_expression_saving (k r : ℤ) :
    (2 * k - r - 2) - (2 * k - 2 - 2 * r) = r := by
  ring

/-- Keeping all k block-occupancy trees but using the pruned encoder yields
this valid, still unnormalized, construction ledger. -/
theorem unnormalized_router_gate_ledger (N k b r d : ℤ) :
    (N - k) + (N - b) + (2 * k - 2 - 2 * r) + d =
      2 * N + k - b - 2 - 2 * r + d := by
  ring

/-- In the partial-label compiler, index zero is represented by 0^r and the
encoder never reads the occupancy bit of block zero. Omitting that dead
(b-1)-gate tree gives the normalized construction ledger.

The hypothesis N=k*b is explicit. The theorem is an identity for a described
upper-bound construction, not a minimum-size theorem. -/
theorem normalized_router_gate_ledger
    (N k b r d : ℤ) (hN : N = k * b) :
    (k - 1) * (b - 1) + b * (k - 1) +
        (2 * k - 2 - 2 * r) + d =
      2 * N + k - 2 * b - 1 - 2 * r + d := by
  rw [hN]
  ring

/-- Relative to the original banked full-router expression, pruning both the
encoder and block-zero occupancy saves b+r-1 gates. -/
theorem original_to_normalized_saving (N k b r d : ℤ) :
    (2 * N + k - b - 2 - r + d) -
        (2 * N + k - 2 * b - 1 - 2 * r + d) =
      b + r - 1 := by
  ring

example : prunedDyadicEncoderCost 0 = 0 := by norm_num [prunedDyadicEncoderCost]
example : prunedDyadicEncoderCost 1 = 0 := by norm_num [prunedDyadicEncoderCost]
example : prunedDyadicEncoderCost 2 = 2 := by norm_num [prunedDyadicEncoderCost]
example : prunedDyadicEncoderCost 3 = 8 := by norm_num [prunedDyadicEncoderCost]
example : prunedDyadicEncoderCost 4 = 22 := by norm_num [prunedDyadicEncoderCost]

#print axioms compress_eq_active
#print axioms prunedDyadicEncoderCost_closed_add
#print axioms encoder_expression_saving
#print axioms unnormalized_router_gate_ledger
#print axioms normalized_router_gate_ledger
#print axioms original_to_normalized_saving

end PNPIndexedDecoderLocalizationFirewall
