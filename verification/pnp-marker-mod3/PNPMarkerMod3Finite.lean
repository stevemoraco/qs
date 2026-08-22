import Mathlib

namespace PNPMarkerMod3Finite

/-- The symmetric completion used by the paper proof. -/
def mod3Label (w : ℕ) : Bool := decide (w % 3 = 1)

/-- The marker obstruction's label as a function of the five weights it uses. -/
def markerWeightLabel (w : ℕ) : Bool := decide (w = 1 ∨ w = 4)

/-- On every Hamming layer inspected by the marker obstruction, the marker label
    is exactly residue-one modulo three. -/
theorem marker_agrees_with_mod3_on_relevant_weights
    (w : ℕ) (hw : w ≤ 4) :
    markerWeightLabel w = mod3Label w := by
  interval_cases w <;> norm_num [markerWeightLabel, mod3Label]

/-- One complementary Boolean pair contributes exactly one to Hamming weight. -/
theorem bool_complement_pair_weight (b : Bool) :
    (if b then 1 else 0) + (if b then 0 else 1) = 1 := by
  cases b <;> decide

/-- The residue-one completion shifts to residue zero after one complementary
    pair is inserted. -/
theorem mod3_pair_shift (rest : ℕ) :
    (rest + 1) % 3 = 1 ↔ rest % 3 = 0 := by
  omega

/-- A positive language whose positive inputs have weight at most `r` becomes
    identically negative after more than `r` complementary pairs have already
    contributed one `1` each. -/
theorem bounded_support_is_killed
    (positive : ℕ → Prop) (r t : ℕ)
    (hbound : ∀ w, positive w → w ≤ r)
    (ht : r < t) :
    ∀ z : ℕ, ¬ positive (t + z) := by
  intro z hz
  have hle : t + z ≤ r := hbound (t + z) hz
  omega

/-- The marker seed has positive weights only one and four, so five
    complementary-pair substitutions kill every positive input. -/
theorem five_pairs_kill_marker (t z : ℕ) (ht : 5 ≤ t) :
    ¬ (t + z = 1 ∨ t + z = 4) := by
  omega

/-- Five gates removed per two variables gives exactly one gate of surplus over
    a `2 per remaining variable` baseline at each induction step. -/
theorem five_for_two_surplus_identity (n t : ℤ) :
    5 * t + 2 * (n - 2 * t) = 2 * n + t := by
  ring

#print axioms marker_agrees_with_mod3_on_relevant_weights
#print axioms bool_complement_pair_weight
#print axioms mod3_pair_shift
#print axioms bounded_support_is_killed
#print axioms five_pairs_kill_marker
#print axioms five_for_two_surplus_identity

end PNPMarkerMod3Finite
