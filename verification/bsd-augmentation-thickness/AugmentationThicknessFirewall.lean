import Mathlib

/-!
# BSD augmentation-thickness firewall

Finite arithmetic core only. If augmentation-local elementary factors have
positive exponents `e_j`, the augmented-fiber rank counts the factors while the
augmentation order sums their exponents. Their difference is the higher-layer
thickness excess.

This does NOT formalize the Iwasawa structure theorem, Selmer complexes,
p-adic L-functions, the complex L-function, or BSD.
-/

namespace Millennium.BSD.AugmentationThicknessFirewall

def augOrder (es : List ℕ) : ℕ := es.sum

def fiberRank (es : List ℕ) : ℕ := es.length

def thicknessExcess (es : List ℕ) : ℕ :=
  (es.map fun e => e - 1).sum

theorem augOrder_eq_fiberRank_add_excess
    (es : List ℕ) (hpos : ∀ e ∈ es, 1 ≤ e) :
    augOrder es = fiberRank es + thicknessExcess es := by
  induction es with
  | nil =>
      simp [augOrder, fiberRank, thicknessExcess]
  | cons a t ih =>
      have ha : 1 ≤ a := hpos a (by simp)
      have ht : ∀ e ∈ t, 1 ≤ e := by
        intro e he
        exact hpos e (by simp [he])
      have hit := ih ht
      simp [augOrder, fiberRank, thicknessExcess] at hit ⊢
      omega

theorem thicknessExcess_eq_zero_iff_all_one
    (es : List ℕ) (hpos : ∀ e ∈ es, 1 ≤ e) :
    thicknessExcess es = 0 ↔ ∀ e ∈ es, e = 1 := by
  induction es with
  | nil =>
      simp [thicknessExcess]
  | cons a t ih =>
      have ha : 1 ≤ a := hpos a (by simp)
      have ht : ∀ e ∈ t, 1 ≤ e := by
        intro e he
        exact hpos e (by simp [he])
      constructor
      · intro hz e he
        have hsum : (a - 1) + thicknessExcess t = 0 := by
          simpa [thicknessExcess] using hz
        have ha0 : a - 1 = 0 := by omega
        have ht0 : thicknessExcess t = 0 := by omega
        have ha1 : a = 1 := by omega
        have htail := (ih ht).1 ht0
        rcases List.mem_cons.mp he with rfl | he
        · exact ha1
        · exact htail e he
      · intro hall
        have ha1 : a = 1 := hall a (by simp)
        have htailall : ∀ e ∈ t, e = 1 := by
          intro e he
          exact hall e (by simp [he])
        have ht0 := (ih ht).2 htailall
        simp [thicknessExcess, ha1, ht0]

theorem augOrder_eq_fiberRank_iff_all_one
    (es : List ℕ) (hpos : ∀ e ∈ es, 1 ≤ e) :
    augOrder es = fiberRank es ↔ ∀ e ∈ es, e = 1 := by
  have hdecomp := augOrder_eq_fiberRank_add_excess es hpos
  constructor
  · intro h
    have hz : thicknessExcess es = 0 := by omega
    exact (thicknessExcess_eq_zero_iff_all_one es hpos).1 hz
  · intro hall
    have hz : thicknessExcess es = 0 :=
      (thicknessExcess_eq_zero_iff_all_one es hpos).2 hall
    omega

theorem first_thickness_counterexample :
    fiberRank [1] = fiberRank [2] ∧
    augOrder [1] ≠ augOrder [2] ∧
    thicknessExcess [2] = 1 := by
  norm_num [fiberRank, augOrder, thicknessExcess]

theorem arbitrary_excess_at_rank_one (d : ℕ) :
    fiberRank [d + 1] = 1 ∧
    augOrder [d + 1] = d + 1 ∧
    thicknessExcess [d + 1] = d := by
  simp [fiberRank, augOrder, thicknessExcess]

#print axioms augOrder_eq_fiberRank_add_excess
#print axioms thicknessExcess_eq_zero_iff_all_one
#print axioms augOrder_eq_fiberRank_iff_all_one
#print axioms first_thickness_counterexample
#print axioms arbitrary_excess_at_rank_one

end Millennium.BSD.AugmentationThicknessFirewall
