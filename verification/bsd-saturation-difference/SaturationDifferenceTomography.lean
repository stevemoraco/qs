import Mathlib

/-!
# BSD saturation-difference finite tomography core

Finite combinatorial shadow of the Z_p-module layer-length calculation.
This file proves only the exact arithmetic identities used by the BSD
saturation-depth firewall. It does NOT prove Birch--Swinnerton-Dyer,
Selmer control, Sha finiteness, or any analytic-to-arithmetic bridge.
-/

namespace Millennium.BSD.SaturationDifference

/-- Synthetic layer length for a free rank `r` plus cyclic p-power torsion
exponents `es`: `r*n + sum min(n,e_i)`. -/
def layerLength (r n : ℕ) (es : List ℕ) : ℕ :=
  r * n + (es.map (fun e => min n e)).sum

/-- Once every torsion exponent is at most `E`, truncation at depth `E`
already sees every torsion summand in full. -/
theorem sum_min_saturated (E : ℕ) (es : List ℕ)
    (h : ∀ e ∈ es, e ≤ E) :
    (es.map (fun e => min E e)).sum = es.sum := by
  induction es with
  | nil => simp
  | cons e es ih =>
      have he : e ≤ E := h e (by simp)
      have htail : ∀ x ∈ es, x ≤ E := by
        intro x hx
        exact h x (by simp [hx])
      simp [min_eq_right he, ih htail]

/-- With a known torsion exponent ceiling `E`, the next layer increment is
exactly the free rank. -/
theorem saturated_first_difference (r E : ℕ) (es : List ℕ)
    (h : ∀ e ∈ es, e ≤ E) :
    layerLength r (E + 1) es - layerLength r E es = r := by
  have hnext : ∀ e ∈ es, e ≤ E + 1 := by
    intro e he
    exact le_trans (h e he) (by omega)
  have hsE := sum_min_saturated E es h
  have hsN := sum_min_saturated (E + 1) es hnext
  unfold layerLength
  rw [hsN, hsE]
  rw [Nat.mul_add]
  omega

/-- At every finite observation depth `m`, one free copy and one torsion
summand of exponent `m+1` have identical layer lengths through depth `m`. -/
theorem finite_prefix_ambiguous (m n : ℕ) (hn : n ≤ m) :
    layerLength 1 n [] = layerLength 0 n [m + 1] := by
  have hnm1 : n ≤ m + 1 := by omega
  unfold layerLength
  simp [min_eq_left hnm1]

/-- The two synthetic modules used in the ambiguity witness have distinct
free ranks. -/
theorem ambiguity_ranks_distinct : (1 : ℕ) ≠ 0 := by
  norm_num

#print axioms sum_min_saturated
#print axioms saturated_first_difference
#print axioms finite_prefix_ambiguous
#print axioms ambiguity_ranks_distinct

end Millennium.BSD.SaturationDifference
