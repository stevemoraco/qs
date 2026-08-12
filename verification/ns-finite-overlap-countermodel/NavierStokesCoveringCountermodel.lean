import Mathlib

namespace NavierStokesCoveringCountermodel

/-- An equal-mass finite partition can have total mass one while every
single cell has arbitrarily small mass.  This is the finite algebraic
countermodel behind the failure of any pigeonhole lower bound depending
only on overlap and not on cover cardinality.

Interpret `N` pairwise disjoint cells as a cover with overlap exactly one.
Each cell has mass `1/N`; their algebraic total is one. -/
theorem equalCellTotal (N : ℕ) (hN : 0 < N) :
    (N : ℝ) * (1 / (N : ℝ)) = 1 := by
  have hNneNat : N ≠ 0 := Nat.ne_of_gt hN
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hNneNat
  field_simp [hNne]

/-- For every proposed positive scale-uniform fraction `c`, there is a
finite overlap-one equal-cell model of total mass one whose every cell
mass `1/N` is strictly below `c`.

Thus bounded overlap alone cannot imply that one member of an arbitrarily
fine cover carries a fixed positive fraction of the total mass. -/
theorem noUniformSingleCellFraction (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ,
      0 < N ∧
      (N : ℝ) * (1 / (N : ℝ)) = 1 ∧
      1 / (N : ℝ) < c := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / c)
  have hcInv : 0 < (1 / c : ℝ) := one_div_pos.mpr hc
  have hNposR : 0 < (N : ℝ) := lt_trans hcInv hN
  have hNpos : 0 < N := by exact_mod_cast hNposR
  have htotal : (N : ℝ) * (1 / (N : ℝ)) = 1 :=
    equalCellTotal N hNpos
  have hmul : 1 < (N : ℝ) * c := (div_lt_iff₀ hc).mp hN
  have hmul' : 1 < c * (N : ℝ) := by
    simpa [mul_comm] using hmul
  have hsmall : 1 / (N : ℝ) < c :=
    (div_lt_iff₀ hNposR).2 hmul'
  exact ⟨N, hNpos, htotal, hsmall⟩

#print axioms equalCellTotal
#print axioms noUniformSingleCellFraction

end NavierStokesCoveringCountermodel
