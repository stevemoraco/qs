import Mathlib

namespace RHDivisorPhaseReplicationObstruction

/-- A natural number dividing two coprime natural numbers must be one. In the
floor-sum application, the common divisor indexes the only carrier that can
jump in a residue cell coprime to the common period. -/
theorem common_divisor_of_coprimes_eq_one
    {d m Q : ℕ}
    (hcop : m.Coprime Q)
    (hdm : d ∣ m)
    (hdQ : d ∣ Q) :
    d = 1 := by
  exact Nat.eq_one_of_dvd_coprimes hcop hdm hdQ

/-- Exact support collapse: among divisors of `Q`, the only one that can also
 divide a cell index coprime to `Q` is `1`. -/
theorem common_divisor_iff_one
    {d m Q : ℕ}
    (hcop : m.Coprime Q) :
    (d ∣ m ∧ d ∣ Q) ↔ d = 1 := by
  constructor
  · rintro ⟨hdm, hdQ⟩
    exact common_divisor_of_coprimes_eq_one hcop hdm hdQ
  · intro hd
    subst d
    simp

/-- If the target jump at cell `1` is replicated at another cell and every
preceding cell value is nonnegative, then the replicated cell also has value
at least one. This is the exact finite order core of the divisor-phase
replication obstruction. -/
theorem replicated_target_jump_forces_cell
    (f jump : ℕ → ℤ)
    {m : ℕ}
    (hm : 1 ≤ m)
    (hzero : f 0 = 0)
    (hrec : ∀ n, 1 ≤ n → f n = f (n - 1) + jump n)
    (hrepl : jump m = jump 1)
    (htarget : 1 ≤ f 1)
    (hnonneg : ∀ n, 0 ≤ f n) :
    1 ≤ f m := by
  have hrec1 := hrec 1 (by omega)
  have hrecm := hrec m hm
  have hprev := hnonneg (m - 1)
  have hjump : 1 ≤ jump 1 := by
    omega
  omega

/-- Nonnegativity and the target cell alone do not control another cell when
jump replication is absent. -/
def counterCell (n : ℕ) : ℤ :=
  if n = 1 then 1 else 0

theorem target_without_replication_countermodel :
    1 ≤ counterCell 1 ∧
    (∀ n, 0 ≤ counterCell n) ∧
    ¬ 1 ≤ counterCell 2 := by
  refine ⟨by norm_num [counterCell], ?_, by norm_num [counterCell]⟩
  intro n
  by_cases h : n = 1 <;> simp [counterCell, h]

/-- Exact reciprocal weight of one unit cell. Under `u = 1/x`, this is the
`L¹` cost forced by a floor-sum value at least one on `[m,m+1)`. -/
theorem reciprocal_cell_weight
    {m : ℚ}
    (hm : 0 < m) :
    1 / m - 1 / (m + 1) = 1 / (m * (m + 1)) := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hm10 : m + 1 ≠ 0 := by linarith
  field_simp [hm0, hm10]
  ring

#print axioms common_divisor_of_coprimes_eq_one
#print axioms common_divisor_iff_one
#print axioms replicated_target_jump_forces_cell
#print axioms target_without_replication_countermodel
#print axioms reciprocal_cell_weight

end RHDivisorPhaseReplicationObstruction
