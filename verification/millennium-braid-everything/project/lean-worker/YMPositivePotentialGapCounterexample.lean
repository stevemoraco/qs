import Mathlib

/-!
# Yang--Mills: positive potentials do not preserve a vacuum-subtracted gap

This file formalizes the finite scalar core of an audit of V. P. Nair,
*Towards a Proof of Mass Gap in 3d Yang-Mills Theory*, arXiv:2608.10133
(10 August 2026).

Grant a two-level kinetic operator with energies `0` and `m`, so its spectral
gap is `m`.  Add the nonnegative diagonal potential with energies `m-ε` and
`0`.  The full energies are then `m-ε` and `m`: the operator has increased in
each level, but the gap above its actual ground energy is only `ε`.

This is not a construction of a Yang--Mills Hamiltonian.  It refutes only the
generic operator inference

`V ≥ 0`, `H = T + V`, `gap(T) ≥ m`  implies  `gap(H) ≥ m`.

A valid transfer needs additional control of the full vacuum, such as a common
zero mode, or a direct Poincare/min--max estimate relative to the ground state
of `H`.
-/

namespace YMPositivePotentialGapCounterexample

/-- Exact two-level counterexample.  The kinetic gap is `m`; the positive
potential raises only the old vacuum; the full vacuum-subtracted gap is `ε`. -/
theorem positive_potential_can_shrink_gap
    {m ε : ℝ}
    (hm : 0 < m)
    (hε : 0 < ε)
    (hεm : ε < m) :
    let kineticGround : ℝ := 0
    let kineticExcited : ℝ := m
    let potentialGround : ℝ := m - ε
    let potentialExcited : ℝ := 0
    let fullGround : ℝ := kineticGround + potentialGround
    let fullExcited : ℝ := kineticExcited + potentialExcited
    0 ≤ potentialGround ∧
    0 ≤ potentialExcited ∧
    kineticGround ≤ fullGround ∧
    kineticExcited ≤ fullExcited ∧
    kineticExcited - kineticGround = m ∧
    fullExcited - fullGround = ε := by
  dsimp
  constructor
  · linarith
  constructor
  · norm_num
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> ring

/-- For every requested positive gap floor `δ`, one can choose a positive
perturbed gap below `δ` while keeping the original kinetic gap equal to `m`. -/
theorem no_uniform_full_gap_floor_from_positive_potential
    {m δ : ℝ}
    (hm : 0 < m)
    (hδ : 0 < δ) :
    ∃ ε : ℝ,
      0 < ε ∧ ε < m ∧ ε < δ ∧
      let kineticGround : ℝ := 0
      let kineticExcited : ℝ := m
      let potentialGround : ℝ := m - ε
      let potentialExcited : ℝ := 0
      let fullGround : ℝ := kineticGround + potentialGround
      let fullExcited : ℝ := kineticExcited + potentialExcited
      0 ≤ potentialGround ∧
      0 ≤ potentialExcited ∧
      kineticGround ≤ fullGround ∧
      kineticExcited ≤ fullExcited ∧
      kineticExcited - kineticGround = m ∧
      fullExcited - fullGround = ε := by
  let ε : ℝ := min m δ / 2
  have hmin : 0 < min m δ := lt_min hm hδ
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hεm : ε < m := by
    have hle : min m δ ≤ m := min_le_left m δ
    dsimp [ε]
    linarith
  have hεδ : ε < δ := by
    have hle : min m δ ≤ δ := min_le_right m δ
    dsimp [ε]
    linarith
  refine ⟨ε, hε, hεm, hεδ, ?_⟩
  exact positive_potential_can_shrink_gap hm hε hεm

/-- An absolute lower bound on the first excited energy is not the same as a
lower bound on its distance from the actual ground energy. -/
theorem excited_energy_bound_does_not_bound_gap
    {m ε ground excited : ℝ}
    (hm : 0 < m)
    (hε : 0 < ε)
    (hεm : ε < m)
    (hground : ground = m - ε)
    (hexcited : excited = m) :
    m ≤ excited ∧ excited - ground = ε := by
  constructor
  · linarith
  · rw [hground, hexcited]
    ring

/-- After subtracting the raised vacuum energy, the full excited energy is
`ε`, so the unshifted comparison `T ≤ H` no longer survives on the excited
coordinate. -/
theorem vacuum_subtraction_breaks_unshifted_order
    {m ε : ℝ}
    (hε : 0 < ε)
    (hεm : ε < m) :
    let kineticExcited : ℝ := m
    let fullGround : ℝ := m - ε
    let fullExcited : ℝ := m
    let shiftedFullExcited : ℝ := fullExcited - fullGround
    ¬ (kineticExcited ≤ shiftedFullExcited) := by
  dsimp
  linarith

#print axioms positive_potential_can_shrink_gap
#print axioms no_uniform_full_gap_floor_from_positive_potential
#print axioms excited_energy_bound_does_not_bound_gap
#print axioms vacuum_subtraction_breaks_unshifted_order

end YMPositivePotentialGapCounterexample
