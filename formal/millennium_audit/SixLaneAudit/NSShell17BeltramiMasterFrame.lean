import Mathlib

/-!
# Navier--Stokes: shell-17 Beltrami stress frame at the master delta

Five carriers from the current shell-17 design, together with the additional
carrier `(2,-2,-3)`, give six transverse-projector stresses forming a basis of
symmetric 3-by-3 matrices.  Their explicit inverse is strictly positive on the
coordinate box of radius `1/32` around the identity, exactly matching the
`delta = 1/32` master point in the active exponent ledger.

This is finite linear algebra.  It does not construct modulated Beltrami waves,
control analytic errors, or prove a Navier--Stokes solution or singularity.
-/

namespace Millennium.NavierStokes.Shell17BeltramiMasterFrame

abbrev V3Z := Fin 3 → ℤ
abbrev Sym6Z := Fin 6 → ℤ
abbrev Sym6R := Fin 6 → ℝ

/-- Five old shell-17 carriers and one added carrier. -/
def carrier : Fin 6 → V3Z := ![
  ![0, 4, 1],
  ![4, 0, 1],
  ![2, -2, 3],
  ![2, 2, 3],
  ![3, 2, -2],
  ![2, -2, -3]
]

def dot (v w : V3Z) : ℤ :=
  v 0 * w 0 + v 1 * w 1 + v 2 * w 2

def normSq (v : V3Z) : ℤ := dot v v

/-- Every selected carrier remains on the original shell `|k|^2=17`. -/
theorem carrier_equal_shell (i : Fin 6) : normSq (carrier i) = 17 := by
  fin_cases i <;> norm_num [normSq, dot, carrier]

/-- The selected carriers are distinct modulo sign. -/
theorem distinct_not_equal_or_antipodal
    {i j : Fin 6} (hij : i ≠ j) :
    carrier i ≠ carrier j ∧ carrier i ≠ -carrier j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [carrier] at hij ⊢

/-- Symmetric matrices use `(xx,yy,zz,xy,xz,yz)`. -/
def projectorStress (k : V3Z) : Sym6Z := ![
  17 - k 0 ^ 2,
  17 - k 1 ^ 2,
  17 - k 2 ^ 2,
  -(k 0 * k 1),
  -(k 0 * k 2),
  -(k 1 * k 2)
]

/-- Exact table of `Q_k=17I-k tensor k`. -/
def qStress : Fin 6 → Sym6Z := ![
  ![17, 1, 16, 0, 0, -4],
  ![1, 17, 16, 0, -4, 0],
  ![13, 13, 8, 4, -6, 6],
  ![13, 13, 8, -4, -6, -6],
  ![8, 13, 13, -6, 6, 4],
  ![13, 13, 8, 4, 6, -6]
]

theorem qStress_eq_projectorStress (i : Fin 6) :
    qStress i = projectorStress (carrier i) := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [qStress, projectorStress, carrier]

/-- Coordinates of the synthesized symmetric stress. -/
def coneCoordinates (a : Fin 6 → ℝ) : Sym6R := ![
  17*a 0 + a 1 + 13*a 2 + 13*a 3 + 8*a 4 + 13*a 5,
  a 0 + 17*a 1 + 13*a 2 + 13*a 3 + 13*a 4 + 13*a 5,
  16*a 0 + 16*a 1 + 8*a 2 + 8*a 3 + 13*a 4 + 8*a 5,
  4*a 2 - 4*a 3 - 6*a 4 + 4*a 5,
  -4*a 1 - 6*a 2 - 6*a 3 + 6*a 4 + 6*a 5,
  -4*a 0 + 6*a 2 - 6*a 3 + 4*a 4 - 6*a 5
]

/-- Exact inverse coefficients. -/
def weight (m : Sym6R) : Fin 6 → ℝ := ![
  (155*m 0 - 491*m 1 + 495*m 2) / 10336
    + 3*m 3/304 - m 4/152 - m 5/152,
  (-523*m 0 + 123*m 1 + 497*m 2) / 10336
    + 9*m 3/304 - 3*m 4/152 - 3*m 5/152,
  (907*m 0 + 261*m 1 - 521*m 2) / 31008
    + 11*m 3/304 - 11*m 4/456 + 9*m 5/152,
  (13*m 0 + 13*m 1 - 21*m 2) / 646
    - 5*m 3/76 - 3*m 4/76 - 3*m 5/76,
  (16*m 0 + 16*m 1 - m 2) / 1615
    - 6*m 3/95 + 4*m 4/95 + 4*m 5/95,
  (889*m 0 + 4119*m 1 - 2579*m 2) / 155040
    + 81*m 3/1520 + 109*m 4/2280 - 27*m 5/760
]

/-- The inverse reconstructs every symmetric stress exactly. -/
theorem cone_weight_reconstruct (m : Sym6R) :
    coneCoordinates (weight m) = m := by
  funext j
  fin_cases j <;> simp [coneCoordinates, weight] <;> ring

/-- The inverse is also a left inverse, so these six projectors form a basis. -/
theorem weight_coneCoordinates (a : Fin 6 → ℝ) :
    weight (coneCoordinates a) = a := by
  funext j
  fin_cases j <;> simp [coneCoordinates, weight] <;> ring

/-- Identity stress. -/
def identityStress : Sym6R := ![1, 1, 1, 0, 0, 0]

/-- Exact strictly positive identity coefficients. -/
def identityWeight : Fin 6 → ℝ := ![
  159/10336,
  97/10336,
  647/31008,
  5/646,
  31/1615,
  2429/155040
]

theorem weight_identity (i : Fin 6) :
    weight identityStress i = identityWeight i := by
  fin_cases i <;> norm_num [weight, identityStress, identityWeight]

theorem identityWeight_pos (i : Fin 6) : 0 < identityWeight i := by
  fin_cases i <;> norm_num [identityWeight]

/-- The exact coordinate box used by the active master point `delta=1/32`. -/
def InMasterBox (m : Sym6R) : Prop :=
  (31:ℝ)/32 ≤ m 0 ∧ m 0 ≤ (33:ℝ)/32 ∧
  (31:ℝ)/32 ≤ m 1 ∧ m 1 ≤ (33:ℝ)/32 ∧
  (31:ℝ)/32 ≤ m 2 ∧ m 2 ≤ (33:ℝ)/32 ∧
  -(1:ℝ)/32 ≤ m 3 ∧ m 3 ≤ (1:ℝ)/32 ∧
  -(1:ℝ)/32 ≤ m 4 ∧ m 4 ≤ (1:ℝ)/32 ∧
  -(1:ℝ)/32 ≤ m 5 ∧ m 5 ≤ (1:ℝ)/32

/-- Every shell-17 inverse coefficient is strictly positive throughout the
master box. -/
theorem weight_pos_of_master_box
    {m : Sym6R} (hbox : InMasterBox m) :
    ∀ i, 0 < weight m i := by
  rcases hbox with
    ⟨h0lo, h0hi, h1lo, h1hi, h2lo, h2hi,
      h3lo, h3hi, h4lo, h4hi, h5lo, h5hi⟩
  intro i
  fin_cases i <;> simp [weight]
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith

/-- Exact local positive geometric lemma on the original shell and at the
active master radius. -/
theorem positive_decomposition_of_master_box
    {m : Sym6R} (hbox : InMasterBox m) :
    (∀ i, 0 < weight m i) ∧ coneCoordinates (weight m) = m := by
  exact ⟨weight_pos_of_master_box hbox, cone_weight_reconstruct m⟩

#print axioms carrier_equal_shell
#print axioms distinct_not_equal_or_antipodal
#print axioms qStress_eq_projectorStress
#print axioms cone_weight_reconstruct
#print axioms weight_coneCoordinates
#print axioms weight_identity
#print axioms identityWeight_pos
#print axioms weight_pos_of_master_box
#print axioms positive_decomposition_of_master_box

end Millennium.NavierStokes.Shell17BeltramiMasterFrame
