import Mathlib

/-!
# Navier--Stokes: symmetric shell-17 Beltrami stress frame

The six carriers

`(0,1,±4)`, `(1,±4,0)`, `(4,0,±1)`

all lie on the original shell `|k|^2=17`.  Their transverse-projector
stresses form a basis of symmetric 3-by-3 matrices, sum to `68 I`, and have an
explicit positive inverse throughout every coordinate box of radius
`epsilon < 482/5663` around the identity.  In particular, they are positive on
the active master box `epsilon=1/32`.

This is finite linear algebra.  It does not construct modulated Beltrami waves,
control analytic errors, or prove a Navier--Stokes solution or singularity.
-/

namespace Millennium.NavierStokes.Shell17BeltramiMasterFrame

noncomputable section

abbrev V3Z := Fin 3 → ℤ
abbrev Sym6Z := Fin 6 → ℤ
abbrev Sym6R := Fin 6 → ℝ

/-- Symmetric equal-shell carrier frame. -/
def carrier : Fin 6 → V3Z := ![
  ![0, 1, -4],
  ![0, 1, 4],
  ![1, -4, 0],
  ![1, 4, 0],
  ![4, 0, -1],
  ![4, 0, 1]
]

def dot (v w : V3Z) : ℤ :=
  v 0 * w 0 + v 1 * w 1 + v 2 * w 2

def normSq (v : V3Z) : ℤ := dot v v

/-- Every selected carrier remains on the original shell `|k|^2=17`. -/
theorem carrier_equal_shell (i : Fin 6) : normSq (carrier i) = 17 := by
  fin_cases i <;> decide

/-- The selected carriers are distinct modulo sign. -/
theorem distinct_not_equal_or_antipodal
    {i j : Fin 6} (hij : i ≠ j) :
    carrier i ≠ carrier j ∧ carrier i ≠ -carrier j := by
  fin_cases i <;> fin_cases j <;> simp_all [carrier] <;> decide

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
  ![17, 16, 1, 0, 0, 4],
  ![17, 16, 1, 0, 0, -4],
  ![16, 1, 17, 4, 0, 0],
  ![16, 1, 17, -4, 0, 0],
  ![1, 17, 16, 0, 4, 0],
  ![1, 17, 16, 0, -4, 0]
]

theorem qStress_eq_projectorStress (i : Fin 6) :
    qStress i = projectorStress (carrier i) := by
  fin_cases i <;> ext j <;> fin_cases j <;> decide

/-- Equal positive amplitudes give `68 I`. -/
def target68I : Sym6Z := ![68, 68, 68, 0, 0, 0]

theorem isotropic_sum (j : Fin 6) :
    qStress 0 j + qStress 1 j + qStress 2 j + qStress 3 j
      + qStress 4 j + qStress 5 j = target68I j := by
  fin_cases j <;> decide

/-- Coordinates of the synthesized symmetric stress. -/
def coneCoordinates (a : Fin 6 → ℝ) : Sym6R := ![
  17*a 0 + 17*a 1 + 16*a 2 + 16*a 3 + a 4 + a 5,
  16*a 0 + 16*a 1 + a 2 + a 3 + 17*a 4 + 17*a 5,
  a 0 + a 1 + 17*a 2 + 17*a 3 + 16*a 4 + 16*a 5,
  4*a 2 - 4*a 3,
  4*a 4 - 4*a 5,
  4*a 0 - 4*a 1
]

/-- Exact inverse coefficients. -/
def weight (m : Sym6R) : Fin 6 → ℝ := ![
  (273*m 0 + 239*m 1 - 271*m 2) / 16388 + m 5/8,
  (273*m 0 + 239*m 1 - 271*m 2) / 16388 - m 5/8,
  (239*m 0 - 271*m 1 + 273*m 2) / 16388 + m 3/8,
  (239*m 0 - 271*m 1 + 273*m 2) / 16388 - m 3/8,
  (-271*m 0 + 273*m 1 + 239*m 2) / 16388 + m 4/8,
  (-271*m 0 + 273*m 1 + 239*m 2) / 16388 - m 4/8
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

/-- The identity coefficient is `1/68` in every direction. -/
theorem weight_identity (i : Fin 6) :
    weight identityStress i = (1 : ℝ) / 68 := by
  fin_cases i
  · change ((273*(1:ℝ) + 239*1 - 271*1) / 16388 + 0/8) = (1:ℝ)/68
    norm_num
  · change ((273*(1:ℝ) + 239*1 - 271*1) / 16388 - 0/8) = (1:ℝ)/68
    norm_num
  · change ((239*(1:ℝ) - 271*1 + 273*1) / 16388 + 0/8) = (1:ℝ)/68
    norm_num
  · change ((239*(1:ℝ) - 271*1 + 273*1) / 16388 - 0/8) = (1:ℝ)/68
    norm_num
  · change ((-271*(1:ℝ) + 273*1 + 239*1) / 16388 + 0/8) = (1:ℝ)/68
    norm_num
  · change ((-271*(1:ℝ) + 273*1 + 239*1) / 16388 - 0/8) = (1:ℝ)/68
    norm_num

/-- Coordinate box of radius `epsilon` around the identity. -/
def InIdentityBox (epsilon : ℝ) (m : Sym6R) : Prop :=
  1 - epsilon ≤ m 0 ∧ m 0 ≤ 1 + epsilon ∧
  1 - epsilon ≤ m 1 ∧ m 1 ≤ 1 + epsilon ∧
  1 - epsilon ≤ m 2 ∧ m 2 ≤ 1 + epsilon ∧
  -epsilon ≤ m 3 ∧ m 3 ≤ epsilon ∧
  -epsilon ≤ m 4 ∧ m 4 ≤ epsilon ∧
  -epsilon ≤ m 5 ∧ m 5 ≤ epsilon

/-- Exact coordinate-box positivity radius. -/
def positivityRadius : ℝ := 482 / 5663

theorem master_radius_inside : (1 : ℝ) / 32 < positivityRadius := by
  norm_num [positivityRadius]

/-- Every inverse coefficient is strictly positive throughout an identity box
of radius below `482/5663`. -/
theorem weight_pos_of_identity_box
    {epsilon : ℝ} {m : Sym6R}
    (hepsilon : epsilon < positivityRadius)
    (hbox : InIdentityBox epsilon m) :
    ∀ i, 0 < weight m i := by
  rcases hbox with
    ⟨h0lo, h0hi, h1lo, h1hi, h2lo, h2hi,
      h3lo, h3hi, h4lo, h4hi, h5lo, h5hi⟩
  intro i
  fin_cases i
  · change 0 < (273*m 0 + 239*m 1 - 271*m 2) / 16388 + m 5/8
    dsimp [positivityRadius] at hepsilon
    linarith
  · change 0 < (273*m 0 + 239*m 1 - 271*m 2) / 16388 - m 5/8
    dsimp [positivityRadius] at hepsilon
    linarith
  · change 0 < (239*m 0 - 271*m 1 + 273*m 2) / 16388 + m 3/8
    dsimp [positivityRadius] at hepsilon
    linarith
  · change 0 < (239*m 0 - 271*m 1 + 273*m 2) / 16388 - m 3/8
    dsimp [positivityRadius] at hepsilon
    linarith
  · change 0 < (-271*m 0 + 273*m 1 + 239*m 2) / 16388 + m 4/8
    dsimp [positivityRadius] at hepsilon
    linarith
  · change 0 < (-271*m 0 + 273*m 1 + 239*m 2) / 16388 - m 4/8
    dsimp [positivityRadius] at hepsilon
    linarith

/-- The active master box is the radius `1/32` box. -/
def InMasterBox (m : Sym6R) : Prop := InIdentityBox ((1 : ℝ) / 32) m

theorem weight_pos_of_master_box
    {m : Sym6R} (hbox : InMasterBox m) :
    ∀ i, 0 < weight m i := by
  apply weight_pos_of_identity_box master_radius_inside
  simpa [InMasterBox] using hbox

/-- Exact local positive geometric lemma on the original shell and at the
active master radius. -/
theorem positive_decomposition_of_master_box
    {m : Sym6R} (hbox : InMasterBox m) :
    (∀ i, 0 < weight m i) ∧ coneCoordinates (weight m) = m := by
  exact ⟨weight_pos_of_master_box hbox, cone_weight_reconstruct m⟩

#print axioms carrier_equal_shell
#print axioms distinct_not_equal_or_antipodal
#print axioms qStress_eq_projectorStress
#print axioms isotropic_sum
#print axioms cone_weight_reconstruct
#print axioms weight_coneCoordinates
#print axioms weight_identity
#print axioms master_radius_inside
#print axioms weight_pos_of_identity_box
#print axioms weight_pos_of_master_box
#print axioms positive_decomposition_of_master_box

end

end Millennium.NavierStokes.Shell17BeltramiMasterFrame
