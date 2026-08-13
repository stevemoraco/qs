import Mathlib

/-!
# Navier--Stokes: a repaired six-carrier Beltrami stress frame

The six integer carriers

`(1, +/-1, 0)`, `(1, 0, +/-1)`, `(0, 1, +/-1)`

all lie on the same shell `|k|^2 = 2`.  Their same-helicity Beltrami
phase-averaged stress generators are, up to a positive scalar,

`Q_k = 2 I - k tensor k`.

Unlike the nine-carrier family isolated in
`NSBeltramiCarrierConeObstruction.lean`, these six `Q_k` form a basis of the
six-dimensional symmetric-matrix space, represent the identity with strictly
positive coefficients, and have an explicit positive inverse on a box of
radius `< 1/9` around the identity.

This is an exact finite geometric lemma.  It does not construct localized
Beltrami packets, control commutators, solve the Reynolds system, or produce a
Navier--Stokes solution.
-/

namespace Millennium.NavierStokes.BeltramiSixCarrierFrame

abbrev V3Z := Fin 3 → ℤ
abbrev Sym6Z := Fin 6 → ℤ
abbrev Sym6R := Fin 6 → ℝ

/-- Six equal-shell carriers, one antipodal-free representative from each
coordinate-diagonal pair. -/
def carrier : Fin 6 → V3Z := ![
  ![1, 1, 0],
  ![1, -1, 0],
  ![1, 0, 1],
  ![1, 0, -1],
  ![0, 1, 1],
  ![0, 1, -1]
]

/-- Integer dot product in three coordinates. -/
def dot (v w : V3Z) : ℤ :=
  v 0 * w 0 + v 1 * w 1 + v 2 * w 2

def normSq (v : V3Z) : ℤ := dot v v

/-- Every carrier lies on the shell of squared radius `2`. -/
theorem carrier_equal_shell (i : Fin 6) : normSq (carrier i) = 2 := by
  fin_cases i <;> norm_num [normSq, dot, carrier]

/-- Distinct listed carriers are neither equal nor antipodal. -/
theorem distinct_not_equal_or_antipodal
    {i j : Fin 6} (hij : i ≠ j) :
    carrier i ≠ carrier j ∧ carrier i ≠ -carrier j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [carrier] at hij ⊢

/-- Symmetric matrices use coordinate order `(xx, yy, zz, xy, xz, yz)`. -/
def projectorStress (k : V3Z) : Sym6Z := ![
  2 - k 0 ^ 2,
  2 - k 1 ^ 2,
  2 - k 2 ^ 2,
  -(k 0 * k 1),
  -(k 0 * k 2),
  -(k 1 * k 2)
]

/-- Exact table of `Q_k = 2 I - k tensor k`. -/
def qStress : Fin 6 → Sym6Z := ![
  ![1, 1, 2, -1, 0, 0],
  ![1, 1, 2, 1, 0, 0],
  ![1, 2, 1, 0, -1, 0],
  ![1, 2, 1, 0, 1, 0],
  ![2, 1, 1, 0, 0, -1],
  ![2, 1, 1, 0, 0, 1]
]

theorem qStress_eq_projectorStress (i : Fin 6) :
    qStress i = projectorStress (carrier i) := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [qStress, projectorStress, carrier]

/-- Equal positive amplitudes give an isotropic stress: the six generators sum
to `8 I`. -/
def target8I : Sym6Z := ![8, 8, 8, 0, 0, 0]

theorem isotropic_sum (j : Fin 6) :
    qStress 0 j + qStress 1 j + qStress 2 j + qStress 3 j
      + qStress 4 j + qStress 5 j = target8I j := by
  fin_cases j <;> norm_num [qStress, target8I]

/-- Coordinates of a linear combination of the six projector generators. -/
def coneCoordinates (a : Fin 6 → ℝ) : Sym6R := ![
  a 0 + a 1 + a 2 + a 3 + 2*a 4 + 2*a 5,
  a 0 + a 1 + 2*a 2 + 2*a 3 + a 4 + a 5,
  2*a 0 + 2*a 1 + a 2 + a 3 + a 4 + a 5,
  -a 0 + a 1,
  -a 2 + a 3,
  -a 4 + a 5
]

/-- Explicit inverse coefficients for a symmetric matrix
`m=(xx,yy,zz,xy,xz,yz)`. -/
def weight (m : Sym6R) : Fin 6 → ℝ := ![
  (-m 0 - m 1 + 3*m 2 - 4*m 3) / 8,
  (-m 0 - m 1 + 3*m 2 + 4*m 3) / 8,
  (-m 0 + 3*m 1 - m 2 - 4*m 4) / 8,
  (-m 0 + 3*m 1 - m 2 + 4*m 4) / 8,
  (3*m 0 - m 1 - m 2 - 4*m 5) / 8,
  (3*m 0 - m 1 - m 2 + 4*m 5) / 8
]

/-- The explicit weights reconstruct every symmetric matrix exactly. -/
theorem cone_weight_reconstruct (m : Sym6R) :
    coneCoordinates (weight m) = m := by
  funext j
  fin_cases j <;> simp [coneCoordinates, weight] <;> ring

/-- Conversely, extracting weights after synthesis recovers every coefficient.
Thus the six projector stresses are a basis, not merely a spanning family. -/
theorem weight_coneCoordinates (a : Fin 6 → ℝ) :
    weight (coneCoordinates a) = a := by
  funext j
  fin_cases j <;> simp [coneCoordinates, weight] <;> ring

/-- The identity matrix in six-coordinate form. -/
def identityStress : Sym6R := ![1, 1, 1, 0, 0, 0]

/-- The identity has the strictly positive coefficient `1/8` in every frame
direction. -/
theorem weight_identity (i : Fin 6) :
    weight identityStress i = (1 : ℝ) / 8 := by
  fin_cases i <;> norm_num [weight, identityStress]

/-- Coordinate box of radius `epsilon` around the identity. -/
def InIdentityBox (epsilon : ℝ) (m : Sym6R) : Prop :=
  1 - epsilon ≤ m 0 ∧ m 0 ≤ 1 + epsilon ∧
  1 - epsilon ≤ m 1 ∧ m 1 ≤ 1 + epsilon ∧
  1 - epsilon ≤ m 2 ∧ m 2 ≤ 1 + epsilon ∧
  -epsilon ≤ m 3 ∧ m 3 ≤ epsilon ∧
  -epsilon ≤ m 4 ∧ m 4 ≤ epsilon ∧
  -epsilon ≤ m 5 ∧ m 5 ≤ epsilon

/-- Every inverse coefficient stays strictly positive throughout any identity
box of radius `< 1/9`.  The constant follows from the exact worst-case
coefficient budget `1 - 9 epsilon`. -/
theorem weight_pos_of_identity_box
    {epsilon : ℝ} {m : Sym6R}
    (hepsilon : epsilon < (1 : ℝ) / 9)
    (hbox : InIdentityBox epsilon m) :
    ∀ i, 0 < weight m i := by
  rcases hbox with
    ⟨h0lo, h0hi, h1lo, h1hi, h2lo, h2hi,
      h3lo, h3hi, h4lo, h4hi, h5lo, h5hi⟩
  intro i
  fin_cases i <;> simp [weight]
  · have hnum : 0 < -m 0 - m 1 + 3*m 2 - 4*m 3 := by linarith
    positivity
  · have hnum : 0 < -m 0 - m 1 + 3*m 2 + 4*m 3 := by linarith
    positivity
  · have hnum : 0 < -m 0 + 3*m 1 - m 2 - 4*m 4 := by linarith
    positivity
  · have hnum : 0 < -m 0 + 3*m 1 - m 2 + 4*m 4 := by linarith
    positivity
  · have hnum : 0 < 3*m 0 - m 1 - m 2 - 4*m 5 := by linarith
    positivity
  · have hnum : 0 < 3*m 0 - m 1 - m 2 + 4*m 5 := by linarith
    positivity

/-- Exact local positive geometric lemma for the repaired carrier frame. -/
theorem positive_decomposition_of_identity_box
    {epsilon : ℝ} {m : Sym6R}
    (hepsilon : epsilon < (1 : ℝ) / 9)
    (hbox : InIdentityBox epsilon m) :
    (∀ i, 0 < weight m i) ∧ coneCoordinates (weight m) = m := by
  exact ⟨weight_pos_of_identity_box hepsilon hbox,
    cone_weight_reconstruct m⟩

#print axioms carrier_equal_shell
#print axioms distinct_not_equal_or_antipodal
#print axioms qStress_eq_projectorStress
#print axioms isotropic_sum
#print axioms cone_weight_reconstruct
#print axioms weight_coneCoordinates
#print axioms weight_identity
#print axioms weight_pos_of_identity_box
#print axioms positive_decomposition_of_identity_box

end Millennium.NavierStokes.BeltramiSixCarrierFrame
