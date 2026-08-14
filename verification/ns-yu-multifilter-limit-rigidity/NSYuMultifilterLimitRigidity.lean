import Mathlib

/-!
# Yu multifilter limit-line rigidity firewall

Finite topology, real algebra, and an exact geometric counterexample only.

The positive statements formalize the post-profile unfiltering step: pairwise
line geometry is closed under componentwise limits, even when the approximating
lines vary with the filter index.  A nonzero anchor then identifies one common
line for the whole limiting field.

The negative statement records that Yu's exact angular kernel can vanish while
the pairwise direction defect is strictly positive.  Therefore the one-sided
estimate from positive near-field stretching to the pairwise defect cannot be
reversed without additional hypotheses.

These declarations do **not** formalize Navier--Stokes, Yu's PDE estimates,
ancient-profile extraction, mollifier convergence, Giga--Miura's theorem, or
regularity.
-/

open Filter
open scoped Topology

namespace NSYuMultifilterLimitRigidity

/-- A coordinate minor detecting whether two three-vectors share a line. -/
def minor3 (a b : Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  a i * b j - a j * b i

/-- If the components converge and every coordinate minor tends to zero, then
the corresponding minor of the limiting field is exactly zero. -/
theorem vanishing_minor_limit_forces_limit_minor
    {ι : Type*}
    (f : ℕ → ι → Fin 3 → ℝ)
    (g : ι → Fin 3 → ℝ)
    (hconv : ∀ x i, Tendsto (fun n => f n x i) atTop (𝓝 (g x i)))
    (hminor : ∀ x y i j,
      Tendsto (fun n => minor3 (f n x) (f n y) i j)
        atTop (𝓝 0)) :
    ∀ x y i j, minor3 (g x) (g y) i j = 0 := by
  intro x y i j
  have hlim :
      Tendsto (fun n => minor3 (f n x) (f n y) i j)
        atTop (𝓝 (minor3 (g x) (g y) i j)) := by
    simpa only [minor3] using
      ((hconv x i).mul (hconv y j)).sub ((hconv x j).mul (hconv y i))
  exact tendsto_nhds_unique hlim (hminor x y i j)

/-- Exact pairwise line geometry at every filter index survives any
componentwise pointwise limit.  No convergence of the lines themselves is
assumed. -/
theorem exact_lines_closed_under_pointwise_limit
    {ι : Type*}
    (f : ℕ → ι → Fin 3 → ℝ)
    (g : ι → Fin 3 → ℝ)
    (hconv : ∀ x i, Tendsto (fun n => f n x i) atTop (𝓝 (g x i)))
    (hline : ∀ n x y i j, minor3 (f n x) (f n y) i j = 0) :
    ∀ x y i j, minor3 (g x) (g y) i j = 0 := by
  apply vanishing_minor_limit_forces_limit_minor f g hconv
  intro x y i j
  have hfun :
      (fun n => minor3 (f n x) (f n y) i j) =
        fun _ : ℕ => (0 : ℝ) := by
    funext n
    exact hline n x y i j
  rw [hfun]
  exact tendsto_const_nhds

/-- If all minors against one nonzero anchor vanish, every vector in the field
is an explicit scalar multiple of that anchor. -/
theorem anchor_minor_zero_forces_common_line
    {ι : Type*}
    (g : ι → Fin 3 → ℝ)
    (a : ι) (k : Fin 3)
    (hak : g a k ≠ 0)
    (hminor : ∀ x i j, minor3 (g a) (g x) i j = 0) :
    ∀ x, ∃ c : ℝ, ∀ i, g x i = c * g a i := by
  intro x
  refine ⟨g x k / g a k, ?_⟩
  intro i
  have h := hminor x k i
  simp only [minor3] at h
  field_simp [hak]
  nlinarith [h]

/-- Combined post-filter theorem: componentwise limits of line-valued fields
are line-valued, and any nonzero limiting anchor fixes a common line. -/
theorem pointwise_limit_has_anchor_line
    {ι : Type*}
    (f : ℕ → ι → Fin 3 → ℝ)
    (g : ι → Fin 3 → ℝ)
    (hconv : ∀ x i, Tendsto (fun n => f n x i) atTop (𝓝 (g x i)))
    (hline : ∀ n x y i j, minor3 (f n x) (f n y) i j = 0)
    (a : ι) (k : Fin 3) (hak : g a k ≠ 0) :
    ∀ x, ∃ c : ℝ, ∀ i, g x i = c * g a i := by
  apply anchor_minor_zero_forces_common_line g a k hak
  intro x i j
  exact exact_lines_closed_under_pointwise_limit f g hconv hline a x i j

structure Vec3 where
  x : ℝ
  y : ℝ
  z : ℝ

/-- Euclidean dot product in explicit coordinates. -/
def dot (a b : Vec3) : ℝ :=
  a.x * b.x + a.y * b.y + a.z * b.z

/-- Three-dimensional cross product in explicit coordinates. -/
def cross (a b : Vec3) : Vec3 :=
  ⟨a.y * b.z - a.z * b.y,
   a.z * b.x - a.x * b.z,
   a.x * b.y - a.y * b.x⟩

/-- Vector subtraction in explicit coordinates. -/
def vsub (a b : Vec3) : Vec3 :=
  ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩

/-- Squared Euclidean norm. -/
def normSq (a : Vec3) : ℝ := dot a a

/-- The angular scalar appearing in Yu's exact direction contraction, with
`zeta` representing the displacement direction. -/
def yuAngularFactor (xi zeta eta : Vec3) : ℝ :=
  dot xi zeta * dot (cross xi zeta) (vsub eta xi)

/-- Exact kernel-blindness witness.  The neighbor direction differs by squared
amount two and the second angular factor is nonzero, yet the full contraction
vanishes because the displacement is orthogonal to the local direction. -/
theorem positive_direction_defect_can_be_kernel_invisible :
    let xi : Vec3 := ⟨1, 0, 0⟩
    let zeta : Vec3 := ⟨0, 1, 0⟩
    let eta : Vec3 := ⟨0, 0, 1⟩
    dot xi zeta = 0 ∧
      dot (cross xi zeta) (vsub eta xi) = 1 ∧
      yuAngularFactor xi zeta eta = 0 ∧
      normSq (vsub eta xi) = 2 := by
  norm_num [dot, cross, vsub, yuAngularFactor, normSq]

/-- The valid one-sided charging consequence.  If a positive defect is bounded
above by two budget channels, at least one channel pays half the defect. -/
theorem positive_defect_forces_budget_branch
    {delta defect channel₁ channel₂ : ℝ}
    (hlow : delta ≤ defect)
    (hup : defect ≤ channel₁ + channel₂) :
    delta / 2 ≤ channel₁ ∨ delta / 2 ≤ channel₂ := by
  by_contra h
  have h₁ : channel₁ < delta / 2 :=
    lt_of_not_ge (fun h₁ => h (Or.inl h₁))
  have h₂ : channel₂ < delta / 2 :=
    lt_of_not_ge (fun h₂ => h (Or.inr h₂))
  linarith

#print axioms vanishing_minor_limit_forces_limit_minor
#print axioms exact_lines_closed_under_pointwise_limit
#print axioms anchor_minor_zero_forces_common_line
#print axioms pointwise_limit_has_anchor_line
#print axioms positive_direction_defect_can_be_kernel_invisible
#print axioms positive_defect_forces_budget_branch

end NSYuMultifilterLimitRigidity
