import Mathlib

namespace RHOneSidedPoissonCoercivity

/-- A real sequence has one uniform upper barrier. -/
def UniformUpperBound (a : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, a n ≤ C

/-- A real sequence has one uniform lower barrier. -/
def UniformLowerBound (a : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, C ≤ a n

/-- A real sequence is uniformly bounded in absolute value. -/
def UniformlyBounded (a : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, |a n| ≤ C

/-- Scalar coercivity step: a lower energy bound and nonnegative discrepancy
terms force an upper bound on the critical primitive. -/
theorem scalar_energy_lower_implies_primitive_upper
    {G I Q R C : ℝ}
    (hdecomp : G = (1 / 2 : ℝ) - I - Q - R)
    (hQ : 0 ≤ Q)
    (hR : 0 ≤ R)
    (hG : -C ≤ G) :
    I ≤ C + (1 / 2 : ℝ) := by
  linarith

/-- Sequence version of the one-sided coercivity step. -/
theorem energy_lower_implies_primitive_upper
    {G I Q R : ℕ → ℝ}
    (hdecomp : ∀ n, G n = (1 / 2 : ℝ) - I n - Q n - R n)
    (hQ : ∀ n, 0 ≤ Q n)
    (hR : ∀ n, 0 ≤ R n)
    (hG : UniformLowerBound G) :
    UniformUpperBound I := by
  rcases hG with ⟨C, hC⟩
  refine ⟨(1 / 2 : ℝ) - C, ?_⟩
  intro n
  have hd := hdecomp n
  have hq := hQ n
  have hr := hR n
  have hg := hC n
  linarith

/-- A uniformly bounded additive correction preserves lower boundedness after
subtracting the deterministic baseline. -/
theorem lower_bound_iff_bounded_correction
    {W G L d : ℕ → ℝ}
    (hdecomp : ∀ n, W n - L n = G n + d n)
    (hd : UniformlyBounded d) :
    UniformLowerBound (fun n => W n - L n) ↔ UniformLowerBound G := by
  rcases hd with ⟨B, hB⟩
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C - B, ?_⟩
    intro n
    have habs := abs_le.mp (hB n)
    have hcenter := hC n
    have heq := hdecomp n
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨C - B, ?_⟩
    intro n
    have habs := abs_le.mp (hB n)
    have henergy := hC n
    have heq := hdecomp n
    linarith

/-- Pure logical transfer shell: if the target problem implies a lower energy
barrier and an upper primitive barrier implies the target problem, then the
nonnegative discrepancy decomposition makes the lower energy barrier exactly
equivalent to the target. -/
theorem equivalent_problem_energy_lower
    {P : Prop} {G I Q R : ℕ → ℝ}
    (hdecomp : ∀ n, G n = (1 / 2 : ℝ) - I n - Q n - R n)
    (hQ : ∀ n, 0 ≤ Q n)
    (hR : ∀ n, 0 ≤ R n)
    (hforward : P → UniformLowerBound G)
    (hreverse : UniformUpperBound I → P) :
    P ↔ UniformLowerBound G := by
  constructor
  · exact hforward
  · intro hG
    exact hreverse
      (energy_lower_implies_primitive_upper hdecomp hQ hR hG)

/-- The lower energy inequality is exactly the corresponding one-sided norm
inequality. -/
theorem lower_energy_iff_norm_inequality
    {G V N C : ℝ}
    (hdecomp : G = V - N / 2) :
    -C ≤ G ↔ N / 2 ≤ V + C := by
  constructor <;> intro h <;> linarith

/-- Finite baseline-correction version used by a renormalized Euler-product
energy. -/
theorem finite_lower_bound_transfer
    {W G L d C B : ℝ}
    (hdecomp : W - L = G + d)
    (hd : |d| ≤ B)
    (hG : -C ≤ G) :
    -(C + B) ≤ W - L := by
  have habs := abs_le.mp hd
  linarith

#print axioms scalar_energy_lower_implies_primitive_upper
#print axioms energy_lower_implies_primitive_upper
#print axioms lower_bound_iff_bounded_correction
#print axioms equivalent_problem_energy_lower
#print axioms lower_energy_iff_norm_inequality
#print axioms finite_lower_bound_transfer

end RHOneSidedPoissonCoercivity
