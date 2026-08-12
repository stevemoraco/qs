import Mathlib

namespace NSTriadHolonomy

variable {G : Type*} [Group G]

/-- Edge transforms induced by one globally assigned frame at each vertex have
trivial ordered holonomy around every triangle. -/
theorem triangle_frame_coboundary_holonomy
    (f0 f1 f2 : G) :
    (f0⁻¹ * f1) * (f1⁻¹ * f2) * (f2⁻¹ * f0) = 1 := by
  group

/-- A nontrivial triangle holonomy is an exact finite obstruction to realizing
three interaction-wise transforms by one shared frame at each mode. -/
theorem nontrivial_triangle_holonomy_blocks_global_frames
    (g01 g12 g20 : G)
    (hhol : g01 * g12 * g20 ≠ 1) :
    ¬ ∃ f0 f1 f2 : G,
        g01 = f0⁻¹ * f1 ∧
        g12 = f1⁻¹ * f2 ∧
        g20 = f2⁻¹ * f0 := by
  rintro ⟨f0, f1, f2, h01, h12, h20⟩
  apply hhol
  calc
    g01 * g12 * g20 =
        (f0⁻¹ * f1) * (f1⁻¹ * f2) * (f2⁻¹ * f0) := by
          rw [h01, h12, h20]
    _ = 1 := triangle_frame_coboundary_holonomy f0 f1 f2

/-- The obstruction is genuinely cyclic: every two-edge chain can be realized
by global vertex frames.  Thus a single cascade chain is an exact escape from
holonomy arguments. -/
theorem two_edge_chain_always_realizable
    (g01 g12 : G) :
    ∃ f0 f1 f2 : G,
      g01 = f0⁻¹ * f1 ∧
      g12 = f1⁻¹ * f2 := by
  refine ⟨1, g01, g01 * g12, ?_, ?_⟩
  · simp
  · simp

/-- Under an arbitrary change of vertex frames, triangle holonomy changes only
by conjugation at the base vertex.  Hence the conjugacy class of the cycle
product is the gauge-invariant finite datum. -/
theorem triangle_holonomy_gauge_conjugates
    (h0 h1 h2 g01 g12 g20 : G) :
    (h0⁻¹ * g01 * h1) * (h1⁻¹ * g12 * h2) * (h2⁻¹ * g20 * h0)
      = h0⁻¹ * (g01 * g12 * g20) * h0 := by
  group

/-- Additive version of the triangle coboundary identity. -/
theorem additive_triangle_frame_coboundary_holonomy
    {A : Type*} [AddCommGroup A]
    (f0 f1 f2 : A) :
    (f1 - f0) + (f2 - f1) + (f0 - f2) = 0 := by
  abel

/-- Three quarter-turn labels in `ZMod 4` are each locally admissible, but their
cycle sum is nonzero, so no globally shared mode frames can realize all three.
This is the smallest explicit finite holonomy countermodel. -/
theorem three_quarter_turns_block_zmod4_vertex_frames :
    ¬ ∃ f0 f1 f2 : ZMod 4,
        f1 - f0 = 1 ∧
        f2 - f1 = 1 ∧
        f0 - f2 = 1 := by
  rintro ⟨f0, f1, f2, h01, h12, h20⟩
  have hzero := additive_triangle_frame_coboundary_holonomy f0 f1 f2
  rw [h01, h12, h20] at hzero
  norm_num at hzero
  have hne : (3 : ZMod 4) ≠ 0 := by decide
  exact hne hzero

#print axioms triangle_frame_coboundary_holonomy
#print axioms nontrivial_triangle_holonomy_blocks_global_frames
#print axioms two_edge_chain_always_realizable
#print axioms triangle_holonomy_gauge_conjugates
#print axioms additive_triangle_frame_coboundary_holonomy
#print axioms three_quarter_turns_block_zmod4_vertex_frames

end NSTriadHolonomy
