import Mathlib

namespace Millennium.YangMills.RootExternalityFirewall

/-- Effective nonroot linear coefficient after eliminating a retained root
which feeds back into the nonroot recursion. -/
def effectiveCoeff (t b c : ℝ) : ℝ := t + b * c

/-- If the retained root is external to the iterated nonroot block, its
feedback coefficient is zero and the nonroot operator coefficient is
unchanged. -/
theorem external_root_preserves_operator (t c : ℝ) :
    effectiveCoeff t 0 c = t := by
  simp [effectiveCoeff]

/-- Algebraic Schur-complement identity for a hidden nonroot → root →
nonroot feedback loop. -/
theorem eliminate_root_feedback
    (x a t b r c d : ℝ)
    (hx : x = a + t * x + b * r)
    (hr : r = c + d * x) :
    x = (a + b * c) + effectiveCoeff t b d * x := by
  rw [hr] at hx
  calc
    x = a + t * x + b * (c + d * x) := hx
    _ = (a + b * c) + (t + b * d) * x := by ring
    _ = (a + b * c) + effectiveCoeff t b d * x := by rfl

/-- A perfect source-free coefficient can be destroyed by hidden root
feedback: `t = 0`, `b = d = 2` produces effective coefficient `4`. -/
theorem hidden_feedback_counterexample :
    effectiveCoeff 0 2 2 = 4 := by
  norm_num [effectiveCoeff]

end Millennium.YangMills.RootExternalityFirewall
