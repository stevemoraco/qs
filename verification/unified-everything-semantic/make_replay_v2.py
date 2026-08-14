#!/usr/bin/env python3
from pathlib import Path

root = Path(__file__).resolve().parent
src = root / "UnifiedEverythingSemanticReplay.lean"
out_v2 = root / "UnifiedEverythingSemanticReplayV2.lean"
out_v3 = root / "UnifiedEverythingSemanticReplayV3.lean"
out_v4 = root / "UnifiedEverythingSemanticReplayV4.lean"
text = src.read_text(encoding="utf-8")

# Failed-first repair 1: use the unscoped topology name accepted by the pinned toolchain.
text = text.replace("𝓝", "nhds")

# Failed-first repair 2: expose all four universe parameters inherited from GiantReceipt.
marker = "structure UnifiedEverythingReceipt (T : Targets) : Prop where"
if text.count(marker) != 1:
    raise SystemExit(f"expected exactly one receipt marker, found {text.count(marker)}")
text = text.replace(
    marker,
    "universe u₁ u₂ u₃ u₄\n\n"
    "structure UnifiedEverythingReceipt (T : Targets) : Prop where",
)

old_field = "  semanticBank : GiantReceipt T"
new_field = "  semanticBank : GiantReceipt.{u₁, u₂, u₃, u₄} T"
if text.count(old_field) != 1:
    raise SystemExit(f"expected exactly one semantic field marker, found {text.count(old_field)}")
text = text.replace(old_field, new_field)

old_result = (
    "theorem everything_one_gigantic_runnable_statement (T : Targets) :\n"
    "    UnifiedEverythingReceipt T := by"
)
new_result = (
    "theorem everything_one_gigantic_runnable_statement (T : Targets) :\n"
    "    UnifiedEverythingReceipt.{u₁, u₂, u₃, u₄} T := by"
)
if text.count(old_result) != 1:
    raise SystemExit(f"expected exactly one theorem-result marker, found {text.count(old_result)}")
text = text.replace(old_result, new_result)
out_v2.write_text(text, encoding="utf-8")

# Failed-first repair 3: uniqueness of limits needs a Hausdorff target.
# The two occurrences are the native theorem block and the GiantReceipt field.
if text.count("[PseudoMetricSpace Y]") != 2:
    raise SystemExit(
        "expected exactly two pseudometric target markers, found "
        f"{text.count('[PseudoMetricSpace Y]')}"
    )
text = text.replace(
    "[PseudoMetricSpace Y]",
    "[PseudoMetricSpace Y] [T2Space Y]",
)
old_intro = "  · intro X Y instX instComplete instY u d hstep hsum F hF y hres"
new_intro = "  · intro X Y instX instComplete instY instT2 u d hstep hsum F hF y hres"
if text.count(old_intro) != 1:
    raise SystemExit(f"expected exactly one equation intro marker, found {text.count(old_intro)}")
text = text.replace(old_intro, new_intro)
out_v3.write_text(text, encoding="utf-8")

# Additive V4: retain a positive continuous observable at the exact limit.
text_v4 = text
boundary = "end Millennium.CrossProblem\n\nnamespace Millennium.Unified700PlusBraid"
if text_v4.count(boundary) != 1:
    raise SystemExit(f"expected exactly one cross-problem boundary, found {text_v4.count(boundary)}")
nontrivial_theorems = r'''
/-- Exact equation passage while retaining a closed lower margin for a
continuous real-valued observable. -/
theorem summable_steps_exact_equation_with_margin
    (u : ℕ → X) (d : ℕ → ℝ)
    (hstep : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ d n)
    (hsum : Summable d)
    (F : X → Y) (hF : Continuous F) (y : Y)
    (hres : Tendsto (fun n => F (u n)) atTop (nhds y))
    (G : X → ℝ) (hG : Continuous G) (margin : ℝ)
    (hmargin : ∀ n : ℕ, margin ≤ G (u n)) :
    ∃ x : X,
      Tendsto u atTop (nhds x) ∧
      F x = y ∧
      margin ≤ G x := by
  obtain ⟨x, hx, hEq⟩ :=
    summable_steps_exact_equation u d hstep hsum F hF y hres
  refine ⟨x, hx, hEq, ?_⟩
  have hGx : Tendsto (fun n => G (u n)) atTop (nhds (G x)) :=
    hG.continuousAt.tendsto.comp hx
  exact isClosed_Ici.mem_of_tendsto hGx (Eventually.of_forall hmargin)

/-- A strictly positive retained observable proves that the limiting exact
solution is nontrivial with respect to that observable. -/
theorem summable_steps_exact_equation_nontrivial
    (u : ℕ → X) (d : ℕ → ℝ)
    (hstep : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ d n)
    (hsum : Summable d)
    (F : X → Y) (hF : Continuous F) (y : Y)
    (hres : Tendsto (fun n => F (u n)) atTop (nhds y))
    (G : X → ℝ) (hG : Continuous G) (margin : ℝ)
    (hmarginPos : 0 < margin)
    (hmargin : ∀ n : ℕ, margin ≤ G (u n)) :
    ∃ x : X,
      Tendsto u atTop (nhds x) ∧
      F x = y ∧
      G x ≠ 0 := by
  obtain ⟨x, hx, hEq, hLower⟩ :=
    summable_steps_exact_equation_with_margin
      u d hstep hsum F hF y hres G hG margin hmargin
  refine ⟨x, hx, hEq, ?_⟩
  exact ne_of_gt (lt_of_lt_of_le hmarginPos hLower)

#print axioms summable_steps_exact_equation_with_margin
#print axioms summable_steps_exact_equation_nontrivial

'''
text_v4 = text_v4.replace(
    boundary,
    nontrivial_theorems + boundary,
)

v2_capstone = r'''

namespace Millennium.UnifiedEverythingOneStatementV2

open Filter
open Millennium.Unified700PlusBraid
open Millennium.UnifiedEverythingOneStatement

universe v₁ v₂ v₃ v₄ v₅ v₆

structure UnifiedEverythingReceiptV2 (T : Targets) : Prop where
  base : UnifiedEverythingReceipt.{v₁, v₂, v₃, v₄} T
  nontrivialExactLimitAvailable :
    ∀ {X : Type v₅} {Y : Type v₆}
      [PseudoMetricSpace X] [CompleteSpace X]
      [PseudoMetricSpace Y] [T2Space Y]
      (u : ℕ → X) (d : ℕ → ℝ),
      (∀ n : ℕ, dist (u n) (u (n + 1)) ≤ d n) →
      Summable d →
      ∀ (F : X → Y), Continuous F → ∀ y : Y,
      Tendsto (fun n => F (u n)) atTop (nhds y) →
      ∀ (G : X → ℝ), Continuous G → ∀ margin : ℝ,
      0 < margin →
      (∀ n : ℕ, margin ≤ G (u n)) →
      ∃ x : X,
        Tendsto u atTop (nhds x) ∧
        F x = y ∧
        G x ≠ 0

theorem everything_one_gigantic_runnable_statement_v2 (T : Targets) :
    UnifiedEverythingReceiptV2.{v₁, v₂, v₃, v₄, v₅, v₆} T := by
  refine ⟨everything_one_gigantic_runnable_statement T, ?_⟩
  intro X Y instX instComplete instY instT2
    u d hstep hsum F hF y hres G hG margin hmarginPos hmargin
  exact Millennium.CrossProblem.summable_steps_exact_equation_nontrivial
    u d hstep hsum F hF y hres G hG margin hmarginPos hmargin

#print axioms everything_one_gigantic_runnable_statement_v2

end Millennium.UnifiedEverythingOneStatementV2
'''
text_v4 += v2_capstone
out_v4.write_text(text_v4, encoding="utf-8")

print(out_v2)
print(out_v3)
print(out_v4)
