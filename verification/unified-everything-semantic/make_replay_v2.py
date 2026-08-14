#!/usr/bin/env python3
from pathlib import Path

root = Path(__file__).resolve().parent
src = root / "UnifiedEverythingSemanticReplay.lean"
out_v2 = root / "UnifiedEverythingSemanticReplayV2.lean"
out_v3 = root / "UnifiedEverythingSemanticReplayV3.lean"
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

print(out_v2)
print(out_v3)
