import Mathlib

namespace Millennium
namespace Round217Hodge

def mapQ (a b d : ℚ) (v : ℚ × ℚ) : ℚ × ℚ :=
  (a * v.1 + b * v.2, d * v.2)

def mapQBack (ai b di : ℚ) (v : ℚ × ℚ) : ℚ × ℚ :=
  (ai * v.1 - ai * b * di * v.2, di * v.2)

theorem mapQBack_mapQ
    (a ai b d di x y : ℚ)
    (ha : ai * a = 1)
    (hd : di * d = 1) :
    mapQBack ai b di (mapQ a b d (x, y)) = (x, y) := by
  apply Prod.ext
  · simp [mapQBack, mapQ]
    nlinarith
  · simp [mapQBack, mapQ]
    nlinarith

theorem mapQ_mapQBack
    (a ai b d di x y : ℚ)
    (ha : a * ai = 1)
    (hd : d * di = 1) :
    mapQ a b d (mapQBack ai b di (x, y)) = (x, y) := by
  apply Prod.ext
  · simp [mapQBack, mapQ]
    nlinarith
  · simp [mapQBack, mapQ]
    nlinarith

theorem extension_term_changes_total_map
    (b : ℚ) (hb : b ≠ 0) :
    mapQBack 1 b 1 (0, 1) ≠ (0, 1) := by
  simp [mapQBack, hb]

#print axioms mapQBack_mapQ
#print axioms mapQ_mapQBack
#print axioms extension_term_changes_total_map

end Round217Hodge
end Millennium
