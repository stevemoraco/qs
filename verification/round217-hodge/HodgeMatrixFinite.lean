import Mathlib

namespace Millennium
namespace Round217Hodge

def mapQ (a b d : ℚ) (v : ℚ × ℚ) : ℚ × ℚ :=
  (a * v.1 + b * v.2, d * v.2)

end Round217Hodge
end Millennium
