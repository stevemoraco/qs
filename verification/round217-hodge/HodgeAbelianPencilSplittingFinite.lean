import Mathlib

namespace Millennium
namespace Round217Hodge

def shear (t : ℚ) (v : ℚ × ℚ) : ℚ × ℚ :=
  (v.1 + t * v.2, v.2)

end Round217Hodge
end Millennium
