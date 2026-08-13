import Millennium.Braid.M1
import Millennium.Braid.M2
import Millennium.Braid.M3
import Millennium.Braid.M4
import Millennium.Braid.M5
import Millennium.Braid.M6

namespace Millennium.Braid

structure FiniteBank where
  lane1 : M1.Certificate
  lane2 : M2.Certificate
  lane3 : M3.Certificate
  lane4 : M4.Certificate
  lane5 : M5.Certificate
  lane6 : M6.Certificate

def finiteBank : FiniteBank where
  lane1 := M1.core
  lane2 := M2.core
  lane3 := M3.core
  lane4 := M4.core
  lane5 := M5.core
  lane6 := M6.core

#print axioms finiteBank

end Millennium.Braid
