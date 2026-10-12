import Horner5Base
import Horner5Node051
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p52 : BiPoly.Poly := [[(Int.ofNat 144), (Int.ofNat 144)], [(Int.negSucc 143)]]

theorem h5n52_arithmetic : BiPoly.add h5p36 h5p51=h5p52 := by
  decide +kernel

theorem h5n52 : h5e52.toBi mapPolyEnv=h5p52 := by
  change BiPoly.add (h5e36.toBi mapPolyEnv) (h5e51.toBi mapPolyEnv)=h5p52
  rw [h5n36, h5n51]
  exact h5n52_arithmetic

#print axioms h5n52_arithmetic
end StackSorting.RationalLift
