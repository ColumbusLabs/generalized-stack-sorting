import Horner5Base
import Horner5Node166
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p167 : BiPoly.Poly := [[(Int.negSucc 23), (Int.negSucc 35)], [(Int.ofNat 12)]]

theorem h5n167_arithmetic : BiPoly.add h5p92 h5p166=h5p167 := by
  decide +kernel

theorem h5n167 : h5e167.toBi mapPolyEnv=h5p167 := by
  change BiPoly.add (h5e92.toBi mapPolyEnv) (h5e166.toBi mapPolyEnv)=h5p167
  rw [h5n92, h5n166]
  exact h5n167_arithmetic

#print axioms h5n167_arithmetic
end StackSorting.RationalLift
