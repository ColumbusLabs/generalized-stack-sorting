import Horner5Node192
import Horner5Node193
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p194 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 48)], [(Int.negSucc 47)]]

theorem h5n194_arithmetic : BiPoly.add h5p192 h5p193=h5p194 := by
  decide +kernel

theorem h5n194 : h5e194.toBi mapPolyEnv=h5p194 := by
  change BiPoly.add (h5e192.toBi mapPolyEnv) (h5e193.toBi mapPolyEnv)=h5p194
  rw [h5n192, h5n193]
  exact h5n194_arithmetic

#print axioms h5n194_arithmetic
end StackSorting.RationalLift
