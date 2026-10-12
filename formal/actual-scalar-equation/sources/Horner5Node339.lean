import Horner5Base
import Horner5Node338
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p339 : BiPoly.Poly := [[(Int.ofNat 60), (Int.ofNat 60)], [(Int.negSucc 59)]]

theorem h5n339_arithmetic : BiPoly.add h5p183 h5p338=h5p339 := by
  decide +kernel

theorem h5n339 : h5e339.toBi mapPolyEnv=h5p339 := by
  change BiPoly.add (h5e183.toBi mapPolyEnv) (h5e338.toBi mapPolyEnv)=h5p339
  rw [h5n183, h5n338]
  exact h5n339_arithmetic

#print axioms h5n339_arithmetic
end StackSorting.RationalLift
