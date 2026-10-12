import Horner5Node037
import Horner5Node041
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p42 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 144)], [(Int.ofNat 144), (Int.negSucc 287)]]

theorem h5n42_arithmetic : BiPoly.add h5p37 h5p41=h5p42 := by
  decide +kernel

theorem h5n42 : h5e42.toBi mapPolyEnv=h5p42 := by
  change BiPoly.add (h5e37.toBi mapPolyEnv) (h5e41.toBi mapPolyEnv)=h5p42
  rw [h5n37, h5n41]
  exact h5n42_arithmetic

#print axioms h5n42_arithmetic
end StackSorting.RationalLift
