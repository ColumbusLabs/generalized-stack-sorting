import Horner4Base
import Horner4Node039
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p40 : BiPoly.Poly := [[(Int.negSucc 95), (Int.ofNat 96)]]

theorem h4n40_arithmetic : BiPoly.add h4p15 h4p39=h4p40 := by
  decide +kernel

theorem h4n40 : h4e40.toBi mapPolyEnv=h4p40 := by
  change BiPoly.add (h4e15.toBi mapPolyEnv) (h4e39.toBi mapPolyEnv)=h4p40
  rw [h4n15, h4n39]
  exact h4n40_arithmetic

#print axioms h4n40_arithmetic
end StackSorting.RationalLift
