import Horner4Base
import Horner4Node147
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p148 : BiPoly.Poly := [[(Int.ofNat 144), (Int.ofNat 288)]]

theorem h4n148_arithmetic : BiPoly.add h4p30 h4p147=h4p148 := by
  decide +kernel

theorem h4n148 : h4e148.toBi mapPolyEnv=h4p148 := by
  change BiPoly.add (h4e30.toBi mapPolyEnv) (h4e147.toBi mapPolyEnv)=h4p148
  rw [h4n30, h4n147]
  exact h4n148_arithmetic

#print axioms h4n148_arithmetic
end StackSorting.RationalLift
