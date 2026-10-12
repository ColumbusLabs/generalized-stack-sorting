import Horner5Base
import Horner5Node138
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p139 : BiPoly.Poly := [[(Int.ofNat 24), (Int.ofNat 0), (Int.ofNat 24)], [(Int.negSucc 23), (Int.ofNat 24)]]

theorem h5n139_arithmetic : BiPoly.add h5p91 h5p138=h5p139 := by
  decide +kernel

theorem h5n139 : h5e139.toBi mapPolyEnv=h5p139 := by
  change BiPoly.add (h5e91.toBi mapPolyEnv) (h5e138.toBi mapPolyEnv)=h5p139
  rw [h5n91, h5n138]
  exact h5n139_arithmetic

#print axioms h5n139_arithmetic
end StackSorting.RationalLift
