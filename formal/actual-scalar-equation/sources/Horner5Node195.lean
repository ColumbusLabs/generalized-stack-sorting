import Horner5Base
import Horner5Node194
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p195 : BiPoly.Poly := [[(Int.ofNat 48), (Int.ofNat 48)], [(Int.negSucc 47)]]

theorem h5n195_arithmetic : BiPoly.add h5p191 h5p194=h5p195 := by
  decide +kernel

theorem h5n195 : h5e195.toBi mapPolyEnv=h5p195 := by
  change BiPoly.add (h5e191.toBi mapPolyEnv) (h5e194.toBi mapPolyEnv)=h5p195
  rw [h5n191, h5n194]
  exact h5n195_arithmetic

#print axioms h5n195_arithmetic
end StackSorting.RationalLift
