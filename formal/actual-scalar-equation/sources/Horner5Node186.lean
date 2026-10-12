import Horner5Base
import Horner5Node185
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p186 : BiPoly.Poly := [[(Int.negSucc 59), (Int.negSucc 59)], [(Int.ofNat 60)]]

theorem h5n186_arithmetic : BiPoly.add h5p181 h5p185=h5p186 := by
  decide +kernel

theorem h5n186 : h5e186.toBi mapPolyEnv=h5p186 := by
  change BiPoly.add (h5e181.toBi mapPolyEnv) (h5e185.toBi mapPolyEnv)=h5p186
  rw [h5n181, h5n185]
  exact h5n186_arithmetic

#print axioms h5n186_arithmetic
end StackSorting.RationalLift
