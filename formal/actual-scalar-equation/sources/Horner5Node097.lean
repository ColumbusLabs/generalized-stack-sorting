import Horner5Node095
import Horner5Node096
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p97 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 23)], [(Int.ofNat 72)]]

theorem h5n97_arithmetic : BiPoly.add h5p95 h5p96=h5p97 := by
  decide +kernel

theorem h5n97 : h5e97.toBi mapPolyEnv=h5p97 := by
  change BiPoly.add (h5e95.toBi mapPolyEnv) (h5e96.toBi mapPolyEnv)=h5p97
  rw [h5n95, h5n96]
  exact h5n97_arithmetic

#print axioms h5n97_arithmetic
end StackSorting.RationalLift
