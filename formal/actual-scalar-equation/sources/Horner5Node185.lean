import Horner5Node182
import Horner5Node184
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p185 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 59)], [(Int.ofNat 60)]]

theorem h5n185_arithmetic : BiPoly.add h5p182 h5p184=h5p185 := by
  decide +kernel

theorem h5n185 : h5e185.toBi mapPolyEnv=h5p185 := by
  change BiPoly.add (h5e182.toBi mapPolyEnv) (h5e184.toBi mapPolyEnv)=h5p185
  rw [h5n182, h5n184]
  exact h5n185_arithmetic

#print axioms h5n185_arithmetic
end StackSorting.RationalLift
