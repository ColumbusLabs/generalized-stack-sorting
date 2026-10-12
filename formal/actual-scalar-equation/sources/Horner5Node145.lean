import Horner5Node010
import Horner5Node062
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p145 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 96)], [(Int.negSucc 95)]]

theorem h5n145_arithmetic : BiPoly.add h5p10 h5p62=h5p145 := by
  decide +kernel

theorem h5n145 : h5e145.toBi mapPolyEnv=h5p145 := by
  change BiPoly.add (h5e10.toBi mapPolyEnv) (h5e62.toBi mapPolyEnv)=h5p145
  rw [h5n10, h5n62]
  exact h5n145_arithmetic

#print axioms h5n145_arithmetic
end StackSorting.RationalLift
