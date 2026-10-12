import Horner5Node225
import Horner5Node226
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p227 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 215)], [(Int.ofNat 216)]]

theorem h5n227_arithmetic : BiPoly.add h5p225 h5p226=h5p227 := by
  decide +kernel

theorem h5n227 : h5e227.toBi mapPolyEnv=h5p227 := by
  change BiPoly.add (h5e225.toBi mapPolyEnv) (h5e226.toBi mapPolyEnv)=h5p227
  rw [h5n225, h5n226]
  exact h5n227_arithmetic

#print axioms h5n227_arithmetic
end StackSorting.RationalLift
