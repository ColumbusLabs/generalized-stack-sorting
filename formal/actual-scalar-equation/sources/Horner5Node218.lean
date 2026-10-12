import Horner5Node037
import Horner5Node217
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p218 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 143), (Int.negSucc 287)], [(Int.ofNat 144)]]

theorem h5n218_arithmetic : BiPoly.add h5p37 h5p217=h5p218 := by
  decide +kernel

theorem h5n218 : h5e218.toBi mapPolyEnv=h5p218 := by
  change BiPoly.add (h5e37.toBi mapPolyEnv) (h5e217.toBi mapPolyEnv)=h5p218
  rw [h5n37, h5n217]
  exact h5n218_arithmetic

#print axioms h5n218_arithmetic
end StackSorting.RationalLift
