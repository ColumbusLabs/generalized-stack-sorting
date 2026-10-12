import Horner5Node049
import Horner5Node050
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p51 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 144)], [(Int.negSucc 143)]]

theorem h5n51_arithmetic : BiPoly.add h5p49 h5p50=h5p51 := by
  decide +kernel

theorem h5n51 : h5e51.toBi mapPolyEnv=h5p51 := by
  change BiPoly.add (h5e49.toBi mapPolyEnv) (h5e50.toBi mapPolyEnv)=h5p51
  rw [h5n49, h5n50]
  exact h5n51_arithmetic

#print axioms h5n51_arithmetic
end StackSorting.RationalLift
