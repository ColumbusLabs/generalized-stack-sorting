import Horner5Node039
import Horner5Node062
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p63 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 96)], [(Int.negSucc 287)]]

theorem h5n63_arithmetic : BiPoly.add h5p39 h5p62=h5p63 := by
  decide +kernel

theorem h5n63 : h5e63.toBi mapPolyEnv=h5p63 := by
  change BiPoly.add (h5e39.toBi mapPolyEnv) (h5e62.toBi mapPolyEnv)=h5p63
  rw [h5n39, h5n62]
  exact h5n63_arithmetic

#print axioms h5n63_arithmetic
end StackSorting.RationalLift
