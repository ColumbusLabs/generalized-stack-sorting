import Horner0Base
import Horner0Node086
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p87 : BiPoly.Poly := [[(Int.ofNat 24), (Int.ofNat 48)]]

theorem h0n87_arithmetic : BiPoly.add h0p85 h0p86=h0p87 := by
  decide +kernel

theorem h0n87 : h0e87.toBi mapPolyEnv=h0p87 := by
  change BiPoly.add (h0e85.toBi mapPolyEnv) (h0e86.toBi mapPolyEnv)=h0p87
  rw [h0n85, h0n86]
  exact h0n87_arithmetic

#print axioms h0n87_arithmetic
end StackSorting.RationalLift
