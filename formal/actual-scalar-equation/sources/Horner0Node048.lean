import Horner0Base
import Horner0Node047
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p48 : BiPoly.Poly := [[(Int.ofNat 6), (Int.ofNat 12)]]

theorem h0n48_arithmetic : BiPoly.add h0p45 h0p47=h0p48 := by
  decide +kernel

theorem h0n48 : h0e48.toBi mapPolyEnv=h0p48 := by
  change BiPoly.add (h0e45.toBi mapPolyEnv) (h0e47.toBi mapPolyEnv)=h0p48
  rw [h0n45, h0n47]
  exact h0n48_arithmetic

#print axioms h0n48_arithmetic
end StackSorting.RationalLift
