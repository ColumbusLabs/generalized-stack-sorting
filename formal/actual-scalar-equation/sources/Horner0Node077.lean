import Horner0Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p77 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 23)]]

theorem h0n77_arithmetic : BiPoly.mul h0p19 h0p12=h0p77 := by
  decide +kernel

theorem h0n77 : h0e77.toBi mapPolyEnv=h0p77 := by
  change BiPoly.mul (h0e19.toBi mapPolyEnv) (h0e12.toBi mapPolyEnv)=h0p77
  rw [h0n19, h0n12]
  exact h0n77_arithmetic

#print axioms h0n77_arithmetic
end StackSorting.RationalLift
