import Horner3RightData
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

theorem rightPoly3_row_probe : (BiPoly.mul scalarQPoly quotientPoly3).getD 18 []=rightPoly3.getD 18 [] := by
  decide +kernel

#print axioms rightPoly3_row_probe
end StackSorting.RationalLift
