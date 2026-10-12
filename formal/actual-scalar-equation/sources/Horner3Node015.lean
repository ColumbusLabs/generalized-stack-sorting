import Horner3Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h3p15 : BiPoly.Poly := [[0,-2353392,-15067542,110200308,-13450326,-52857648],[0,8955200,45090875,-428781429,124214965,81932205,-14682680],[0,-12632580,-43955705,613384190,-118328303,14400648,-25943080],[0,7533714,7834996,-385089686,-201090179,-9267693,32794536],[0,-1039982,12842468,88631730,351530481,-22108722,11649564],[0,-646506,-8477943,2455167,-165359808,-40716774,-11807352],[0,183546,1832967,140238,18827064,44370288,1086264],[0,0,-100116,-918918,1939680,-9470520]]

theorem h3n15_arithmetic : BiPoly.mul h3p2 h3p9=h3p15 := by
  decide +kernel

theorem h3n15 : h3e15.toBi mapPolyEnv=h3p15 := by
  change BiPoly.mul (h3e2.toBi mapPolyEnv) (h3e9.toBi mapPolyEnv)=h3p15
  rw [h3n2, h3n9]
  exact h3n15_arithmetic

#print axioms h3n15_arithmetic
end StackSorting.RationalLift
