import Horner3Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h3p38 : BiPoly.Poly := [[0,8706816,-9664188,90904872,-48917244,-105715296],[0,-32256464,36644638,-473549634,135326642,288699378,-29365360],[0,47168280,-13402306,893344012,-80551390,-257964480,-15132416],[0,-35069628,-74148088,-763715548,-276429286,-25390242,120027336],[0,14493284,98211592,316578468,522692754,172213548,-77904504],[0,-3409380,-44925366,-81601050,-315486648,-135404604,-37586880],[0,367092,7483950,22107276,70552224,64107504,41239152],[0,0,-200232,-3517452,-3445632,-18941040]]

theorem h3n38_arithmetic : BiPoly.mul h3p3 h3p9=h3p38 := by
  decide +kernel

theorem h3n38 : h3e38.toBi mapPolyEnv=h3p38 := by
  change BiPoly.mul (h3e3.toBi mapPolyEnv) (h3e9.toBi mapPolyEnv)=h3p38
  rw [h3n3, h3n9]
  exact h3n38_arithmetic

#print axioms h3n38_arithmetic
end StackSorting.RationalLift
