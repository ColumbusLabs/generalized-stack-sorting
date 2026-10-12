import Horner4Node119
import Horner4Node120
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p121 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 6452135999), (Int.negSucc 47593216439), (Int.negSucc 49917239279), (Int.ofNat 147009227400)], [(Int.ofNat 0), (Int.ofNat 28073960640), (Int.ofNat 215020267128), (Int.ofNat 301700236752), (Int.negSucc 634515746183), (Int.ofNat 40257724320)], [(Int.ofNat 0), (Int.negSucc 49588249679), (Int.negSucc 451570983455), (Int.negSucc 608603367479), (Int.ofNat 980314067400), (Int.negSucc 5938040231), (Int.negSucc 204309599)], [(Int.ofNat 0), (Int.ofNat 45408699360), (Int.ofNat 575824874340), (Int.ofNat 498889236372), (Int.negSucc 304243567211), (Int.negSucc 238152994499), (Int.ofNat 7413436080)], [(Int.ofNat 0), (Int.negSucc 22709925599), (Int.negSucc 470305655627), (Int.negSucc 151382845439), (Int.negSucc 659589815195), (Int.ofNat 355366015296), (Int.ofNat 12417139320)], [(Int.ofNat 0), (Int.ofNat 5889764640), (Int.ofNat 238779665292), (Int.ofNat 57767854080), (Int.ofNat 643308523668), (Int.negSucc 47898069227), (Int.negSucc 22642929899)], [(Int.ofNat 0), (Int.negSucc 622113359), (Int.negSucc 69797824667), (Int.negSucc 95602313411), (Int.negSucc 182943245927), (Int.negSucc 160410786131), (Int.negSucc 5459416199)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 10104277512), (Int.ofNat 62792185380), (Int.ofNat 5066326836), (Int.ofNat 83787666192), (Int.ofNat 14983538760)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 461404079), (Int.negSucc 18076074011), (Int.ofNat 5732735976), (Int.negSucc 13127620031), (Int.negSucc 4283383679)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2207697120), (Int.negSucc 1331325287), (Int.ofNat 874717920)]]

theorem h4n121_arithmetic : BiPoly.add h4p119 h4p120=h4p121 := by
  decide +kernel

theorem h4n121 : h4e121.toBi mapPolyEnv=h4p121 := by
  change BiPoly.add (h4e119.toBi mapPolyEnv) (h4e120.toBi mapPolyEnv)=h4p121
  rw [h4n119, h4n120]
  exact h4n121_arithmetic

#print axioms h4n121_arithmetic
end StackSorting.RationalLift
