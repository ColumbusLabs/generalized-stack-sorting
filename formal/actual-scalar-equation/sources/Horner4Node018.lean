import Horner4Base
import Horner4Node017
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p18 : BiPoly.Poly := [[(Int.ofNat 45337088448), (Int.ofNat 71496416448), (Int.negSucc 352048268735), (Int.ofNat 235214763840)], [(Int.negSucc 221402948543), (Int.negSucc 422142572735), (Int.ofNat 1675425571776), (Int.negSucc 1096292409407), (Int.ofNat 64412358912)], [(Int.ofNat 510724892352), (Int.ofNat 669403516800), (Int.negSucc 2754841000511), (Int.ofNat 1585982133312), (Int.negSucc 10942646591), (Int.negSucc 326895359)], [(Int.negSucc 712259319071), (Int.negSucc 91982703359), (Int.ofNat 1191701363328), (Int.negSucc 28918079), (Int.negSucc 399291920543), (Int.ofNat 11861497728)], [(Int.ofNat 625727177568), (Int.negSucc 587093521055), (Int.ofNat 1145962688736), (Int.negSucc 1758729347423), (Int.ofNat 554265579264), (Int.ofNat 19867422912)], [(Int.negSucc 336461002079), (Int.ofNat 431236826976), (Int.negSucc 1125769009439), (Int.ofNat 1087006052352), (Int.negSucc 19784179967), (Int.negSucc 36228687839)], [(Int.ofNat 103194307872), (Int.negSucc 20802348479), (Int.ofNat 136677055200), (Int.ofNat 54538937568), (Int.negSucc 264872886239), (Int.negSucc 8735065919)], [(Int.negSucc 15598443071), (Int.negSucc 74278999775), (Int.ofNat 121946182656), (Int.negSucc 160537164767), (Int.ofNat 104494762944), (Int.ofNat 23973662016)], [(Int.ofNat 738246528), (Int.ofNat 27940403808), (Int.negSucc 44521248671), (Int.ofNat 29729193408), (Int.negSucc 7033181183), (Int.negSucc 6853413887)], [(Int.ofNat 0), (Int.negSucc 3532315391), (Int.ofNat 5746171968), (Int.negSucc 2213856575)]]

theorem h4n18_arithmetic : BiPoly.mul h4p7 h4p17=h4p18 := by
  decide +kernel

theorem h4n18 : h4e18.toBi mapPolyEnv=h4p18 := by
  change BiPoly.mul (h4e7.toBi mapPolyEnv) (h4e17.toBi mapPolyEnv)=h4p18
  rw [h4n7, h4n17]
  exact h4n18_arithmetic

#print axioms h4n18_arithmetic
end StackSorting.RationalLift
