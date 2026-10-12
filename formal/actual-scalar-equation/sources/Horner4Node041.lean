import Horner4Base
import Horner4Node040
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p41 : BiPoly.Poly := [[(Int.negSucc 45337088447), (Int.negSucc 71496416447), (Int.ofNat 352048268736), (Int.negSucc 235214763839)], [(Int.ofNat 221402948544), (Int.ofNat 422142572736), (Int.negSucc 1675425571775), (Int.ofNat 1096292409408), (Int.negSucc 64412358911)], [(Int.negSucc 510724892351), (Int.negSucc 669403516799), (Int.ofNat 2754841000512), (Int.negSucc 1585982133311), (Int.ofNat 10942646592), (Int.ofNat 326895360)], [(Int.ofNat 712259319072), (Int.ofNat 91982703360), (Int.negSucc 1191701363327), (Int.ofNat 28918080), (Int.ofNat 399291920544), (Int.negSucc 11861497727)], [(Int.negSucc 625727177567), (Int.ofNat 587093521056), (Int.negSucc 1145962688735), (Int.ofNat 1758729347424), (Int.negSucc 554265579263), (Int.negSucc 19867422911)], [(Int.ofNat 336461002080), (Int.negSucc 431236826975), (Int.ofNat 1125769009440), (Int.negSucc 1087006052351), (Int.ofNat 19784179968), (Int.ofNat 36228687840)], [(Int.negSucc 103194307871), (Int.ofNat 20802348480), (Int.negSucc 136677055199), (Int.negSucc 54538937567), (Int.ofNat 264872886240), (Int.ofNat 8735065920)], [(Int.ofNat 15598443072), (Int.ofNat 74278999776), (Int.negSucc 121946182655), (Int.ofNat 160537164768), (Int.negSucc 104494762943), (Int.negSucc 23973662015)], [(Int.negSucc 738246527), (Int.negSucc 27940403807), (Int.ofNat 44521248672), (Int.negSucc 29729193407), (Int.ofNat 7033181184), (Int.ofNat 6853413888)], [(Int.ofNat 0), (Int.ofNat 3532315392), (Int.negSucc 5746171967), (Int.ofNat 2213856576)]]

theorem h4n41_arithmetic : BiPoly.mul h4p7 h4p40=h4p41 := by
  decide +kernel

theorem h4n41 : h4e41.toBi mapPolyEnv=h4p41 := by
  change BiPoly.mul (h4e7.toBi mapPolyEnv) (h4e40.toBi mapPolyEnv)=h4p41
  rw [h4n7, h4n40]
  exact h4n41_arithmetic

#print axioms h4n41_arithmetic
end StackSorting.RationalLift
