import Horner2Base
import Horner2Node083
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p84 : BiPoly.Poly := [[(Int.ofNat 1889045352), (Int.ofNat 19980425520), (Int.ofNat 29143886472), (Int.negSucc 78404921279)], [(Int.negSucc 9225122855), (Int.negSucc 100615379567), (Int.negSucc 171520171655), (Int.ofNat 341276168544), (Int.negSucc 21470786303)], [(Int.ofNat 21280203848), (Int.ofNat 219413647832), (Int.ofNat 327763111744), (Int.negSucc 524434632871), (Int.ofNat 3770134624), (Int.ofNat 108965120)], [(Int.negSucc 29677471627), (Int.negSucc 270929857291), (Int.negSucc 251936534939), (Int.ofNat 145296047916), (Int.ofNat 128649245200), (Int.negSucc 3953832575)], [(Int.ofNat 26071965732), (Int.ofNat 210185461544), (Int.ofNat 62236066556), (Int.ofNat 370943239992), (Int.negSucc 192205476679), (Int.negSucc 6622474303)], [(Int.negSucc 14019208419), (Int.negSucc 108204674655), (Int.negSucc 11366107723), (Int.negSucc 341330525355), (Int.ofNat 20180484596), (Int.ofNat 12076229280)], [(Int.ofNat 4299762828), (Int.ofNat 37831100932), (Int.ofNat 36591862072), (Int.ofNat 84423336204), (Int.ofNat 91566611800), (Int.ofNat 2911688640)], [(Int.negSucc 649935127), (Int.negSucc 8944374475), (Int.negSucc 28622950123), (Int.ofNat 5336728896), (Int.negSucc 43821710903), (Int.negSucc 7991220671)], [(Int.ofNat 30760272), (Int.ofNat 1441025940), (Int.ofNat 8899441848), (Int.negSucc 4702257983), (Int.ofNat 4914423936), (Int.ofNat 2284471296)], [(Int.ofNat 0), (Int.negSucc 147179807), (Int.negSucc 1085194439), (Int.ofNat 737952192)]]

theorem h2n84_arithmetic : BiPoly.mul h2p5 h2p83=h2p84 := by
  decide +kernel

theorem h2n84 : h2e84.toBi mapPolyEnv=h2p84 := by
  change BiPoly.mul (h2e5.toBi mapPolyEnv) (h2e83.toBi mapPolyEnv)=h2p84
  rw [h2n5, h2n83]
  exact h2n84_arithmetic

#print axioms h2n84_arithmetic
end StackSorting.RationalLift
