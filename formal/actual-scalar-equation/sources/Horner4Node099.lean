import Horner4Node096
import Horner4Node098
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p99 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 9678203999), (Int.negSucc 20385600155), (Int.ofNat 56561834088), (Int.negSucc 44102768219)], [(Int.ofNat 0), (Int.ofNat 42110940960), (Int.ofNat 73452083580), (Int.negSucc 271438356311), (Int.ofNat 209091437532), (Int.negSucc 12077317295)], [(Int.ofNat 0), (Int.negSucc 74382374519), (Int.negSucc 102790971287), (Int.ofNat 414739409076), (Int.negSucc 301080564179), (Int.ofNat 3771174348), (Int.ofNat 61292880)], [(Int.ofNat 0), (Int.ofNat 68113049040), (Int.ofNat 62445577554), (Int.negSucc 156438420677), (Int.negSucc 20473592309), (Int.ofNat 78629733918), (Int.negSucc 2224030823)], [(Int.ofNat 0), (Int.negSucc 34064888399), (Int.negSucc 1515408677), (Int.negSucc 183611404583), (Int.ofNat 343286165610), (Int.negSucc 112850604503), (Int.negSucc 3725141795)], [(Int.ofNat 0), (Int.ofNat 8834646960), (Int.negSucc 20349129401), (Int.ofNat 193274584128), (Int.negSucc 194904547109), (Int.negSucc 8832627557), (Int.ofNat 6792878970)], [(Int.ofNat 0), (Int.negSucc 933170039), (Int.ofNat 11396859354), (Int.negSucc 50712515801), (Int.negSucc 27962227475), (Int.ofNat 67192766982), (Int.ofNat 1637824860)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2391832187), (Int.negSucc 6923845133), (Int.ofNat 43676822538), (Int.negSucc 18845478791), (Int.negSucc 4495061627)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 138421224), (Int.ofNat 5149370610), (Int.negSucc 9223819163), (Int.negSucc 4069010591), (Int.ofNat 1285015104)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 662309135), (Int.ofNat 493600716), (Int.ofNat 1312076880)]]

theorem h4n99_arithmetic : BiPoly.add h4p96 h4p98=h4p99 := by
  decide +kernel

theorem h4n99 : h4e99.toBi mapPolyEnv=h4p99 := by
  change BiPoly.add (h4e96.toBi mapPolyEnv) (h4e98.toBi mapPolyEnv)=h4p99
  rw [h4n96, h4n98]
  exact h4n99_arithmetic

#print axioms h4n99_arithmetic
end StackSorting.RationalLift
