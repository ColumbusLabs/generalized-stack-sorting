import Horner4Base
import Horner4Node056
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p57 : BiPoly.Poly := [[(Int.ofNat 11334272112), (Int.ofNat 17874104112), (Int.negSucc 88012067183), (Int.ofNat 58803690960)], [(Int.negSucc 55350737135), (Int.negSucc 105535643183), (Int.ofNat 418856392944), (Int.negSucc 274073102351), (Int.ofNat 16103089728)], [(Int.ofNat 127681223088), (Int.ofNat 167350879200), (Int.negSucc 688710250127), (Int.ofNat 396495533328), (Int.negSucc 2735661647), (Int.negSucc 81723839)], [(Int.negSucc 178064829767), (Int.negSucc 22995675839), (Int.ofNat 297925340832), (Int.negSucc 7229519), (Int.negSucc 99822980135), (Int.ofNat 2965374432)], [(Int.ofNat 156431794392), (Int.negSucc 146773380263), (Int.ofNat 286490672184), (Int.negSucc 439682336855), (Int.ofNat 138566394816), (Int.ofNat 4966855728)], [(Int.negSucc 84115250519), (Int.ofNat 107809206744), (Int.negSucc 281442252359), (Int.ofNat 271751513088), (Int.negSucc 4946044991), (Int.negSucc 9057171959)], [(Int.ofNat 25798576968), (Int.negSucc 5200587119), (Int.ofNat 34169263800), (Int.ofNat 13634734392), (Int.negSucc 66218221559), (Int.negSucc 2183766479)], [(Int.negSucc 3899610767), (Int.negSucc 18569749943), (Int.ofNat 30486545664), (Int.negSucc 40134291191), (Int.ofNat 26123690736), (Int.ofNat 5993415504)], [(Int.ofNat 184561632), (Int.ofNat 6985100952), (Int.negSucc 11130312167), (Int.ofNat 7432298352), (Int.negSucc 1758295295), (Int.negSucc 1713353471)], [(Int.ofNat 0), (Int.negSucc 883078847), (Int.ofNat 1436542992), (Int.negSucc 553464143)]]

theorem h4n57_arithmetic : BiPoly.mul h4p7 h4p56=h4p57 := by
  decide +kernel

theorem h4n57 : h4e57.toBi mapPolyEnv=h4p57 := by
  change BiPoly.mul (h4e7.toBi mapPolyEnv) (h4e56.toBi mapPolyEnv)=h4p57
  rw [h4n7, h4n56]
  exact h4n57_arithmetic

#print axioms h4n57_arithmetic
end StackSorting.RationalLift
