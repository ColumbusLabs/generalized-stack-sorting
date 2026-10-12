import Horner2Base
import Horner2Node015
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p38 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 18890453520), (Int.ofNat 48680627040), (Int.negSucc 98006151599)], [(Int.ofNat 0), (Int.negSucc 92251228559), (Int.negSucc 268143967199), (Int.ofNat 429950021040), (Int.negSucc 26838482879)], [(Int.ofNat 0), (Int.ofNat 212802038480), (Int.ofNat 491720170480), (Int.negSucc 656130246399), (Int.ofNat 4695642480), (Int.ofNat 136206400)], [(Int.ofNat 0), (Int.negSucc 296774716279), (Int.negSucc 335100842679), (Int.ofNat 161441392040), (Int.ofNat 161429342840), (Int.negSucc 4942290719)], [(Int.ofNat 0), (Int.ofNat 260719657320), (Int.ofNat 16097356880), (Int.ofNat 493581810520), (Int.negSucc 239222084239), (Int.negSucc 8278092879)], [(Int.ofNat 0), (Int.negSucc 140192084199), (Int.ofNat 39489927040), (Int.negSucc 429580493559), (Int.ofNat 23338694920), (Int.ofNat 15095286600)], [(Int.ofNat 0), (Int.ofNat 42997628280), (Int.ofNat 34329983080), (Int.ofNat 91278756080), (Int.ofNat 114003313400), (Int.ofNat 3639610800)], [(Int.ofNat 0), (Int.negSucc 6499351279), (Int.negSucc 37448934519), (Int.ofNat 13361974920), (Int.negSucc 53528510399), (Int.negSucc 9989025839)], [(Int.ofNat 0), (Int.ofNat 307602720), (Int.ofNat 11949437640), (Int.negSucc 6601082639), (Int.ofNat 5786081280), (Int.ofNat 2855589120)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1471798079), (Int.ofNat 922440240)]]

theorem h2n38_arithmetic : BiPoly.mul h2p37 h2p15=h2p38 := by
  decide +kernel

theorem h2n38 : h2e38.toBi mapPolyEnv=h2p38 := by
  change BiPoly.mul (h2e37.toBi mapPolyEnv) (h2e15.toBi mapPolyEnv)=h2p38
  rw [h2n37, h2n15]
  exact h2n38_arithmetic

#print axioms h2n38_arithmetic
end StackSorting.RationalLift
