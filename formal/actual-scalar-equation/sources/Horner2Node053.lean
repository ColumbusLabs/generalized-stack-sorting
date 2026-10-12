import Horner2Node050
import Horner2Node052
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p53 : BiPoly.Poly := [[(Int.ofNat 3226068000), (Int.ofNat 11517813432), (Int.negSucc 6683787935), (Int.negSucc 9800615159)], [(Int.negSucc 14036980319), (Int.negSucc 47546834999), (Int.ofNat 23443460304), (Int.ofNat 37790359416), (Int.negSucc 2683848287)], [(Int.ofNat 24794124840), (Int.ofNat 87464166716), (Int.negSucc 15316427071), (Int.negSucc 63672373539), (Int.negSucc 83147495), (Int.ofNat 13620640)], [(Int.negSucc 22704349679), (Int.negSucc 95008871587), (Int.negSucc 31629070443), (Int.ofNat 47184878780), (Int.ofNat 14147424404), (Int.negSucc 494229071)], [(Int.ofNat 11354962800), (Int.ofNat 65685050556), (Int.ofNat 65228140748), (Int.ofNat 8966730760), (Int.negSucc 22188652891), (Int.negSucc 827809287)], [(Int.negSucc 2944882319), (Int.negSucc 28264977915), (Int.negSucc 54552379615), (Int.negSucc 42426941019), (Int.ofNat 8778882916), (Int.ofNat 1509528660)], [(Int.ofNat 311056680), (Int.ofNat 6950453952), (Int.ofNat 25486667704), (Int.ofNat 32140431512), (Int.ofNat 6103239356), (Int.ofNat 363961080)], [(Int.ofNat 0), (Int.negSucc 827560423), (Int.negSucc 7054285251), (Int.negSucc 11218447115), (Int.negSucc 7100301335), (Int.negSucc 998902583)], [(Int.ofNat 0), (Int.ofNat 30760272), (Int.ofNat 1270902540), (Int.ofNat 1424335728), (Int.ofNat 2802857184), (Int.ofNat 285558912)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 147179807), (Int.ofNat 66076488), (Int.negSucc 437358959)]]

theorem h2n53_arithmetic : BiPoly.add h2p50 h2p52=h2p53 := by
  decide +kernel

theorem h2n53 : h2e53.toBi mapPolyEnv=h2p53 := by
  change BiPoly.add (h2e50.toBi mapPolyEnv) (h2e52.toBi mapPolyEnv)=h2p53
  rw [h2n50, h2n52]
  exact h2n53_arithmetic

#print axioms h2n53_arithmetic
end StackSorting.RationalLift
