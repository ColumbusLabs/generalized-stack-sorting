import Horner2Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p43 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 2353391), (Int.negSucc 15067541), (Int.ofNat 110200308), (Int.negSucc 13450325), (Int.negSucc 52857647)], [(Int.ofNat 0), (Int.ofNat 8955200), (Int.ofNat 45090875), (Int.negSucc 428781428), (Int.ofNat 124214965), (Int.ofNat 81932205), (Int.negSucc 14682679)], [(Int.ofNat 0), (Int.negSucc 12632579), (Int.negSucc 43955704), (Int.ofNat 613384190), (Int.negSucc 118328302), (Int.ofNat 14400648), (Int.negSucc 25943079)], [(Int.ofNat 0), (Int.ofNat 7533714), (Int.ofNat 7834996), (Int.negSucc 385089685), (Int.negSucc 201090178), (Int.negSucc 9267692), (Int.ofNat 32794536)], [(Int.ofNat 0), (Int.negSucc 1039981), (Int.ofNat 12842468), (Int.ofNat 88631730), (Int.ofNat 351530481), (Int.negSucc 22108721), (Int.ofNat 11649564)], [(Int.ofNat 0), (Int.negSucc 646505), (Int.negSucc 8477942), (Int.ofNat 2455167), (Int.negSucc 165359807), (Int.negSucc 40716773), (Int.negSucc 11807351)], [(Int.ofNat 0), (Int.ofNat 183546), (Int.ofNat 1832967), (Int.ofNat 140238), (Int.ofNat 18827064), (Int.ofNat 44370288), (Int.ofNat 1086264)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 100115), (Int.negSucc 918917), (Int.ofNat 1939680), (Int.negSucc 9470519)]]

theorem h2n43_arithmetic : BiPoly.mul h2p20 h2p8=h2p43 := by
  decide +kernel

theorem h2n43 : h2e43.toBi mapPolyEnv=h2p43 := by
  change BiPoly.mul (h2e20.toBi mapPolyEnv) (h2e8.toBi mapPolyEnv)=h2p43
  rw [h2n20, h2n8]
  exact h2n43_arithmetic

#print axioms h2n43_arithmetic
end StackSorting.RationalLift
