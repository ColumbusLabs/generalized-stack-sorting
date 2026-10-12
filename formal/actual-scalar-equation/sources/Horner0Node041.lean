import Horner0Base
import Horner0Node040
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p41 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 2833568027), (Int.negSucc 7302094055), (Int.ofNat 14700922740)], [(Int.ofNat 0), (Int.ofNat 13837684284), (Int.ofNat 40221595080), (Int.negSucc 64492503155), (Int.ofNat 4025772432)], [(Int.ofNat 0), (Int.negSucc 31920305771), (Int.negSucc 73758025571), (Int.ofNat 98419536960), (Int.negSucc 704346371), (Int.negSucc 20430959)], [(Int.ofNat 0), (Int.ofNat 44516207442), (Int.ofNat 50265126402), (Int.negSucc 24216208805), (Int.negSucc 24214401425), (Int.ofNat 741343608)], [(Int.ofNat 0), (Int.negSucc 39107948597), (Int.negSucc 2414603531), (Int.negSucc 74037271577), (Int.ofNat 35883312636), (Int.ofNat 1241713932)], [(Int.ofNat 0), (Int.ofNat 21028812630), (Int.negSucc 5923489055), (Int.ofNat 64437074034), (Int.negSucc 3500804237), (Int.negSucc 2264292989)], [(Int.ofNat 0), (Int.negSucc 6449644241), (Int.negSucc 5149497461), (Int.negSucc 13691813411), (Int.negSucc 17100497009), (Int.negSucc 545941619)], [(Int.ofNat 0), (Int.ofNat 974902692), (Int.ofNat 5617340178), (Int.negSucc 2004296237), (Int.ofNat 8029276560), (Int.ofNat 1498353876)], [(Int.ofNat 0), (Int.negSucc 46140407), (Int.negSucc 1792415645), (Int.ofNat 990162396), (Int.negSucc 867912191), (Int.negSucc 428338367)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 220769712), (Int.negSucc 138366035)]]

theorem h0n41_arithmetic : BiPoly.mul h0p39 h0p40=h0p41 := by
  decide +kernel

theorem h0n41 : h0e41.toBi mapPolyEnv=h0p41 := by
  change BiPoly.mul (h0e39.toBi mapPolyEnv) (h0e40.toBi mapPolyEnv)=h0p41
  rw [h0n39, h0n40]
  exact h0n41_arithmetic

#print axioms h0n41_arithmetic
end StackSorting.RationalLift
