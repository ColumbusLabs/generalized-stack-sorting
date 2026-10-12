import Horner2Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p50 : BiPoly.Poly := [[(Int.ofNat 3226068000), (Int.ofNat 9628768080), (Int.negSucc 11551850639)], [(Int.negSucc 14036980319), (Int.negSucc 38321712143), (Int.ofNat 50257857024), (Int.negSucc 5204642687)], [(Int.ofNat 24794124840), (Int.ofNat 66183962868), (Int.negSucc 64488444119), (Int.ofNat 1940651100), (Int.negSucc 552711743)], [(Int.negSucc 22704349679), (Int.negSucc 65331399959), (Int.ofNat 1881013824), (Int.ofNat 31040739576), (Int.negSucc 1995509879)], [(Int.ofNat 11354962800), (Int.ofNat 39613084824), (Int.ofNat 63618405060), (Int.negSucc 40391450291), (Int.ofNat 1733555532)], [(Int.negSucc 2944882319), (Int.negSucc 14245769495), (Int.negSucc 58501372319), (Int.ofNat 531108336), (Int.ofNat 6445013424)], [(Int.ofNat 311056680), (Int.ofNat 2650691124), (Int.ofNat 22053669396), (Int.ofNat 23012555904), (Int.negSucc 5297091983)], [(Int.ofNat 0), (Int.negSucc 177625295), (Int.negSucc 3309391799), (Int.negSucc 12554644607), (Int.negSucc 1747450295)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 75958776), (Int.ofNat 2084443992), (Int.ofNat 2224249056)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 26167535), (Int.negSucc 437358959)]]

theorem h2n50_arithmetic : BiPoly.mul h2p49 h2p35=h2p50 := by
  decide +kernel

theorem h2n50 : h2e50.toBi mapPolyEnv=h2p50 := by
  change BiPoly.mul (h2e49.toBi mapPolyEnv) (h2e35.toBi mapPolyEnv)=h2p50
  rw [h2n49, h2n35]
  exact h2n50_arithmetic

#print axioms h2n50_arithmetic
end StackSorting.RationalLift
