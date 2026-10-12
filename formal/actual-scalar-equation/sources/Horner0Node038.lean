import Horner0Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p38 : BiPoly.Poly := [[(Int.ofNat 3226068000), (Int.ofNat 9628768080), (Int.negSucc 11551850639)], [(Int.negSucc 14036980319), (Int.negSucc 38321712143), (Int.ofNat 50257857024), (Int.negSucc 5204642687)], [(Int.ofNat 24794124840), (Int.ofNat 66183962868), (Int.negSucc 64488444119), (Int.ofNat 1940651100), (Int.negSucc 552711743)], [(Int.negSucc 22704349679), (Int.negSucc 65331399959), (Int.ofNat 1881013824), (Int.ofNat 31040739576), (Int.negSucc 1995509879)], [(Int.ofNat 11354962800), (Int.ofNat 39613084824), (Int.ofNat 63618405060), (Int.negSucc 40391450291), (Int.ofNat 1733555532)], [(Int.negSucc 2944882319), (Int.negSucc 14245769495), (Int.negSucc 58501372319), (Int.ofNat 531108336), (Int.ofNat 6445013424)], [(Int.ofNat 311056680), (Int.ofNat 2650691124), (Int.ofNat 22053669396), (Int.ofNat 23012555904), (Int.negSucc 5297091983)], [(Int.ofNat 0), (Int.negSucc 177625295), (Int.negSucc 3309391799), (Int.negSucc 12554644607), (Int.negSucc 1747450295)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 75958776), (Int.ofNat 2084443992), (Int.ofNat 2224249056)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 26167535), (Int.negSucc 437358959)]]

theorem h0n38_arithmetic : BiPoly.mul h0p37 h0p7=h0p38 := by
  decide +kernel

theorem h0n38 : h0e38.toBi mapPolyEnv=h0p38 := by
  change BiPoly.mul (h0e37.toBi mapPolyEnv) (h0e7.toBi mapPolyEnv)=h0p38
  rw [h0n37, h0n7]
  exact h0n38_arithmetic

#print axioms h0n38_arithmetic
end StackSorting.RationalLift
