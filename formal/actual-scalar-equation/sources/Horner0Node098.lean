import Horner0Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p98 : BiPoly.Poly := [[(Int.negSucc 3226067999), (Int.negSucc 9628768079), (Int.ofNat 11551850640)], [(Int.ofNat 14036980320), (Int.ofNat 38321712144), (Int.negSucc 50257857023), (Int.ofNat 5204642688)], [(Int.negSucc 24794124839), (Int.negSucc 66183962867), (Int.ofNat 64488444120), (Int.negSucc 1940651099), (Int.ofNat 552711744)], [(Int.ofNat 22704349680), (Int.ofNat 65331399960), (Int.negSucc 1881013823), (Int.negSucc 31040739575), (Int.ofNat 1995509880)], [(Int.negSucc 11354962799), (Int.negSucc 39613084823), (Int.negSucc 63618405059), (Int.ofNat 40391450292), (Int.negSucc 1733555531)], [(Int.ofNat 2944882320), (Int.ofNat 14245769496), (Int.ofNat 58501372320), (Int.negSucc 531108335), (Int.negSucc 6445013423)], [(Int.negSucc 311056679), (Int.negSucc 2650691123), (Int.negSucc 22053669395), (Int.negSucc 23012555903), (Int.ofNat 5297091984)], [(Int.ofNat 0), (Int.ofNat 177625296), (Int.ofNat 3309391800), (Int.ofNat 12554644608), (Int.ofNat 1747450296)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 75958775), (Int.negSucc 2084443991), (Int.negSucc 2224249055)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 26167536), (Int.ofNat 437358960)]]

theorem h0n98_arithmetic : BiPoly.mul h0p46 h0p7=h0p98 := by
  decide +kernel

theorem h0n98 : h0e98.toBi mapPolyEnv=h0p98 := by
  change BiPoly.mul (h0e46.toBi mapPolyEnv) (h0e7.toBi mapPolyEnv)=h0p98
  rw [h0n46, h0n7]
  exact h0n98_arithmetic

#print axioms h0n98_arithmetic
end StackSorting.RationalLift
