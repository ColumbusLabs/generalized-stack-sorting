import Horner0Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p106 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 8706816), (Int.negSucc 9664187), (Int.ofNat 90904872), (Int.negSucc 48917243), (Int.negSucc 105715295)], [(Int.ofNat 0), (Int.negSucc 32256463), (Int.ofNat 36644638), (Int.negSucc 473549633), (Int.ofNat 135326642), (Int.ofNat 288699378), (Int.negSucc 29365359)], [(Int.ofNat 0), (Int.ofNat 47168280), (Int.negSucc 13402305), (Int.ofNat 893344012), (Int.negSucc 80551389), (Int.negSucc 257964479), (Int.negSucc 15132415)], [(Int.ofNat 0), (Int.negSucc 35069627), (Int.negSucc 74148087), (Int.negSucc 763715547), (Int.negSucc 276429285), (Int.negSucc 25390241), (Int.ofNat 120027336)], [(Int.ofNat 0), (Int.ofNat 14493284), (Int.ofNat 98211592), (Int.ofNat 316578468), (Int.ofNat 522692754), (Int.ofNat 172213548), (Int.negSucc 77904503)], [(Int.ofNat 0), (Int.negSucc 3409379), (Int.negSucc 44925365), (Int.negSucc 81601049), (Int.negSucc 315486647), (Int.negSucc 135404603), (Int.negSucc 37586879)], [(Int.ofNat 0), (Int.ofNat 367092), (Int.ofNat 7483950), (Int.ofNat 22107276), (Int.ofNat 70552224), (Int.ofNat 64107504), (Int.ofNat 41239152)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 200231), (Int.negSucc 3517451), (Int.negSucc 3445631), (Int.negSucc 18941039)]]

theorem h0n106_arithmetic : BiPoly.mul h0p5 h0p12=h0p106 := by
  decide +kernel

theorem h0n106 : h0e106.toBi mapPolyEnv=h0p106 := by
  change BiPoly.mul (h0e5.toBi mapPolyEnv) (h0e12.toBi mapPolyEnv)=h0p106
  rw [h0n5, h0n12]
  exact h0n106_arithmetic

#print axioms h0n106_arithmetic
end StackSorting.RationalLift
