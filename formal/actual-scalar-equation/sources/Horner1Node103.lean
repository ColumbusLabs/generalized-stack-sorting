import Horner1Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p103 : BiPoly.Poly := [[(Int.negSucc 6452135999), (Int.negSucc 19257536159), (Int.ofNat 23103701280)], [(Int.ofNat 28073960640), (Int.ofNat 76643424288), (Int.negSucc 100515714047), (Int.ofNat 10409285376)], [(Int.negSucc 49588249679), (Int.negSucc 132367925735), (Int.ofNat 128976888240), (Int.negSucc 3881302199), (Int.ofNat 1105423488)], [(Int.ofNat 45408699360), (Int.ofNat 130662799920), (Int.negSucc 3762027647), (Int.negSucc 62081479151), (Int.ofNat 3991019760)], [(Int.negSucc 22709925599), (Int.negSucc 79226169647), (Int.negSucc 127236810119), (Int.ofNat 80782900584), (Int.negSucc 3467111063)], [(Int.ofNat 5889764640), (Int.ofNat 28491538992), (Int.ofNat 117002744640), (Int.negSucc 1062216671), (Int.negSucc 12890026847)], [(Int.negSucc 622113359), (Int.negSucc 5301382247), (Int.negSucc 44107338791), (Int.negSucc 46025111807), (Int.ofNat 10594183968)], [(Int.ofNat 0), (Int.ofNat 355250592), (Int.ofNat 6618783600), (Int.ofNat 25109289216), (Int.ofNat 3494900592)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 151917551), (Int.negSucc 4168887983), (Int.negSucc 4448498111)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 52335072), (Int.ofNat 874717920)]]

theorem h1n103_arithmetic : BiPoly.mul h1p7 h1p6=h1p103 := by
  decide +kernel

theorem h1n103 : h1e103.toBi mapPolyEnv=h1p103 := by
  change BiPoly.mul (h1e7.toBi mapPolyEnv) (h1e6.toBi mapPolyEnv)=h1p103
  rw [h1n7, h1n6]
  exact h1n103_arithmetic

#print axioms h1n103_arithmetic
end StackSorting.RationalLift
