import Horner1Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p22 : BiPoly.Poly := [[(Int.ofNat 25808544000), (Int.ofNat 77030144640), (Int.negSucc 92414805119)], [(Int.negSucc 112295842559), (Int.negSucc 306573697151), (Int.ofNat 402062856192), (Int.negSucc 41637141503)], [(Int.ofNat 198352998720), (Int.ofNat 529471702944), (Int.negSucc 515907552959), (Int.ofNat 15525208800), (Int.negSucc 4421693951)], [(Int.negSucc 181634797439), (Int.negSucc 522651199679), (Int.ofNat 15048110592), (Int.ofNat 248325916608), (Int.negSucc 15964079039)], [(Int.ofNat 90839702400), (Int.ofNat 316904678592), (Int.ofNat 508947240480), (Int.negSucc 323131602335), (Int.ofNat 13868444256)], [(Int.negSucc 23559058559), (Int.negSucc 113966155967), (Int.negSucc 468010978559), (Int.ofNat 4248866688), (Int.ofNat 51560107392)], [(Int.ofNat 2488453440), (Int.ofNat 21205528992), (Int.ofNat 176429355168), (Int.ofNat 184100447232), (Int.negSucc 42376735871)], [(Int.ofNat 0), (Int.negSucc 1421002367), (Int.negSucc 26475134399), (Int.negSucc 100437156863), (Int.negSucc 13979602367)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 607670208), (Int.ofNat 16675551936), (Int.ofNat 17793992448)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 209340287), (Int.negSucc 3498871679)]]

theorem h1n22_arithmetic : BiPoly.mul h1p21 h1p6=h1p22 := by
  decide +kernel

theorem h1n22 : h1e22.toBi mapPolyEnv=h1p22 := by
  change BiPoly.mul (h1e21.toBi mapPolyEnv) (h1e6.toBi mapPolyEnv)=h1p22
  rw [h1n21, h1n6]
  exact h1n22_arithmetic

#print axioms h1n22_arithmetic
end StackSorting.RationalLift
