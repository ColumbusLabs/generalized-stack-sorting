import Horner1Node103
import Horner1Node104
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p105 : BiPoly.Poly := [[(Int.negSucc 6452135999), (Int.negSucc 21146581511), (Int.ofNat 18235638576), (Int.ofNat 9800615160)], [(Int.ofNat 28073960640), (Int.ofNat 85868547144), (Int.negSucc 73701317327), (Int.negSucc 32585716727), (Int.ofNat 2683848288)], [(Int.negSucc 49588249679), (Int.negSucc 153648129583), (Int.ofNat 79804871192), (Int.ofNat 61731722440), (Int.ofNat 635859240), (Int.negSucc 13620639)], [(Int.ofNat 45408699360), (Int.ofNat 160340271548), (Int.ofNat 29748056620), (Int.negSucc 78225618355), (Int.negSucc 12151914523), (Int.ofNat 494229072)], [(Int.negSucc 22709925599), (Int.negSucc 105298135379), (Int.negSucc 128846545807), (Int.ofNat 31424719532), (Int.ofNat 20455097360), (Int.ofNat 827809288)], [(Int.ofNat 5889764640), (Int.ofNat 42510747412), (Int.ofNat 113053751936), (Int.ofNat 41895832684), (Int.negSucc 15223896339), (Int.negSucc 1509528659)], [(Int.negSucc 622113359), (Int.negSucc 9601145075), (Int.negSucc 47540337099), (Int.negSucc 55152987415), (Int.negSucc 806147371), (Int.negSucc 363961079)], [(Int.ofNat 0), (Int.ofNat 1005185720), (Int.ofNat 10363677052), (Int.ofNat 23773091724), (Int.ofNat 8847751632), (Int.ofNat 998902584)], [(Int.ofNat 0), (Int.negSucc 30760271), (Int.negSucc 1346861315), (Int.negSucc 3508779719), (Int.negSucc 5027106239), (Int.negSucc 285558911)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 147179808), (Int.negSucc 39908951), (Int.ofNat 874717920)]]

theorem h1n105_arithmetic : BiPoly.add h1p103 h1p104=h1p105 := by
  decide +kernel

theorem h1n105 : h1e105.toBi mapPolyEnv=h1p105 := by
  change BiPoly.add (h1e103.toBi mapPolyEnv) (h1e104.toBi mapPolyEnv)=h1p105
  rw [h1n103, h1n104]
  exact h1n105_arithmetic

#print axioms h1n105_arithmetic
end StackSorting.RationalLift
