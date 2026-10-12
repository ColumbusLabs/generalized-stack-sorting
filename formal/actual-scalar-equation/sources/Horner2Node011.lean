import Horner2Base
import Horner2Node010
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p11 : BiPoly.Poly := [[(Int.ofNat 5667136056), (Int.ofNat 37272732336), (Int.ofNat 29014906968), (Int.negSucc 117607381919)], [(Int.negSucc 27675368567), (Int.negSucc 191144664431), (Int.negSucc 192787754327), (Int.ofNat 507888480384), (Int.negSucc 32206179455)], [(Int.ofNat 63840611544), (Int.ofNat 402878497320), (Int.ofNat 393225130656), (Int.negSucc 785947602935), (Int.ofNat 5675632896), (Int.ofNat 163447680)], [(Int.negSucc 89032414883), (Int.negSucc 456659912339), (Int.negSucc 353688593603), (Int.ofNat 242158473300), (Int.ofNat 192232524192), (Int.negSucc 5930748863)], [(Int.ofNat 78215897196), (Int.ofNat 317692795848), (Int.ofNat 167391371412), (Int.ofNat 520531547352), (Int.negSucc 289549928951), (Int.negSucc 9933711455)], [(Int.negSucc 42057625259), (Int.negSucc 156383522927), (Int.negSucc 81486235619), (Int.negSucc 508494983795), (Int.ofNat 32535019884), (Int.ofNat 18114343920)], [(Int.ofNat 12899288484), (Int.ofNat 61896148860), (Int.ofNat 68579606520), (Int.ofNat 143735501316), (Int.ofNat 137895859320), (Int.ofNat 4367532960)], [(Int.negSucc 1949805383), (Int.negSucc 19033901891), (Int.negSucc 40930128947), (Int.negSucc 24183215), (Int.negSucc 67230920231), (Int.negSucc 11986831007)], [(Int.ofNat 92280816), (Int.ofNat 3953954556), (Int.ofNat 12359000376), (Int.negSucc 6185474783), (Int.ofNat 7799974272), (Int.ofNat 3426706944)], [(Int.ofNat 0), (Int.negSucc 441539423), (Int.negSucc 1489425623), (Int.ofNat 1106928288)]]

theorem h2n11_arithmetic : BiPoly.mul h2p5 h2p10=h2p11 := by
  decide +kernel

theorem h2n11 : h2e11.toBi mapPolyEnv=h2p11 := by
  change BiPoly.mul (h2e5.toBi mapPolyEnv) (h2e10.toBi mapPolyEnv)=h2p11
  rw [h2n5, h2n10]
  exact h2n11_arithmetic

#print axioms h2n11_arithmetic
end StackSorting.RationalLift
