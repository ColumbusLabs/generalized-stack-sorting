import Horner1Base
import Horner1Node024
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p104 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 1889045351), (Int.negSucc 4868062703), (Int.ofNat 9800615160)], [(Int.ofNat 0), (Int.ofNat 9225122856), (Int.ofNat 26814396720), (Int.negSucc 42995002103), (Int.ofNat 2683848288)], [(Int.ofNat 0), (Int.negSucc 21280203847), (Int.negSucc 49172017047), (Int.ofNat 65613024640), (Int.negSucc 469564247), (Int.negSucc 13620639)], [(Int.ofNat 0), (Int.ofNat 29677471628), (Int.ofNat 33510084268), (Int.negSucc 16144139203), (Int.negSucc 16142934283), (Int.ofNat 494229072)], [(Int.ofNat 0), (Int.negSucc 26071965731), (Int.negSucc 1609735687), (Int.negSucc 49358181051), (Int.ofNat 23922208424), (Int.ofNat 827809288)], [(Int.ofNat 0), (Int.ofNat 14019208420), (Int.negSucc 3948992703), (Int.ofNat 42958049356), (Int.negSucc 2333869491), (Int.negSucc 1509528659)], [(Int.ofNat 0), (Int.negSucc 4299762827), (Int.negSucc 3432998307), (Int.negSucc 9127875607), (Int.negSucc 11400331339), (Int.negSucc 363961079)], [(Int.ofNat 0), (Int.ofNat 649935128), (Int.ofNat 3744893452), (Int.negSucc 1336197491), (Int.ofNat 5352851040), (Int.ofNat 998902584)], [(Int.ofNat 0), (Int.negSucc 30760271), (Int.negSucc 1194943763), (Int.ofNat 660108264), (Int.negSucc 578608127), (Int.negSucc 285558911)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 147179808), (Int.negSucc 92244023)]]

theorem h1n104_arithmetic : BiPoly.mul h1p64 h1p24=h1p104 := by
  decide +kernel

theorem h1n104 : h1e104.toBi mapPolyEnv=h1p104 := by
  change BiPoly.mul (h1e64.toBi mapPolyEnv) (h1e24.toBi mapPolyEnv)=h1p104
  rw [h1n64, h1n24]
  exact h1n104_arithmetic

#print axioms h1n104_arithmetic
end StackSorting.RationalLift
