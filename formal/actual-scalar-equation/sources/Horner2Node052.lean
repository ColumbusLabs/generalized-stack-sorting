import Horner2Base
import Horner2Node015
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p52 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 1889045352), (Int.ofNat 4868062704), (Int.negSucc 9800615159)], [(Int.ofNat 0), (Int.negSucc 9225122855), (Int.negSucc 26814396719), (Int.ofNat 42995002104), (Int.negSucc 2683848287)], [(Int.ofNat 0), (Int.ofNat 21280203848), (Int.ofNat 49172017048), (Int.negSucc 65613024639), (Int.ofNat 469564248), (Int.ofNat 13620640)], [(Int.ofNat 0), (Int.negSucc 29677471627), (Int.negSucc 33510084267), (Int.ofNat 16144139204), (Int.ofNat 16142934284), (Int.negSucc 494229071)], [(Int.ofNat 0), (Int.ofNat 26071965732), (Int.ofNat 1609735688), (Int.ofNat 49358181052), (Int.negSucc 23922208423), (Int.negSucc 827809287)], [(Int.ofNat 0), (Int.negSucc 14019208419), (Int.ofNat 3948992704), (Int.negSucc 42958049355), (Int.ofNat 2333869492), (Int.ofNat 1509528660)], [(Int.ofNat 0), (Int.ofNat 4299762828), (Int.ofNat 3432998308), (Int.ofNat 9127875608), (Int.ofNat 11400331340), (Int.ofNat 363961080)], [(Int.ofNat 0), (Int.negSucc 649935127), (Int.negSucc 3744893451), (Int.ofNat 1336197492), (Int.negSucc 5352851039), (Int.negSucc 998902583)], [(Int.ofNat 0), (Int.ofNat 30760272), (Int.ofNat 1194943764), (Int.negSucc 660108263), (Int.ofNat 578608128), (Int.ofNat 285558912)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 147179807), (Int.ofNat 92244024)]]

theorem h2n52_arithmetic : BiPoly.mul h2p51 h2p15=h2p52 := by
  decide +kernel

theorem h2n52 : h2e52.toBi mapPolyEnv=h2p52 := by
  change BiPoly.mul (h2e51.toBi mapPolyEnv) (h2e15.toBi mapPolyEnv)=h2p52
  rw [h2n51, h2n15]
  exact h2n52_arithmetic

#print axioms h2n52_arithmetic
end StackSorting.RationalLift
