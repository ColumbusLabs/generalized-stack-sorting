import Horner2Base
import Horner2Node024
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p25 : BiPoly.Poly := [[(Int.negSucc 11334272111), (Int.negSucc 74545464671), (Int.negSucc 58029813935), (Int.ofNat 235214763840)], [(Int.ofNat 55350737136), (Int.ofNat 382289328864), (Int.ofNat 385575508656), (Int.negSucc 1015776960767), (Int.ofNat 64412358912)], [(Int.negSucc 127681223087), (Int.negSucc 805756994639), (Int.negSucc 786450261311), (Int.ofNat 1571895205872), (Int.negSucc 11351265791), (Int.negSucc 326895359)], [(Int.ofNat 178064829768), (Int.ofNat 913319824680), (Int.ofNat 707377187208), (Int.negSucc 484316946599), (Int.negSucc 384465048383), (Int.ofNat 11861497728)], [(Int.negSucc 156431794391), (Int.negSucc 635385591695), (Int.negSucc 334782742823), (Int.negSucc 1041063094703), (Int.ofNat 579099857904), (Int.ofNat 19867422912)], [(Int.ofNat 84115250520), (Int.ofNat 312767045856), (Int.ofNat 162972471240), (Int.ofNat 1016989967592), (Int.negSucc 65070039767), (Int.negSucc 36228687839)], [(Int.negSucc 25798576967), (Int.negSucc 123792297719), (Int.negSucc 137159213039), (Int.negSucc 287471002631), (Int.negSucc 275791718639), (Int.negSucc 8735065919)], [(Int.ofNat 3899610768), (Int.ofNat 38067803784), (Int.ofNat 81860257896), (Int.ofNat 48366432), (Int.ofNat 134461840464), (Int.ofNat 23973662016)], [(Int.negSucc 184561631), (Int.negSucc 7907909111), (Int.negSucc 24718000751), (Int.ofNat 12370949568), (Int.negSucc 15599948543), (Int.negSucc 6853413887)], [(Int.ofNat 0), (Int.ofNat 883078848), (Int.ofNat 2978851248), (Int.negSucc 2213856575)]]

theorem h2n25_arithmetic : BiPoly.mul h2p5 h2p24=h2p25 := by
  decide +kernel

theorem h2n25 : h2e25.toBi mapPolyEnv=h2p25 := by
  change BiPoly.mul (h2e5.toBi mapPolyEnv) (h2e24.toBi mapPolyEnv)=h2p25
  rw [h2n5, h2n24]
  exact h2n25_arithmetic

#print axioms h2n25_arithmetic
end StackSorting.RationalLift
