import Horner1Base
import Horner1Node024
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p25 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 11334272112), (Int.ofNat 29208376224), (Int.negSucc 58803690959)], [(Int.ofNat 0), (Int.negSucc 55350737135), (Int.negSucc 160886380319), (Int.ofNat 257970012624), (Int.negSucc 16103089727)], [(Int.ofNat 0), (Int.ofNat 127681223088), (Int.ofNat 295032102288), (Int.negSucc 393678147839), (Int.ofNat 2817385488), (Int.ofNat 81723840)], [(Int.ofNat 0), (Int.negSucc 178064829767), (Int.negSucc 201060505607), (Int.ofNat 96864835224), (Int.ofNat 96857605704), (Int.negSucc 2965374431)], [(Int.ofNat 0), (Int.ofNat 156431794392), (Int.ofNat 9658414128), (Int.ofNat 296149086312), (Int.negSucc 143533250543), (Int.negSucc 4966855727)], [(Int.ofNat 0), (Int.negSucc 84115250519), (Int.ofNat 23693956224), (Int.negSucc 257748296135), (Int.ofNat 14003216952), (Int.ofNat 9057171960)], [(Int.ofNat 0), (Int.ofNat 25798576968), (Int.ofNat 20597989848), (Int.ofNat 54767253648), (Int.ofNat 68401988040), (Int.ofNat 2183766480)], [(Int.ofNat 0), (Int.negSucc 3899610767), (Int.negSucc 22469360711), (Int.ofNat 8017184952), (Int.negSucc 32117106239), (Int.negSucc 5993415503)], [(Int.ofNat 0), (Int.ofNat 184561632), (Int.ofNat 7169662584), (Int.negSucc 3960649583), (Int.ofNat 3471648768), (Int.ofNat 1713353472)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 883078847), (Int.ofNat 553464144)]]

theorem h1n25_arithmetic : BiPoly.mul h1p7 h1p24=h1p25 := by
  decide +kernel

theorem h1n25 : h1e25.toBi mapPolyEnv=h1p25 := by
  change BiPoly.mul (h1e7.toBi mapPolyEnv) (h1e24.toBi mapPolyEnv)=h1p25
  rw [h1n7, h1n24]
  exact h1n25_arithmetic

#print axioms h1n25_arithmetic
end StackSorting.RationalLift
