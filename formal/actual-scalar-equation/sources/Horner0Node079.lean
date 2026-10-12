import Horner0Base
import Horner0Node078
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p79 : BiPoly.Poly := [[(Int.negSucc 5667136055), (Int.negSucc 25938460223), (Int.ofNat 193469256), (Int.ofNat 58803690960)], [(Int.ofNat 27675368568), (Int.ofNat 135793927296), (Int.ofNat 31901374008), (Int.negSucc 249918467759), (Int.ofNat 16103089728)], [(Int.negSucc 63840611543), (Int.negSucc 275197274231), (Int.negSucc 98193028367), (Int.ofNat 392269455096), (Int.negSucc 2858247407), (Int.negSucc 81723839)], [(Int.ofNat 89032414884), (Int.ofNat 278595082572), (Int.ofNat 152628087996), (Int.negSucc 145293638075), (Int.negSucc 95374918487), (Int.ofNat 2965374432)], [(Int.negSucc 78215897195), (Int.negSucc 161261001455), (Int.negSucc 157732957283), (Int.negSucc 224382461039), (Int.ofNat 146016678408), (Int.ofNat 4966855728)], [(Int.ofNat 42057625260), (Int.ofNat 72268272408), (Int.ofNat 105180191844), (Int.ofNat 250746687660), (Int.negSucc 18531802931), (Int.negSucc 9057171959)], [(Int.negSucc 12899288483), (Int.negSucc 36097571891), (Int.negSucc 47981616671), (Int.negSucc 88968247667), (Int.negSucc 69493871279), (Int.negSucc 2183766479)], [(Int.ofNat 1949805384), (Int.ofNat 15134291124), (Int.ofNat 18460768236), (Int.ofNat 8041368168), (Int.ofNat 35113813992), (Int.ofNat 5993415504)], [(Int.negSucc 92280815), (Int.negSucc 3769392923), (Int.negSucc 5189337791), (Int.ofNat 2224825200), (Int.negSucc 4328325503), (Int.negSucc 1713353471)], [(Int.ofNat 0), (Int.ofNat 441539424), (Int.ofNat 606346776), (Int.negSucc 553464143)]]

theorem h0n79_arithmetic : BiPoly.mul h0p8 h0p78=h0p79 := by
  decide +kernel

theorem h0n79 : h0e79.toBi mapPolyEnv=h0p79 := by
  change BiPoly.mul (h0e8.toBi mapPolyEnv) (h0e78.toBi mapPolyEnv)=h0p79
  rw [h0n8, h0n78]
  exact h0n79_arithmetic

#print axioms h0n79_arithmetic
end StackSorting.RationalLift
