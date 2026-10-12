import Horner0Base
import Horner0Node048
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p49 : BiPoly.Poly := [[(Int.ofNat 2833568028), (Int.ofNat 12969230112), (Int.negSucc 96734627), (Int.negSucc 29401845479)], [(Int.negSucc 13837684283), (Int.negSucc 67896963647), (Int.negSucc 15950687003), (Int.ofNat 124959233880), (Int.negSucc 8051544863)], [(Int.ofNat 31920305772), (Int.ofNat 137598637116), (Int.ofNat 49096514184), (Int.negSucc 196134727547), (Int.ofNat 1429123704), (Int.ofNat 40861920)], [(Int.negSucc 44516207441), (Int.negSucc 139297541285), (Int.negSucc 76314043997), (Int.ofNat 72646819038), (Int.ofNat 47687459244), (Int.negSucc 1482687215)], [(Int.ofNat 39107948598), (Int.ofNat 80630500728), (Int.ofNat 78866478642), (Int.ofNat 112191230520), (Int.negSucc 73008339203), (Int.negSucc 2483427863)], [(Int.negSucc 21028812629), (Int.negSucc 36134136203), (Int.negSucc 52590095921), (Int.negSucc 125373343829), (Int.ofNat 9265901466), (Int.ofNat 4528585980)], [(Int.ofNat 6449644242), (Int.ofNat 18048785946), (Int.ofNat 23990808336), (Int.ofNat 44484123834), (Int.ofNat 34746935640), (Int.ofNat 1091883240)], [(Int.negSucc 974902691), (Int.negSucc 7567145561), (Int.negSucc 9230384117), (Int.negSucc 4020684083), (Int.negSucc 17556906995), (Int.negSucc 2996707751)], [(Int.ofNat 46140408), (Int.ofNat 1884696462), (Int.ofNat 2594668896), (Int.negSucc 1112412599), (Int.ofNat 2164162752), (Int.ofNat 856676736)], [(Int.ofNat 0), (Int.negSucc 220769711), (Int.negSucc 303173387), (Int.ofNat 276732072)]]

theorem h0n49_arithmetic : BiPoly.mul h0p8 h0p48=h0p49 := by
  decide +kernel

theorem h0n49 : h0e49.toBi mapPolyEnv=h0p49 := by
  change BiPoly.mul (h0e8.toBi mapPolyEnv) (h0e48.toBi mapPolyEnv)=h0p49
  rw [h0n8, h0n48]
  exact h0n49_arithmetic

#print axioms h0n49_arithmetic
end StackSorting.RationalLift
