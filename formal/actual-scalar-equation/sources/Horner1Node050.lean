import Horner1Base
import Horner1Node024
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p50 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 8500704083), (Int.negSucc 21906282167), (Int.ofNat 44102768220)], [(Int.ofNat 0), (Int.ofNat 41513052852), (Int.ofNat 120664785240), (Int.negSucc 193477509467), (Int.ofNat 12077317296)], [(Int.ofNat 0), (Int.negSucc 95760917315), (Int.negSucc 221274076715), (Int.ofNat 295258610880), (Int.negSucc 2113039115), (Int.negSucc 61292879)], [(Int.ofNat 0), (Int.ofNat 133548622326), (Int.ofNat 150795379206), (Int.negSucc 72648626417), (Int.negSucc 72643204277), (Int.ofNat 2224030824)], [(Int.ofNat 0), (Int.negSucc 117323845793), (Int.negSucc 7243810595), (Int.negSucc 222111814733), (Int.ofNat 107649937908), (Int.ofNat 3725141796)], [(Int.ofNat 0), (Int.ofNat 63086437890), (Int.negSucc 17770467167), (Int.ofNat 193311222102), (Int.negSucc 10502412713), (Int.negSucc 6792878969)], [(Int.ofNat 0), (Int.negSucc 19348932725), (Int.negSucc 15448492385), (Int.negSucc 41075440235), (Int.negSucc 51301491029), (Int.negSucc 1637824859)], [(Int.ofNat 0), (Int.ofNat 2924708076), (Int.ofNat 16852020534), (Int.negSucc 6012888713), (Int.ofNat 24087829680), (Int.ofNat 4495061628)], [(Int.ofNat 0), (Int.negSucc 138421223), (Int.negSucc 5377246937), (Int.ofNat 2970487188), (Int.negSucc 2603736575), (Int.negSucc 1285015103)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 662309136), (Int.negSucc 415098107)]]

theorem h1n50_arithmetic : BiPoly.mul h1p49 h1p24=h1p50 := by
  decide +kernel

theorem h1n50 : h1e50.toBi mapPolyEnv=h1p50 := by
  change BiPoly.mul (h1e49.toBi mapPolyEnv) (h1e24.toBi mapPolyEnv)=h1p50
  rw [h1n49, h1n24]
  exact h1n50_arithmetic

#print axioms h1n50_arithmetic
end StackSorting.RationalLift
