import Horner0Base
import Horner0Node040
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p100 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 1416784013), (Int.negSucc 3651047027), (Int.ofNat 7350461370)], [(Int.ofNat 0), (Int.ofNat 6918842142), (Int.ofNat 20110797540), (Int.negSucc 32246251577), (Int.ofNat 2012886216)], [(Int.ofNat 0), (Int.negSucc 15960152885), (Int.negSucc 36879012785), (Int.ofNat 49209768480), (Int.negSucc 352173185), (Int.negSucc 10215479)], [(Int.ofNat 0), (Int.ofNat 22258103721), (Int.ofNat 25132563201), (Int.negSucc 12108104402), (Int.negSucc 12107200712), (Int.ofNat 370671804)], [(Int.ofNat 0), (Int.negSucc 19553974298), (Int.negSucc 1207301765), (Int.negSucc 37018635788), (Int.ofNat 17941656318), (Int.ofNat 620856966)], [(Int.ofNat 0), (Int.ofNat 10514406315), (Int.negSucc 2961744527), (Int.ofNat 32218537017), (Int.negSucc 1750402118), (Int.negSucc 1132146494)], [(Int.ofNat 0), (Int.negSucc 3224822120), (Int.negSucc 2574748730), (Int.negSucc 6845906705), (Int.negSucc 8550248504), (Int.negSucc 272970809)], [(Int.ofNat 0), (Int.ofNat 487451346), (Int.ofNat 2808670089), (Int.negSucc 1002148118), (Int.ofNat 4014638280), (Int.ofNat 749176938)], [(Int.ofNat 0), (Int.negSucc 23070203), (Int.negSucc 896207822), (Int.ofNat 495081198), (Int.negSucc 433956095), (Int.negSucc 214169183)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 110384856), (Int.negSucc 69183017)]]

theorem h0n100_arithmetic : BiPoly.mul h0p99 h0p40=h0p100 := by
  decide +kernel

theorem h0n100 : h0e100.toBi mapPolyEnv=h0p100 := by
  change BiPoly.mul (h0e99.toBi mapPolyEnv) (h0e40.toBi mapPolyEnv)=h0p100
  rw [h0n99, h0n40]
  exact h0n100_arithmetic

#print axioms h0n100_arithmetic
end StackSorting.RationalLift
