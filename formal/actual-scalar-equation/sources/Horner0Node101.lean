import Horner0Node098
import Horner0Node100
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p101 : BiPoly.Poly := [[(Int.negSucc 3226067999), (Int.negSucc 11045552093), (Int.ofNat 7900803612), (Int.ofNat 7350461370)], [(Int.ofNat 14036980320), (Int.ofNat 45240554286), (Int.negSucc 30147059483), (Int.negSucc 27041608889), (Int.ofNat 2012886216)], [(Int.negSucc 24794124839), (Int.negSucc 82144115753), (Int.ofNat 27609431334), (Int.ofNat 47269117380), (Int.ofNat 200538558), (Int.negSucc 10215479)], [(Int.ofNat 22704349680), (Int.ofNat 87589503681), (Int.ofNat 23251549377), (Int.negSucc 43148843978), (Int.negSucc 10111690832), (Int.ofNat 370671804)], [(Int.negSucc 11354962799), (Int.negSucc 59167059122), (Int.negSucc 64825706825), (Int.ofNat 3372814503), (Int.ofNat 16208100786), (Int.ofNat 620856966)], [(Int.ofNat 2944882320), (Int.ofNat 24760175811), (Int.ofNat 55539627792), (Int.ofNat 31687428681), (Int.negSucc 8195415542), (Int.negSucc 1132146494)], [(Int.negSucc 311056679), (Int.negSucc 5875513244), (Int.negSucc 24628418126), (Int.negSucc 29858462609), (Int.negSucc 3253156520), (Int.negSucc 272970809)], [(Int.ofNat 0), (Int.ofNat 665076642), (Int.ofNat 6118061889), (Int.ofNat 11552496489), (Int.ofNat 5762088576), (Int.ofNat 749176938)], [(Int.ofNat 0), (Int.negSucc 23070203), (Int.negSucc 972166598), (Int.negSucc 1589362793), (Int.negSucc 2658205151), (Int.negSucc 214169183)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 110384856), (Int.negSucc 43015481), (Int.ofNat 437358960)]]

theorem h0n101_arithmetic : BiPoly.add h0p98 h0p100=h0p101 := by
  decide +kernel

theorem h0n101 : h0e101.toBi mapPolyEnv=h0p101 := by
  change BiPoly.add (h0e98.toBi mapPolyEnv) (h0e100.toBi mapPolyEnv)=h0p101
  rw [h0n98, h0n100]
  exact h0n101_arithmetic

#print axioms h0n101_arithmetic
end StackSorting.RationalLift
