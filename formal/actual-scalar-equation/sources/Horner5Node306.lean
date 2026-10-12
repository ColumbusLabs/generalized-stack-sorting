import Horner5Node301
import Horner5Node305
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p306 : BiPoly.Poly := [[(Int.ofNat 8602848000), (Int.ofNat 8471018880), (Int.negSucc 102095484911), (Int.negSucc 4609493135), (Int.ofNat 60400249776), (Int.ofNat 58803690960)], [(Int.negSucc 46034795519), (Int.negSucc 27195508223), (Int.ofNat 550355453280), (Int.negSucc 26699030351), (Int.negSucc 262150180991), (Int.negSucc 227987875727), (Int.ofNat 16103089728)], [(Int.ofNat 103549613760), (Int.ofNat 34150624992), (Int.negSucc 1214694595295), (Int.ofNat 4965068256), (Int.ofNat 475124063808), (Int.ofNat 372530398992), (Int.negSucc 1425211343), (Int.negSucc 81723839)], [(Int.negSucc 126662598719), (Int.negSucc 31264770527), (Int.ofNat 1421182042584), (Int.ofNat 400035113472), (Int.negSucc 448371378287), (Int.negSucc 267459335567), (Int.negSucc 88489147751), (Int.ofNat 2965374432)], [(Int.ofNat 90824833280), (Int.ofNat 37657360384), (Int.negSucc 934064467071), (Int.negSucc 987521496367), (Int.ofNat 95099413888), (Int.ofNat 26742595504), (Int.ofNat 140911917088), (Int.ofNat 4966855728)], [(Int.negSucc 38132920319), (Int.negSucc 37077870079), (Int.ofNat 315629440656), (Int.ofNat 1038149809608), (Int.ofNat 372806793328), (Int.ofNat 78290579072), (Int.negSucc 45213947103), (Int.negSucc 9057171959)], [(Int.ofNat 8682504000), (Int.ofNat 19839200800), (Int.negSucc 24033042687), (Int.negSucc 555451142079), (Int.negSucc 541720370575), (Int.negSucc 90721575839), (Int.negSucc 47403003935), (Int.negSucc 2183766479)], [(Int.negSucc 829484479), (Int.negSucc 5053723679), (Int.negSucc 15783778215), (Int.ofNat 146674205520), (Int.ofNat 338568737184), (Int.ofNat 92923960656), (Int.ofNat 44954155680), (Int.ofNat 5993415504)], [(Int.ofNat 0), (Int.ofNat 473667456), (Int.ofNat 3522426768), (Int.negSucc 17666263199), (Int.negSucc 96357377999), (Int.negSucc 63028886735), (Int.negSucc 17109748559), (Int.negSucc 1713353471)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 17995103), (Int.ofNat 3032114232), (Int.ofNat 6086455872), (Int.ofNat 23114538288), (Int.ofNat 2879644032)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 813298751), (Int.ofNat 1510414416), (Int.negSucc 3498871679)]]

theorem h5n306_arithmetic : BiPoly.add h5p301 h5p305=h5p306 := by
  decide +kernel

theorem h5n306 : h5e306.toBi mapPolyEnv=h5p306 := by
  change BiPoly.add (h5e301.toBi mapPolyEnv) (h5e305.toBi mapPolyEnv)=h5p306
  rw [h5n301, h5n305]
  exact h5n306_arithmetic

#print axioms h5n306_arithmetic
end StackSorting.RationalLift
