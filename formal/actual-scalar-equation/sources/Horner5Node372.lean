import Horner5Node365
import Horner5Node371
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p372 : BiPoly.Poly := [[(Int.ofNat 2150712000), (Int.ofNat 2117754720), (Int.negSucc 31191007283), (Int.negSucc 21423697451), (Int.ofNat 29897719812), (Int.ofNat 44102768220)], [(Int.negSucc 11508698879), (Int.negSucc 6798877055), (Int.ofNat 170931367944), (Int.ofNat 116047989252), (Int.negSucc 143481206879), (Int.negSucc 177930430379), (Int.ofNat 12077317296)], [(Int.ofNat 25887403440), (Int.ofNat 8537656248), (Int.negSucc 395189628935), (Int.negSucc 290558585783), (Int.ofNat 297089045040), (Int.ofNat 280511436060), (Int.negSucc 1805857499), (Int.negSucc 61292879)], [(Int.negSucc 31665649679), (Int.negSucc 7816192631), (Int.ofNat 508168537074), (Int.ofNat 437087497200), (Int.negSucc 256834083299), (Int.negSucc 162317361611), (Int.negSucc 69027540653), (Int.ofNat 2224030824)], [(Int.ofNat 22706208320), (Int.ofNat 9414340096), (Int.negSucc 400764428847), (Int.negSucc 430455731155), (Int.negSucc 80696479135), (Int.negSucc 21193466155), (Int.ofNat 107995345192), (Int.ofNat 3725141796)], [(Int.negSucc 9533230079), (Int.negSucc 9269467519), (Int.ofNat 199180882620), (Int.ofNat 294577306614), (Int.ofNat 358303411444), (Int.ofNat 69678559088), (Int.negSucc 25317109095), (Int.negSucc 6792878969)], [(Int.ofNat 2170626000), (Int.ofNat 4959800200), (Int.negSucc 60965174415), (Int.negSucc 150214090815), (Int.negSucc 301986862459), (Int.negSucc 77263406327), (Int.negSucc 42615042263), (Int.negSucc 1637824859)], [(Int.negSucc 207371119), (Int.negSucc 1263430919), (Int.ofNat 10903149314), (Int.ofNat 60152032044), (Int.ofNat 119251899000), (Int.ofNat 69481944828), (Int.ofNat 31385683032), (Int.ofNat 4495061628)], [(Int.ofNat 0), (Int.ofNat 118416864), (Int.negSucc 1161479507), (Int.negSucc 19328358263), (Int.negSucc 21685258523), (Int.negSucc 31571274395), (Int.negSucc 9866646011), (Int.negSucc 1285015103)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 87782040), (Int.ofNat 4784399274), (Int.negSucc 293903471), (Int.ofNat 7237726884), (Int.ofNat 1576587744)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 644864111), (Int.ofNat 654335676), (Int.negSucc 874717919)]]

theorem h5n372_arithmetic : BiPoly.add h5p365 h5p371=h5p372 := by
  decide +kernel

theorem h5n372 : h5e372.toBi mapPolyEnv=h5p372 := by
  change BiPoly.add (h5e365.toBi mapPolyEnv) (h5e371.toBi mapPolyEnv)=h5p372
  rw [h5n365, h5n371]
  exact h5n372_arithmetic

#print axioms h5n372_arithmetic
end StackSorting.RationalLift
