import Horner2Node036
import Horner2Node038
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p39 : BiPoly.Poly := [[(Int.ofNat 6452136000), (Int.ofNat 38147989680), (Int.ofNat 25576925760), (Int.negSucc 98006151599)], [(Int.negSucc 28073960639), (Int.negSucc 168894652847), (Int.negSucc 167628253151), (Int.ofNat 419540735664), (Int.negSucc 26838482879)], [(Int.ofNat 49588249680), (Int.ofNat 345169964216), (Int.ofNat 362743282240), (Int.negSucc 652248944199), (Int.ofNat 3590218992), (Int.ofNat 136206400)], [(Int.negSucc 45408699359), (Int.negSucc 427437516199), (Int.negSucc 331338815031), (Int.ofNat 223522871192), (Int.ofNat 157438323080), (Int.negSucc 4942290719)], [(Int.ofNat 22709925600), (Int.ofNat 339945826968), (Int.ofNat 143334167000), (Int.ofNat 412798909936), (Int.negSucc 235754973175), (Int.negSucc 8278092879)], [(Int.negSucc 5889764639), (Int.negSucc 168683623191), (Int.negSucc 77512817599), (Int.negSucc 428518276887), (Int.ofNat 36228721768), (Int.ofNat 15095286600)], [(Int.ofNat 622113360), (Int.ofNat 48299010528), (Int.ofNat 78437321872), (Int.ofNat 137303867888), (Int.ofNat 103409129432), (Int.ofNat 3639610800)], [(Int.ofNat 0), (Int.negSucc 6854601871), (Int.negSucc 44067718119), (Int.negSucc 11747314295), (Int.negSucc 57023410991), (Int.negSucc 9989025839)], [(Int.ofNat 0), (Int.ofNat 307602720), (Int.ofNat 12101355192), (Int.negSucc 2432194655), (Int.ofNat 10234579392), (Int.ofNat 2855589120)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1471798079), (Int.ofNat 870105168), (Int.negSucc 874717919)]]

theorem h2n39_arithmetic : BiPoly.add h2p36 h2p38=h2p39 := by
  decide +kernel

theorem h2n39 : h2e39.toBi mapPolyEnv=h2p39 := by
  change BiPoly.add (h2e36.toBi mapPolyEnv) (h2e38.toBi mapPolyEnv)=h2p39
  rw [h2n36, h2n38]
  exact h2n39_arithmetic

#print axioms h2n39_arithmetic
end StackSorting.RationalLift
