import Horner4Node102
import Horner4Node107
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p108 : BiPoly.Poly := [[(Int.ofNat 6452136000), (Int.ofNat 13590400104), (Int.negSucc 54709297559), (Int.negSucc 14410718855), (Int.ofNat 88205536440)], [(Int.negSucc 28073960639), (Int.negSucc 48968055719), (Int.ofNat 263985009912), (Int.ofNat 101935278792), (Int.negSucc 378903474071), (Int.ofNat 24154634592)], [(Int.ofNat 49588249680), (Int.ofNat 68527314192), (Int.negSucc 468014774015), (Int.negSucc 241827777311), (Int.ofNat 588003105528), (Int.negSucc 4266940151), (Int.negSucc 122585759)], [(Int.negSucc 45408699359), (Int.negSucc 41630385035), (Int.ofNat 371389525104), (Int.ofNat 315239819952), (Int.negSucc 197717075447), (Int.negSucc 143803721339), (Int.ofNat 4448061648)], [(Int.ofNat 22709925600), (Int.ofNat 1010272452), (Int.negSucc 112240088531), (Int.negSucc 243345064931), (Int.negSucc 368989893131), (Int.ofNat 217783303680), (Int.ofNat 7450283592)], [(Int.negSucc 5889764639), (Int.ofNat 13566086268), (Int.negSucc 2676846971), (Int.ofNat 94395430404), (Int.ofNat 392510862576), (Int.negSucc 25533411407), (Int.negSucc 13585757939)], [(Int.ofNat 622113360), (Int.negSucc 7597906235), (Int.negSucc 4889521583), (Int.negSucc 12255499787), (Int.negSucc 126946058459), (Int.negSucc 103694865299), (Int.negSucc 3275649719)], [(Int.ofNat 0), (Int.ofNat 1594554792), (Int.ofNat 10465312908), (Int.ofNat 4586159376), (Int.ofNat 537875100), (Int.ofNat 51172367112), (Int.ofNat 8990123256)], [(Int.ofNat 0), (Int.negSucc 92280815), (Int.negSucc 3709756187), (Int.negSucc 4605281099), (Int.ofNat 8653648104), (Int.negSucc 6064149887), (Int.negSucc 2570030207)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 441539424), (Int.ofNat 995551128), (Int.negSucc 1704914135)]]

theorem h4n108_arithmetic : BiPoly.add h4p102 h4p107=h4p108 := by
  decide +kernel

theorem h4n108 : h4e108.toBi mapPolyEnv=h4p108 := by
  change BiPoly.add (h4e102.toBi mapPolyEnv) (h4e107.toBi mapPolyEnv)=h4p108
  rw [h4n102, h4n107]
  exact h4n108_arithmetic

#print axioms h4n108_arithmetic
end StackSorting.RationalLift
