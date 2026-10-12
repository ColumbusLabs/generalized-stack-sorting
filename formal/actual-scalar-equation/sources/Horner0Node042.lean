import Horner0Node038
import Horner0Node041
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p42 : BiPoly.Poly := [[(Int.ofNat 3226068000), (Int.ofNat 6795200052), (Int.negSucc 18853944695), (Int.ofNat 14700922740)], [(Int.negSucc 14036980319), (Int.negSucc 24484027859), (Int.ofNat 90479452104), (Int.negSucc 69697145843), (Int.ofNat 4025772432)], [(Int.ofNat 24794124840), (Int.ofNat 34263657096), (Int.negSucc 138246469691), (Int.ofNat 100360188060), (Int.negSucc 1257058115), (Int.negSucc 20430959)], [(Int.negSucc 22704349679), (Int.negSucc 20815192517), (Int.ofNat 52146140226), (Int.ofNat 6824530770), (Int.negSucc 26209911305), (Int.ofNat 741343608)], [(Int.ofNat 11354962800), (Int.ofNat 505136226), (Int.ofNat 61203801528), (Int.negSucc 114428721869), (Int.ofNat 37616868168), (Int.ofNat 1241713932)], [(Int.negSucc 2944882319), (Int.ofNat 6783043134), (Int.negSucc 64424861375), (Int.ofNat 64968182370), (Int.ofNat 2944209186), (Int.negSucc 2264292989)], [(Int.ofNat 311056680), (Int.negSucc 3798953117), (Int.ofNat 16904171934), (Int.ofNat 9320742492), (Int.negSucc 22397588993), (Int.negSucc 545941619)], [(Int.ofNat 0), (Int.ofNat 797277396), (Int.ofNat 2307948378), (Int.negSucc 14558940845), (Int.ofNat 6281826264), (Int.ofNat 1498353876)], [(Int.ofNat 0), (Int.negSucc 46140407), (Int.negSucc 1716456869), (Int.ofNat 3074606388), (Int.ofNat 1356336864), (Int.negSucc 428338367)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 220769712), (Int.negSucc 164533571), (Int.negSucc 437358959)]]

theorem h0n42_arithmetic : BiPoly.add h0p38 h0p41=h0p42 := by
  decide +kernel

theorem h0n42 : h0e42.toBi mapPolyEnv=h0p42 := by
  change BiPoly.add (h0e38.toBi mapPolyEnv) (h0e41.toBi mapPolyEnv)=h0p42
  rw [h0n38, h0n41]
  exact h0n42_arithmetic

#print axioms h0n42_arithmetic
end StackSorting.RationalLift
