import Horner5Node335
import Horner5Node341
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p342 : BiPoly.Poly := [[(Int.negSucc 8602847999), (Int.negSucc 8471018879), (Int.ofNat 119096893080), (Int.ofNat 65423465640), (Int.negSucc 104793221879), (Int.negSucc 147009227399)], [(Int.ofNat 46034795520), (Int.ofNat 27195508224), (Int.negSucc 650382967151), (Int.negSucc 341469210167), (Int.ofNat 495981165888), (Int.ofNat 590788260072), (Int.negSucc 40257724319)], [(Int.negSucc 103549613759), (Int.negSucc 34150624991), (Int.ofNat 1489242535632), (Int.ofNat 870434490288), (Int.negSucc 1010048151071), (Int.negSucc 934666907927), (Int.ofNat 5773875336), (Int.ofNat 204309600)], [(Int.ofNat 126662598720), (Int.ofNat 31264770528), (Int.negSucc 1879801121867), (Int.negSucc 1411271269967), (Int.ofNat 882595094472), (Int.ofNat 553816918728), (Int.ofNat 229204908900), (Int.negSucc 7413436079)], [(Int.negSucc 90824833279), (Int.negSucc 37657360383), (Int.ofNat 1435809403312), (Int.ofNat 1538247567560), (Int.ofNat 218314583936), (Int.ofNat 56894749592), (Int.negSucc 359214014847), (Int.negSucc 12417139319)], [(Int.ofNat 38132920320), (Int.ofNat 37077870080), (Int.negSucc 676450008023), (Int.negSucc 1143269372243), (Int.negSucc 1168111932663), (Int.negSucc 228608322031), (Int.ofNat 87254814064), (Int.ofNat 22642929900)], [(Int.negSucc 8682503999), (Int.negSucc 19839200799), (Int.ofNat 188903783920), (Int.ofNat 589505057968), (Int.ofNat 1041390680024), (Int.ofNat 254470612944), (Int.ofNat 139695877776), (Int.ofNat 5459416200)], [(Int.ofNat 829484480), (Int.ofNat 5053723680), (Int.negSucc 28763503387), (Int.negSucc 217124647511), (Int.negSucc 442397881295), (Int.negSucc 231676824647), (Int.negSucc 105395588015), (Int.negSucc 14983538759)], [(Int.ofNat 0), (Int.negSucc 473667455), (Int.ofNat 2603831832), (Int.ofNat 62401640592), (Int.ofNat 89145120072), (Int.ofNat 110471044872), (Int.ofNat 33877375176), (Int.ofNat 4283383680)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 258847343), (Int.negSucc 15111226379), (Int.negSucc 639903551), (Int.negSucc 27491815223), (Int.negSucc 5449674239)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2137917024), (Int.negSucc 2340610631), (Int.ofNat 3498871680)]]

theorem h5n342_arithmetic : BiPoly.add h5p335 h5p341=h5p342 := by
  decide +kernel

theorem h5n342 : h5e342.toBi mapPolyEnv=h5p342 := by
  change BiPoly.add (h5e335.toBi mapPolyEnv) (h5e341.toBi mapPolyEnv)=h5p342
  rw [h5n335, h5n341]
  exact h5n342_arithmetic

#print axioms h5n342_arithmetic
end StackSorting.RationalLift
