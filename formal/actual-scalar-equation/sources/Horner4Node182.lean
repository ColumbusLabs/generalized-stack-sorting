import Horner4Node179
import Horner4Node181
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p182 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 9678204000), (Int.ofNat 33136656282), (Int.negSucc 23702410835), (Int.negSucc 22051384109)], [(Int.ofNat 0), (Int.negSucc 42110940959), (Int.negSucc 135721662857), (Int.ofNat 90441178452), (Int.ofNat 81124826670), (Int.negSucc 6038658647)], [(Int.ofNat 0), (Int.ofNat 74382374520), (Int.ofNat 246432347262), (Int.negSucc 82828294001), (Int.negSucc 141807352139), (Int.negSucc 601615673), (Int.ofNat 30646440)], [(Int.ofNat 0), (Int.negSucc 68113049039), (Int.negSucc 262768511042), (Int.negSucc 69754648130), (Int.ofNat 129446531937), (Int.ofNat 30335072499), (Int.negSucc 1112015411)], [(Int.ofNat 0), (Int.ofNat 34064888400), (Int.ofNat 177501177369), (Int.ofNat 194477120478), (Int.negSucc 10118443508), (Int.negSucc 48624302357), (Int.negSucc 1862570897)], [(Int.ofNat 0), (Int.negSucc 8834646959), (Int.negSucc 74280527432), (Int.negSucc 166618883375), (Int.negSucc 95062286042), (Int.ofNat 24586246629), (Int.ofNat 3396439485)], [(Int.ofNat 0), (Int.ofNat 933170040), (Int.ofNat 17626539735), (Int.ofNat 73885254381), (Int.ofNat 89575387830), (Int.ofNat 9759469563), (Int.ofNat 818912430)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1995229925), (Int.negSucc 18354185666), (Int.negSucc 34657489466), (Int.negSucc 17286265727), (Int.negSucc 2247530813)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 69210612), (Int.ofNat 2916499797), (Int.ofNat 4768088382), (Int.ofNat 7974615456), (Int.ofNat 642507552)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 331154567), (Int.ofNat 129046446), (Int.negSucc 1312076879)]]

theorem h4n182_arithmetic : BiPoly.add h4p179 h4p181=h4p182 := by
  decide +kernel

theorem h4n182 : h4e182.toBi mapPolyEnv=h4p182 := by
  change BiPoly.add (h4e179.toBi mapPolyEnv) (h4e181.toBi mapPolyEnv)=h4p182
  rw [h4n179, h4n181]
  exact h4n182_arithmetic

#print axioms h4n182_arithmetic
end StackSorting.RationalLift
