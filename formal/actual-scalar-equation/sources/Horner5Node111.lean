import Horner5Node102
import Horner5Node110
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p111 : BiPoly.Poly := [[(Int.negSucc 6452135999), (Int.negSucc 6353264159), (Int.ofNat 93573021852), (Int.ofNat 64271092356), (Int.negSucc 89693159435), (Int.negSucc 132308304659)], [(Int.ofNat 34526096640), (Int.ofNat 20396631168), (Int.negSucc 512794103831), (Int.negSucc 348143967755), (Int.ofNat 430443620640), (Int.ofNat 533791291140), (Int.negSucc 36231951887)], [(Int.negSucc 77662210319), (Int.negSucc 25612968743), (Int.ofNat 1185568886808), (Int.ofNat 871675757352), (Int.negSucc 891267135119), (Int.negSucc 841534308179), (Int.ofNat 5417572500), (Int.ofNat 183878640)], [(Int.ofNat 94996949040), (Int.ofNat 23448577896), (Int.negSucc 1524505611221), (Int.negSucc 1311262491599), (Int.ofNat 770502249900), (Int.ofNat 486952084836), (Int.ofNat 207082621962), (Int.negSucc 6672092471)], [(Int.negSucc 68118624959), (Int.negSucc 28243020287), (Int.ofNat 1202293286544), (Int.ofNat 1291367193468), (Int.ofNat 242089437408), (Int.ofNat 63580398468), (Int.negSucc 323986035575), (Int.negSucc 11175425387)], [(Int.ofNat 28599690240), (Int.ofNat 27808402560), (Int.negSucc 597542647859), (Int.negSucc 883731919841), (Int.negSucc 1074910234331), (Int.negSucc 209035677263), (Int.ofNat 75951327288), (Int.ofNat 20378636910)], [(Int.negSucc 6511877999), (Int.negSucc 14879400599), (Int.ofNat 182895523248), (Int.ofNat 450642272448), (Int.ofNat 905960587380), (Int.ofNat 231790218984), (Int.ofNat 127845126792), (Int.ofNat 4913474580)], [(Int.ofNat 622113360), (Int.ofNat 3790292760), (Int.negSucc 32709447941), (Int.negSucc 180456096131), (Int.negSucc 357755696999), (Int.negSucc 208445834483), (Int.negSucc 94157049095), (Int.negSucc 13485184883)], [(Int.ofNat 0), (Int.negSucc 355250591), (Int.ofNat 3484438524), (Int.ofNat 57985074792), (Int.ofNat 65055775572), (Int.ofNat 94713823188), (Int.ofNat 29599938036), (Int.ofNat 3855045312)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 263346119), (Int.negSucc 14353197821), (Int.ofNat 881710416), (Int.negSucc 21713180651), (Int.negSucc 4729763231)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1934592336), (Int.negSucc 1963007027), (Int.ofNat 2624153760)]]

theorem h5n111_arithmetic : BiPoly.add h5p102 h5p110=h5p111 := by
  decide +kernel

theorem h5n111 : h5e111.toBi mapPolyEnv=h5p111 := by
  change BiPoly.add (h5e102.toBi mapPolyEnv) (h5e110.toBi mapPolyEnv)=h5p111
  rw [h5n102, h5n110]
  exact h5n111_arithmetic

#print axioms h5n111_arithmetic
end StackSorting.RationalLift
