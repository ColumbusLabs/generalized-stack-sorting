import BivariateRowEquality
import Horner2Base
import Horner2Node025
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p26 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 1836152082144), (Int.ofNat 13912517359008), (Int.ofNat 21477195134496), (Int.negSucc 28703961884447), (Int.negSucc 38104791742079)], [(Int.ofNat 0), (Int.negSucc 15121329172847), (Int.negSucc 114572142744479), (Int.negSucc 177300144662687), (Int.ofNat 210989844143136), (Int.ofNat 218536645043664), (Int.negSucc 2672714937023)], [(Int.ofNat 0), (Int.ofNat 58277099359584), (Int.ofNat 426973986561888), (Int.ofNat 638664023664576), (Int.negSucc 676072063758239), (Int.negSucc 537594923180735), (Int.negSucc 86481651263327), (Int.ofNat 7353289696896)], [(Int.ofNat 0), (Int.negSucc 138941307721727), (Int.negSucc 949551527253023), (Int.negSucc 1347009740017631), (Int.ofNat 1068558126451488), (Int.ofNat 743834832255072), (Int.ofNat 468188639700768), (Int.negSucc 43205127680447), (Int.ofNat 1406284349184)], [(Int.ofNat 0), (Int.ofNat 226993301556792), (Int.ofNat 1407113702434872), (Int.ofNat 1902364004771088), (Int.negSucc 510510396070895), (Int.negSucc 768296665049063), (Int.negSucc 931313850570791), (Int.ofNat 9650101350240), (Int.ofNat 563466456960), (Int.negSucc 7191697919)], [(Int.ofNat 0), (Int.negSucc 265140791506367), (Int.negSucc 1481346044531111), (Int.negSucc 1978379485108271), (Int.negSucc 1042949611751663), (Int.ofNat 725425340639760), (Int.ofNat 758672605776696), (Int.ofNat 257848911749424), (Int.negSucc 18901198209599), (Int.ofNat 259318473216)], [(Int.ofNat 0), (Int.ofNat 224324998861608), (Int.ofNat 1165792495149840), (Int.ofNat 1642060464172560), (Int.ofNat 2204053710295440), (Int.negSucc 254408441830631), (Int.negSucc 51006603123743), (Int.negSucc 503005428921551), (Int.ofNat 8963763258816), (Int.ofNat 533656863744)], [(Int.ofNat 0), (Int.negSucc 136745916011567), (Int.negSucc 718675828041191), (Int.negSucc 1151877174894695), (Int.negSucc 2011205943897311), (Int.negSucc 690202949735135), (Int.negSucc 285441693915191), (Int.ofNat 267346356399192), (Int.ofNat 60548066707776), (Int.negSucc 2055788875391)], [(Int.ofNat 0), (Int.ofNat 58827730382088), (Int.ofNat 357841633429824), (Int.ofNat 695216080003128), (Int.ofNat 1103927396925912), (Int.ofNat 1183488263334672), (Int.ofNat 238160575315704), (Int.ofNat 143306968627368), (Int.negSucc 84642288918071), (Int.negSucc 2424694142303)], [(Int.ofNat 0), (Int.negSucc 17164652772527), (Int.negSucc 142612312321847), (Int.negSucc 353196112106903), (Int.negSucc 425454598318127), (Int.negSucc 834608343966239), (Int.negSucc 256388146903199), (Int.negSucc 208832251853879), (Int.ofNat 11108803673280), (Int.ofNat 4971429260928)], [(Int.ofNat 0), (Int.ofNat 3160605146232), (Int.ofNat 43081502773776), (Int.ofNat 143449354274976), (Int.ofNat 148751163088224), (Int.ofNat 302485840940112), (Int.ofNat 238978322893968), (Int.ofNat 91953819150048), (Int.ofNat 36694505517120), (Int.ofNat 312774338304)], [(Int.ofNat 0), (Int.negSucc 317886709487), (Int.negSucc 9059741463575), (Int.negSucc 43388331736727), (Int.negSucc 56068508201567), (Int.negSucc 55030084910927), (Int.negSucc 113351497053407), (Int.negSucc 34392055551551), (Int.negSucc 22269239834687), (Int.negSucc 2924495725823)], [(Int.ofNat 0), (Int.ofNat 11996506080), (Int.ofNat 1173000893544), (Int.ofNat 8995136865768), (Int.ofNat 18028612522152), (Int.ofNat 5429044130400), (Int.ofNat 24171010774560), (Int.ofNat 14242434853536), (Int.ofNat 5630035675680), (Int.ofNat 1212815099520)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 71242247519), (Int.negSucc 1144823382647), (Int.negSucc 3735284007455), (Int.negSucc 1329181457759), (Int.negSucc 1321724794751), (Int.negSucc 3208059958175), (Int.negSucc 1041288856703), (Int.negSucc 123361449983)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 69553022976), (Int.ofNat 408143992320), (Int.ofNat 437765049504), (Int.negSucc 275322885407), (Int.ofNat 240949655424), (Int.ofNat 123361449984)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 15895419263), (Int.negSucc 53619322463), (Int.ofNat 39849418368)]]

theorem h2n26_arithmetic_row0 :
    (BiPoly.mul h2p4 h2p25).getD 0 []=h2p26.getD 0 [] := by
  decide +kernel

theorem h2n26_arithmetic_row1 :
    (BiPoly.mul h2p4 h2p25).getD 1 []=h2p26.getD 1 [] := by
  decide +kernel

theorem h2n26_arithmetic_row2 :
    (BiPoly.mul h2p4 h2p25).getD 2 []=h2p26.getD 2 [] := by
  decide +kernel

theorem h2n26_arithmetic_row3 :
    (BiPoly.mul h2p4 h2p25).getD 3 []=h2p26.getD 3 [] := by
  decide +kernel

theorem h2n26_arithmetic_row4 :
    (BiPoly.mul h2p4 h2p25).getD 4 []=h2p26.getD 4 [] := by
  decide +kernel

theorem h2n26_arithmetic_row5 :
    (BiPoly.mul h2p4 h2p25).getD 5 []=h2p26.getD 5 [] := by
  decide +kernel

theorem h2n26_arithmetic_row6 :
    (BiPoly.mul h2p4 h2p25).getD 6 []=h2p26.getD 6 [] := by
  decide +kernel

theorem h2n26_arithmetic_row7 :
    (BiPoly.mul h2p4 h2p25).getD 7 []=h2p26.getD 7 [] := by
  decide +kernel

theorem h2n26_arithmetic_row8 :
    (BiPoly.mul h2p4 h2p25).getD 8 []=h2p26.getD 8 [] := by
  decide +kernel

theorem h2n26_arithmetic_row9 :
    (BiPoly.mul h2p4 h2p25).getD 9 []=h2p26.getD 9 [] := by
  decide +kernel

theorem h2n26_arithmetic_row10 :
    (BiPoly.mul h2p4 h2p25).getD 10 []=h2p26.getD 10 [] := by
  decide +kernel

theorem h2n26_arithmetic_row11 :
    (BiPoly.mul h2p4 h2p25).getD 11 []=h2p26.getD 11 [] := by
  decide +kernel

theorem h2n26_arithmetic_row12 :
    (BiPoly.mul h2p4 h2p25).getD 12 []=h2p26.getD 12 [] := by
  decide +kernel

theorem h2n26_arithmetic_row13 :
    (BiPoly.mul h2p4 h2p25).getD 13 []=h2p26.getD 13 [] := by
  decide +kernel

theorem h2n26_arithmetic_row14 :
    (BiPoly.mul h2p4 h2p25).getD 14 []=h2p26.getD 14 [] := by
  decide +kernel

theorem h2n26_arithmetic_row15 :
    (BiPoly.mul h2p4 h2p25).getD 15 []=h2p26.getD 15 [] := by
  decide +kernel

theorem h2n26_arithmetic : BiPoly.mul h2p4 h2p25=h2p26 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<16 at hk
    have hf : ∀ j : Fin 16, (BiPoly.mul h2p4 h2p25).getD j.val []=h2p26.getD j.val [] :=
      (fun j => Fin.cases h2n26_arithmetic_row0 (fun j => Fin.cases h2n26_arithmetic_row1 (fun j => Fin.cases h2n26_arithmetic_row2 (fun j => Fin.cases h2n26_arithmetic_row3 (fun j => Fin.cases h2n26_arithmetic_row4 (fun j => Fin.cases h2n26_arithmetic_row5 (fun j => Fin.cases h2n26_arithmetic_row6 (fun j => Fin.cases h2n26_arithmetic_row7 (fun j => Fin.cases h2n26_arithmetic_row8 (fun j => Fin.cases h2n26_arithmetic_row9 (fun j => Fin.cases h2n26_arithmetic_row10 (fun j => Fin.cases h2n26_arithmetic_row11 (fun j => Fin.cases h2n26_arithmetic_row12 (fun j => Fin.cases h2n26_arithmetic_row13 (fun j => Fin.cases h2n26_arithmetic_row14 (fun j => Fin.cases h2n26_arithmetic_row15 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h2n26 : h2e26.toBi mapPolyEnv=h2p26 := by
  change BiPoly.mul (h2e4.toBi mapPolyEnv) (h2e25.toBi mapPolyEnv)=h2p26
  rw [h2n4, h2n25]
  exact h2n26_arithmetic

#print axioms h2n26_arithmetic
end StackSorting.RationalLift
