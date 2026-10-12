import BivariateRowEquality
import Horner2Base
import Horner2Node016
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p17 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 1632135184128), (Int.ofNat 6756217401456), (Int.negSucc 12402717095663), (Int.negSucc 40306995225647), (Int.ofNat 54511021519920)], [(Int.ofNat 0), (Int.negSucc 13257944087831), (Int.negSucc 50165338171247), (Int.ofNat 108249984387216), (Int.ofNat 285923954337552), (Int.negSucc 411969780542807), (Int.ofNat 32568671465856)], [(Int.ofNat 0), (Int.ofNat 50378726163600), (Int.ofNat 157643018576496), (Int.negSucc 445755840757631), (Int.negSucc 820652005273679), (Int.ofNat 1216694476941696), (Int.negSucc 75582656993231), (Int.ofNat 5460813210240)], [(Int.ofNat 0), (Int.negSucc 118352351673431), (Int.negSucc 256733614462679), (Int.ofNat 1073902572759456), (Int.ofNat 1161497396700864), (Int.negSucc 1566735885892583), (Int.negSucc 296100567948311), (Int.ofNat 26124451777440), (Int.ofNat 168719924736)], [(Int.ofNat 0), (Int.ofNat 190304508997116), (Int.ofNat 186225003934308), (Int.negSucc 1597201378976807), (Int.negSucc 825279668818343), (Int.ofNat 236279066958108), (Int.ofNat 1410269428098900), (Int.negSucc 113824282850783), (Int.ofNat 4556259360576), (Int.negSucc 980686079)], [(Int.ofNat 0), (Int.negSucc 218351449762703), (Int.ofNat 70048037951604), (Int.ofNat 1466882455601016), (Int.ofNat 484124635084968), (Int.ofNat 1620761889788712), (Int.negSucc 1995787517073515), (Int.negSucc 44614123037351), (Int.ofNat 6964886892960), (Int.ofNat 16461114624)], [(Int.ofNat 0), (Int.ofNat 180962217005148), (Int.negSucc 290828926526759), (Int.negSucc 800957247595703), (Int.negSucc 875817391199687), (Int.negSucc 1681668437959403), (Int.ofNat 579410802861840), (Int.ofNat 615296083337064), (Int.negSucc 36516398666399), (Int.ofNat 729963419904)], [(Int.ofNat 0), (Int.negSucc 107675795520287), (Int.ofNat 300060340859340), (Int.ofNat 263959122899340), (Int.ofNat 1283844659520600), (Int.ofNat 552279807173664), (Int.ofNat 1249519176163404), (Int.negSucc 802859694035219), (Int.negSucc 10473422157143), (Int.ofNat 1951716886848)], [(Int.ofNat 0), (Int.ofNat 45030452526468), (Int.negSucc 170474956050527), (Int.negSucc 124381941877619), (Int.negSucc 949988146051115), (Int.negSucc 188281892012183), (Int.negSucc 1261671867523259), (Int.ofNat 117510784594308), (Int.ofNat 117843623304156), (Int.negSucc 2316431180015)], [(Int.ofNat 0), (Int.negSucc 12717971647127), (Int.ofNat 57025397706732), (Int.ofNat 132148899193212), (Int.ofNat 347404813970328), (Int.ofNat 407605171281120), (Int.ofNat 341247029514048), (Int.ofNat 450552426091020), (Int.negSucc 95282894762639), (Int.negSucc 5729647987871)], [(Int.ofNat 0), (Int.ofNat 2258078565636), (Int.negSucc 10019364195239), (Int.negSucc 95885111885759), (Int.negSucc 54080417267279), (Int.negSucc 339397030784663), (Int.ofNat 12372941130840), (Int.negSucc 314406755237231), (Int.negSucc 25419346779455), (Int.ofNat 5643847098432)], [(Int.ofNat 0), (Int.negSucc 218634181703), (Int.ofNat 288416646252), (Int.ofNat 39894050919204), (Int.ofNat 9488300618232), (Int.ofNat 111644632226952), (Int.ofNat 27575546576112), (Int.ofNat 55525831604928), (Int.ofNat 55202762755008), (Int.ofNat 2504412851904)], [(Int.ofNat 0), (Int.ofNat 8028430992), (Int.ofNat 201722349996), (Int.negSucc 9668032930331), (Int.negSucc 9846823436531), (Int.negSucc 9451087365167), (Int.negSucc 31687823434319), (Int.ofNat 6385520554128), (Int.negSucc 18629152728335), (Int.negSucc 3729890172095)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 25956019727), (Int.ofNat 1289742674508), (Int.ofNat 4526053772832), (Int.negSucc 2983541715215), (Int.ofNat 8679908872800), (Int.negSucc 1946964106223), (Int.ofNat 1458345441024), (Int.ofNat 925210874880)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 74557314431), (Int.negSucc 908978482655), (Int.ofNat 764534931984), (Int.negSucc 892557915119), (Int.ofNat 160089006528)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 71529386688), (Int.negSucc 44830595663)]]

theorem h2n17_arithmetic_row0 :
    (BiPoly.mul h2p13 h2p16).getD 0 []=h2p17.getD 0 [] := by
  decide +kernel

theorem h2n17_arithmetic_row1 :
    (BiPoly.mul h2p13 h2p16).getD 1 []=h2p17.getD 1 [] := by
  decide +kernel

theorem h2n17_arithmetic_row2 :
    (BiPoly.mul h2p13 h2p16).getD 2 []=h2p17.getD 2 [] := by
  decide +kernel

theorem h2n17_arithmetic_row3 :
    (BiPoly.mul h2p13 h2p16).getD 3 []=h2p17.getD 3 [] := by
  decide +kernel

theorem h2n17_arithmetic_row4 :
    (BiPoly.mul h2p13 h2p16).getD 4 []=h2p17.getD 4 [] := by
  decide +kernel

theorem h2n17_arithmetic_row5 :
    (BiPoly.mul h2p13 h2p16).getD 5 []=h2p17.getD 5 [] := by
  decide +kernel

theorem h2n17_arithmetic_row6 :
    (BiPoly.mul h2p13 h2p16).getD 6 []=h2p17.getD 6 [] := by
  decide +kernel

theorem h2n17_arithmetic_row7 :
    (BiPoly.mul h2p13 h2p16).getD 7 []=h2p17.getD 7 [] := by
  decide +kernel

theorem h2n17_arithmetic_row8 :
    (BiPoly.mul h2p13 h2p16).getD 8 []=h2p17.getD 8 [] := by
  decide +kernel

theorem h2n17_arithmetic_row9 :
    (BiPoly.mul h2p13 h2p16).getD 9 []=h2p17.getD 9 [] := by
  decide +kernel

theorem h2n17_arithmetic_row10 :
    (BiPoly.mul h2p13 h2p16).getD 10 []=h2p17.getD 10 [] := by
  decide +kernel

theorem h2n17_arithmetic_row11 :
    (BiPoly.mul h2p13 h2p16).getD 11 []=h2p17.getD 11 [] := by
  decide +kernel

theorem h2n17_arithmetic_row12 :
    (BiPoly.mul h2p13 h2p16).getD 12 []=h2p17.getD 12 [] := by
  decide +kernel

theorem h2n17_arithmetic_row13 :
    (BiPoly.mul h2p13 h2p16).getD 13 []=h2p17.getD 13 [] := by
  decide +kernel

theorem h2n17_arithmetic_row14 :
    (BiPoly.mul h2p13 h2p16).getD 14 []=h2p17.getD 14 [] := by
  decide +kernel

theorem h2n17_arithmetic_row15 :
    (BiPoly.mul h2p13 h2p16).getD 15 []=h2p17.getD 15 [] := by
  decide +kernel

theorem h2n17_arithmetic : BiPoly.mul h2p13 h2p16=h2p17 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<16 at hk
    have hf : ∀ j : Fin 16, (BiPoly.mul h2p13 h2p16).getD j.val []=h2p17.getD j.val [] :=
      (fun j => Fin.cases h2n17_arithmetic_row0 (fun j => Fin.cases h2n17_arithmetic_row1 (fun j => Fin.cases h2n17_arithmetic_row2 (fun j => Fin.cases h2n17_arithmetic_row3 (fun j => Fin.cases h2n17_arithmetic_row4 (fun j => Fin.cases h2n17_arithmetic_row5 (fun j => Fin.cases h2n17_arithmetic_row6 (fun j => Fin.cases h2n17_arithmetic_row7 (fun j => Fin.cases h2n17_arithmetic_row8 (fun j => Fin.cases h2n17_arithmetic_row9 (fun j => Fin.cases h2n17_arithmetic_row10 (fun j => Fin.cases h2n17_arithmetic_row11 (fun j => Fin.cases h2n17_arithmetic_row12 (fun j => Fin.cases h2n17_arithmetic_row13 (fun j => Fin.cases h2n17_arithmetic_row14 (fun j => Fin.cases h2n17_arithmetic_row15 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h2n17 : h2e17.toBi mapPolyEnv=h2p17 := by
  change BiPoly.mul (h2e13.toBi mapPolyEnv) (h2e16.toBi mapPolyEnv)=h2p17
  rw [h2n13, h2n16]
  exact h2n17_arithmetic

#print axioms h2n17_arithmetic
end StackSorting.RationalLift
