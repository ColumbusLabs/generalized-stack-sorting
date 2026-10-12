import BivariateRowEquality
import Horner5Base
import Horner5Node349
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p350 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 2477620223999), (Int.negSucc 8788555261439), (Int.ofNat 24533155272960), (Int.ofNat 48199870368000), (Int.negSucc 118579199719679), (Int.ofNat 57112349564160)], [(Int.ofNat 0), (Int.ofNat 21284478293760), (Int.ofNat 59129564637312), (Int.negSucc 240962746869503), (Int.negSucc 287116293599999), (Int.ofNat 1003996357129728), (Int.negSucc 596668389395327), (Int.ofNat 44214714473472)], [(Int.ofNat 0), (Int.negSucc 82141254455039), (Int.negSucc 166951417932287), (Int.ofNat 988569942935616), (Int.ofNat 622007492974848), (Int.negSucc 3429273867682175), (Int.ofNat 2237417513759232), (Int.negSucc 216240416047295), (Int.ofNat 11799353604096)], [(Int.ofNat 0), (Int.ofNat 187790622678720), (Int.ofNat 245722075613856), (Int.negSucc 2274247535290847), (Int.negSucc 470057644867391), (Int.ofNat 6061505021385984), (Int.negSucc 3441255619214303), (Int.negSucc 140513182096607), (Int.ofNat 8085463516800), (Int.ofNat 1217435922432)], [(Int.ofNat 0), (Int.negSucc 282292210172159), (Int.negSucc 169509007124927), (Int.ofNat 3284433482929632), (Int.negSucc 249162448048127), (Int.negSucc 5739700139371583), (Int.ofNat 224124630443712), (Int.ofNat 2602897274307168), (Int.negSucc 276246735128063), (Int.ofNat 9534537877248), (Int.ofNat 35373551616)], [(Int.ofNat 0), (Int.ofNat 292647292625280), (Int.negSucc 30449964914495), (Int.negSucc 3142087576432799), (Int.ofNat 461613914112192), (Int.ofNat 2510009140322688), (Int.ofNat 6592457005587072), (Int.negSucc 5625246803541983), (Int.ofNat 375052871252352), (Int.negSucc 22503006109055), (Int.ofNat 746749785600)], [(Int.ofNat 0), (Int.negSucc 213253475569919), (Int.ofNat 177261565364352), (Int.ofNat 2056301185096320), (Int.ofNat 415781391528864), (Int.negSucc 265411586261759), (Int.negSucc 9293349264902975), (Int.ofNat 3630214582564224), (Int.ofNat 1087619340707232), (Int.negSucc 102566187216191), (Int.ofNat 1593420237312)], [(Int.ofNat 0), (Int.ofNat 109114050551040), (Int.negSucc 178473811729919), (Int.negSucc 964010684267039), (Int.negSucc 1389992427089663), (Int.ofNat 537727699279392), (Int.ofNat 5175417238182240), (Int.ofNat 3043942821104832), (Int.negSucc 3107181640522943), (Int.ofNat 218333799036960), (Int.negSucc 7559492840063)], [(Int.ofNat 0), (Int.negSucc 38379497061119), (Int.ofNat 101211645871104), (Int.ofNat 366909600277440), (Int.ofNat 1476922436384928), (Int.negSucc 1090158009638975), (Int.negSucc 657864150681407), (Int.negSucc 6253080469755167), (Int.ofNat 2167441600664160), (Int.ofNat 223530120822528), (Int.negSucc 13908842997503)], [(Int.ofNat 0), (Int.ofNat 8831282290560), (Int.negSucc 36466809797951), (Int.negSucc 139005677950367), (Int.negSucc 915490915800767), (Int.ofNat 608573519818368), (Int.negSucc 118942587692543), (Int.ofNat 3552063608594304), (Int.ofNat 977355317640576), (Int.negSucc 774763601446079), (Int.ofNat 34044052163328)], [(Int.ofNat 0), (Int.negSucc 1195834106879), (Int.ofNat 8384330760576), (Int.ofNat 52057448802624), (Int.ofNat 374548089157152), (Int.ofNat 45644168141376), (Int.negSucc 539644766485439), (Int.negSucc 476579195079551), (Int.negSucc 2111955685433279), (Int.ofNat 439678057511232), (Int.ofNat 25105024122624)], [(Int.ofNat 0), (Int.ofNat 72165149760), (Int.negSucc 1140386822303), (Int.negSucc 14804741119871), (Int.negSucc 104639825674559), (Int.negSucc 205261297655903), (Int.ofNat 493172183083392), (Int.negSucc 147021117945983), (Int.ofNat 991056212575488), (Int.ofNat 235248811294464), (Int.negSucc 72792289064447)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 70771336128), (Int.ofNat 2494845772128), (Int.ofNat 19411649313120), (Int.ofNat 101421788881536), (Int.negSucc 133762232200319), (Int.negSucc 85362414436223), (Int.negSucc 88404509687039), (Int.negSucc 323857210452479), (Int.ofNat 22735546795008)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 180699156287), (Int.negSucc 2123297177471), (Int.negSucc 22605430629311), (Int.negSucc 5446794200831), (Int.ofNat 89057305640448), (Int.negSucc 33917045283071), (Int.ofNat 100413469732608), (Int.ofNat 22884179484672)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 98008418880), (Int.ofNat 2154070504512), (Int.ofNat 8261254478592), (Int.negSucc 18727986786047), (Int.negSucc 5055194568959), (Int.negSucc 2237331352319), (Int.negSucc 15414835092479)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 42234504191), (Int.negSucc 1042542316799), (Int.ofNat 161128154880), (Int.ofNat 4465695877632), (Int.negSucc 2242503221759), (Int.ofNat 2519187609600)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 11304375552), (Int.ofNat 166330319616), (Int.negSucc 377878141439)]]

theorem h5n350_arithmetic_row0 :
    (BiPoly.mul h5p34 h5p349).getD 0 []=h5p350.getD 0 [] := by
  decide +kernel

theorem h5n350_arithmetic_row1 :
    (BiPoly.mul h5p34 h5p349).getD 1 []=h5p350.getD 1 [] := by
  decide +kernel

theorem h5n350_arithmetic_row2 :
    (BiPoly.mul h5p34 h5p349).getD 2 []=h5p350.getD 2 [] := by
  decide +kernel

theorem h5n350_arithmetic_row3 :
    (BiPoly.mul h5p34 h5p349).getD 3 []=h5p350.getD 3 [] := by
  decide +kernel

theorem h5n350_arithmetic_row4 :
    (BiPoly.mul h5p34 h5p349).getD 4 []=h5p350.getD 4 [] := by
  decide +kernel

theorem h5n350_arithmetic_row5 :
    (BiPoly.mul h5p34 h5p349).getD 5 []=h5p350.getD 5 [] := by
  decide +kernel

theorem h5n350_arithmetic_row6 :
    (BiPoly.mul h5p34 h5p349).getD 6 []=h5p350.getD 6 [] := by
  decide +kernel

theorem h5n350_arithmetic_row7 :
    (BiPoly.mul h5p34 h5p349).getD 7 []=h5p350.getD 7 [] := by
  decide +kernel

theorem h5n350_arithmetic_row8 :
    (BiPoly.mul h5p34 h5p349).getD 8 []=h5p350.getD 8 [] := by
  decide +kernel

theorem h5n350_arithmetic_row9 :
    (BiPoly.mul h5p34 h5p349).getD 9 []=h5p350.getD 9 [] := by
  decide +kernel

theorem h5n350_arithmetic_row10 :
    (BiPoly.mul h5p34 h5p349).getD 10 []=h5p350.getD 10 [] := by
  decide +kernel

theorem h5n350_arithmetic_row11 :
    (BiPoly.mul h5p34 h5p349).getD 11 []=h5p350.getD 11 [] := by
  decide +kernel

theorem h5n350_arithmetic_row12 :
    (BiPoly.mul h5p34 h5p349).getD 12 []=h5p350.getD 12 [] := by
  decide +kernel

theorem h5n350_arithmetic_row13 :
    (BiPoly.mul h5p34 h5p349).getD 13 []=h5p350.getD 13 [] := by
  decide +kernel

theorem h5n350_arithmetic_row14 :
    (BiPoly.mul h5p34 h5p349).getD 14 []=h5p350.getD 14 [] := by
  decide +kernel

theorem h5n350_arithmetic_row15 :
    (BiPoly.mul h5p34 h5p349).getD 15 []=h5p350.getD 15 [] := by
  decide +kernel

theorem h5n350_arithmetic_row16 :
    (BiPoly.mul h5p34 h5p349).getD 16 []=h5p350.getD 16 [] := by
  decide +kernel

theorem h5n350_arithmetic : BiPoly.mul h5p34 h5p349=h5p350 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p34 h5p349).getD j.val []=h5p350.getD j.val [] :=
      (fun j => Fin.cases h5n350_arithmetic_row0 (fun j => Fin.cases h5n350_arithmetic_row1 (fun j => Fin.cases h5n350_arithmetic_row2 (fun j => Fin.cases h5n350_arithmetic_row3 (fun j => Fin.cases h5n350_arithmetic_row4 (fun j => Fin.cases h5n350_arithmetic_row5 (fun j => Fin.cases h5n350_arithmetic_row6 (fun j => Fin.cases h5n350_arithmetic_row7 (fun j => Fin.cases h5n350_arithmetic_row8 (fun j => Fin.cases h5n350_arithmetic_row9 (fun j => Fin.cases h5n350_arithmetic_row10 (fun j => Fin.cases h5n350_arithmetic_row11 (fun j => Fin.cases h5n350_arithmetic_row12 (fun j => Fin.cases h5n350_arithmetic_row13 (fun j => Fin.cases h5n350_arithmetic_row14 (fun j => Fin.cases h5n350_arithmetic_row15 (fun j => Fin.cases h5n350_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n350 : h5e350.toBi mapPolyEnv=h5p350 := by
  change BiPoly.mul (h5e34.toBi mapPolyEnv) (h5e349.toBi mapPolyEnv)=h5p350
  rw [h5n34, h5n349]
  exact h5n350_arithmetic

#print axioms h5n350_arithmetic
end StackSorting.RationalLift
