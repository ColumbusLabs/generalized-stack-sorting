import BivariateRowEquality
import Horner5Base
import Horner5Node313
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p314 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 2477620224000), (Int.ofNat 8788555261440), (Int.negSucc 24533155272959), (Int.negSucc 48199870367999), (Int.ofNat 118579199719680), (Int.negSucc 57112349564159)], [(Int.ofNat 0), (Int.negSucc 21284478293759), (Int.negSucc 59129564637311), (Int.ofNat 240962746869504), (Int.ofNat 287116293600000), (Int.negSucc 1003996357129727), (Int.ofNat 596668389395328), (Int.negSucc 44214714473471)], [(Int.ofNat 0), (Int.ofNat 82141254455040), (Int.ofNat 166951417932288), (Int.negSucc 988569942935615), (Int.negSucc 622007492974847), (Int.ofNat 3429273867682176), (Int.negSucc 2237417513759231), (Int.ofNat 216240416047296), (Int.negSucc 11799353604095)], [(Int.ofNat 0), (Int.negSucc 187790622678719), (Int.negSucc 245722075613855), (Int.ofNat 2274247535290848), (Int.ofNat 470057644867392), (Int.negSucc 6061505021385983), (Int.ofNat 3441255619214304), (Int.ofNat 140513182096608), (Int.negSucc 8085463516799), (Int.negSucc 1217435922431)], [(Int.ofNat 0), (Int.ofNat 282292210172160), (Int.ofNat 169509007124928), (Int.negSucc 3284433482929631), (Int.ofNat 249162448048128), (Int.ofNat 5739700139371584), (Int.negSucc 224124630443711), (Int.negSucc 2602897274307167), (Int.ofNat 276246735128064), (Int.negSucc 9534537877247), (Int.negSucc 35373551615)], [(Int.ofNat 0), (Int.negSucc 292647292625279), (Int.ofNat 30449964914496), (Int.ofNat 3142087576432800), (Int.negSucc 461613914112191), (Int.negSucc 2510009140322687), (Int.negSucc 6592457005587071), (Int.ofNat 5625246803541984), (Int.negSucc 375052871252351), (Int.ofNat 22503006109056), (Int.negSucc 746749785599)], [(Int.ofNat 0), (Int.ofNat 213253475569920), (Int.negSucc 177261565364351), (Int.negSucc 2056301185096319), (Int.negSucc 415781391528863), (Int.ofNat 265411586261760), (Int.ofNat 9293349264902976), (Int.negSucc 3630214582564223), (Int.negSucc 1087619340707231), (Int.ofNat 102566187216192), (Int.negSucc 1593420237311)], [(Int.ofNat 0), (Int.negSucc 109114050551039), (Int.ofNat 178473811729920), (Int.ofNat 964010684267040), (Int.ofNat 1389992427089664), (Int.negSucc 537727699279391), (Int.negSucc 5175417238182239), (Int.negSucc 3043942821104831), (Int.ofNat 3107181640522944), (Int.negSucc 218333799036959), (Int.ofNat 7559492840064)], [(Int.ofNat 0), (Int.ofNat 38379497061120), (Int.negSucc 101211645871103), (Int.negSucc 366909600277439), (Int.negSucc 1476922436384927), (Int.ofNat 1090158009638976), (Int.ofNat 657864150681408), (Int.ofNat 6253080469755168), (Int.negSucc 2167441600664159), (Int.negSucc 223530120822527), (Int.ofNat 13908842997504)], [(Int.ofNat 0), (Int.negSucc 8831282290559), (Int.ofNat 36466809797952), (Int.ofNat 139005677950368), (Int.ofNat 915490915800768), (Int.negSucc 608573519818367), (Int.ofNat 118942587692544), (Int.negSucc 3552063608594303), (Int.negSucc 977355317640575), (Int.ofNat 774763601446080), (Int.negSucc 34044052163327)], [(Int.ofNat 0), (Int.ofNat 1195834106880), (Int.negSucc 8384330760575), (Int.negSucc 52057448802623), (Int.negSucc 374548089157151), (Int.negSucc 45644168141375), (Int.ofNat 539644766485440), (Int.ofNat 476579195079552), (Int.ofNat 2111955685433280), (Int.negSucc 439678057511231), (Int.negSucc 25105024122623)], [(Int.ofNat 0), (Int.negSucc 72165149759), (Int.ofNat 1140386822304), (Int.ofNat 14804741119872), (Int.ofNat 104639825674560), (Int.ofNat 205261297655904), (Int.negSucc 493172183083391), (Int.ofNat 147021117945984), (Int.negSucc 991056212575487), (Int.negSucc 235248811294463), (Int.ofNat 72792289064448)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 70771336127), (Int.negSucc 2494845772127), (Int.negSucc 19411649313119), (Int.negSucc 101421788881535), (Int.ofNat 133762232200320), (Int.ofNat 85362414436224), (Int.ofNat 88404509687040), (Int.ofNat 323857210452480), (Int.negSucc 22735546795007)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 180699156288), (Int.ofNat 2123297177472), (Int.ofNat 22605430629312), (Int.ofNat 5446794200832), (Int.negSucc 89057305640447), (Int.ofNat 33917045283072), (Int.negSucc 100413469732607), (Int.negSucc 22884179484671)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 98008418879), (Int.negSucc 2154070504511), (Int.negSucc 8261254478591), (Int.ofNat 18727986786048), (Int.ofNat 5055194568960), (Int.ofNat 2237331352320), (Int.ofNat 15414835092480)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 42234504192), (Int.ofNat 1042542316800), (Int.negSucc 161128154879), (Int.negSucc 4465695877631), (Int.ofNat 2242503221760), (Int.negSucc 2519187609599)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 11304375551), (Int.negSucc 166330319615), (Int.ofNat 377878141440)]]

theorem h5n314_arithmetic_row0 :
    (BiPoly.mul h5p34 h5p313).getD 0 []=h5p314.getD 0 [] := by
  decide +kernel

theorem h5n314_arithmetic_row1 :
    (BiPoly.mul h5p34 h5p313).getD 1 []=h5p314.getD 1 [] := by
  decide +kernel

theorem h5n314_arithmetic_row2 :
    (BiPoly.mul h5p34 h5p313).getD 2 []=h5p314.getD 2 [] := by
  decide +kernel

theorem h5n314_arithmetic_row3 :
    (BiPoly.mul h5p34 h5p313).getD 3 []=h5p314.getD 3 [] := by
  decide +kernel

theorem h5n314_arithmetic_row4 :
    (BiPoly.mul h5p34 h5p313).getD 4 []=h5p314.getD 4 [] := by
  decide +kernel

theorem h5n314_arithmetic_row5 :
    (BiPoly.mul h5p34 h5p313).getD 5 []=h5p314.getD 5 [] := by
  decide +kernel

theorem h5n314_arithmetic_row6 :
    (BiPoly.mul h5p34 h5p313).getD 6 []=h5p314.getD 6 [] := by
  decide +kernel

theorem h5n314_arithmetic_row7 :
    (BiPoly.mul h5p34 h5p313).getD 7 []=h5p314.getD 7 [] := by
  decide +kernel

theorem h5n314_arithmetic_row8 :
    (BiPoly.mul h5p34 h5p313).getD 8 []=h5p314.getD 8 [] := by
  decide +kernel

theorem h5n314_arithmetic_row9 :
    (BiPoly.mul h5p34 h5p313).getD 9 []=h5p314.getD 9 [] := by
  decide +kernel

theorem h5n314_arithmetic_row10 :
    (BiPoly.mul h5p34 h5p313).getD 10 []=h5p314.getD 10 [] := by
  decide +kernel

theorem h5n314_arithmetic_row11 :
    (BiPoly.mul h5p34 h5p313).getD 11 []=h5p314.getD 11 [] := by
  decide +kernel

theorem h5n314_arithmetic_row12 :
    (BiPoly.mul h5p34 h5p313).getD 12 []=h5p314.getD 12 [] := by
  decide +kernel

theorem h5n314_arithmetic_row13 :
    (BiPoly.mul h5p34 h5p313).getD 13 []=h5p314.getD 13 [] := by
  decide +kernel

theorem h5n314_arithmetic_row14 :
    (BiPoly.mul h5p34 h5p313).getD 14 []=h5p314.getD 14 [] := by
  decide +kernel

theorem h5n314_arithmetic_row15 :
    (BiPoly.mul h5p34 h5p313).getD 15 []=h5p314.getD 15 [] := by
  decide +kernel

theorem h5n314_arithmetic_row16 :
    (BiPoly.mul h5p34 h5p313).getD 16 []=h5p314.getD 16 [] := by
  decide +kernel

theorem h5n314_arithmetic : BiPoly.mul h5p34 h5p313=h5p314 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p34 h5p313).getD j.val []=h5p314.getD j.val [] :=
      (fun j => Fin.cases h5n314_arithmetic_row0 (fun j => Fin.cases h5n314_arithmetic_row1 (fun j => Fin.cases h5n314_arithmetic_row2 (fun j => Fin.cases h5n314_arithmetic_row3 (fun j => Fin.cases h5n314_arithmetic_row4 (fun j => Fin.cases h5n314_arithmetic_row5 (fun j => Fin.cases h5n314_arithmetic_row6 (fun j => Fin.cases h5n314_arithmetic_row7 (fun j => Fin.cases h5n314_arithmetic_row8 (fun j => Fin.cases h5n314_arithmetic_row9 (fun j => Fin.cases h5n314_arithmetic_row10 (fun j => Fin.cases h5n314_arithmetic_row11 (fun j => Fin.cases h5n314_arithmetic_row12 (fun j => Fin.cases h5n314_arithmetic_row13 (fun j => Fin.cases h5n314_arithmetic_row14 (fun j => Fin.cases h5n314_arithmetic_row15 (fun j => Fin.cases h5n314_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n314 : h5e314.toBi mapPolyEnv=h5p314 := by
  change BiPoly.mul (h5e34.toBi mapPolyEnv) (h5e313.toBi mapPolyEnv)=h5p314
  rw [h5n34, h5n313]
  exact h5n314_arithmetic

#print axioms h5n314_arithmetic
end StackSorting.RationalLift
