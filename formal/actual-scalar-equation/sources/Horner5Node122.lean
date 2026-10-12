import BivariateRowEquality
import Horner5Base
import Horner5Node121
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p122 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 1858215167999), (Int.negSucc 6591416446079), (Int.ofNat 18399866454720), (Int.ofNat 36149902776000), (Int.negSucc 88934399789759), (Int.ofNat 42834262173120)], [(Int.ofNat 0), (Int.ofNat 15963358720320), (Int.ofNat 44347173477984), (Int.negSucc 180722060152127), (Int.negSucc 215337220199999), (Int.ofNat 752997267847296), (Int.negSucc 447501292046495), (Int.ofNat 33161035855104)], [(Int.ofNat 0), (Int.negSucc 61605940841279), (Int.negSucc 125213563449215), (Int.ofNat 741427457201712), (Int.ofNat 466505619731136), (Int.negSucc 2571955400761631), (Int.ofNat 1678063135319424), (Int.negSucc 162180312035471), (Int.ofNat 8849515203072)], [(Int.ofNat 0), (Int.ofNat 140842967009040), (Int.ofNat 184291556710392), (Int.negSucc 1705685651468135), (Int.negSucc 352543233650543), (Int.ofNat 4546128766039488), (Int.negSucc 2580941714410727), (Int.negSucc 105384886572455), (Int.ofNat 6064097637600), (Int.ofNat 913076941824)], [(Int.ofNat 0), (Int.negSucc 211719157629119), (Int.negSucc 127131755343695), (Int.ofNat 2463325112197224), (Int.negSucc 186871836036095), (Int.negSucc 4304775104528687), (Int.ofNat 168093472832784), (Int.ofNat 1952172955730376), (Int.negSucc 207185051346047), (Int.ofNat 7150903407936), (Int.ofNat 26530163712)], [(Int.ofNat 0), (Int.ofNat 219485469468960), (Int.negSucc 22837473685871), (Int.negSucc 2356565682324599), (Int.ofNat 346210435584144), (Int.ofNat 1882506855242016), (Int.ofNat 4944342754190304), (Int.negSucc 4218935102656487), (Int.ofNat 281289653439264), (Int.negSucc 16877254581791), (Int.ofNat 560062339200)], [(Int.ofNat 0), (Int.negSucc 159940106677439), (Int.ofNat 132946174023264), (Int.ofNat 1542225888822240), (Int.ofNat 311836043646648), (Int.negSucc 199058689696319), (Int.negSucc 6970011948677231), (Int.ofNat 2722660936923168), (Int.ofNat 815714505530424), (Int.negSucc 76924640412143), (Int.ofNat 1195065177984)], [(Int.ofNat 0), (Int.ofNat 81835537913280), (Int.negSucc 133855358797439), (Int.negSucc 723008013200279), (Int.negSucc 1042494320317247), (Int.ofNat 403295774459544), (Int.ofNat 3881562928636680), (Int.ofNat 2282957115828624), (Int.negSucc 2330386230392207), (Int.ofNat 163750349277720), (Int.negSucc 5669619630047)], [(Int.ofNat 0), (Int.negSucc 28784622795839), (Int.ofNat 75908734403328), (Int.ofNat 275182200208080), (Int.ofNat 1107691827288696), (Int.negSucc 817618507229231), (Int.negSucc 493398113011055), (Int.negSucc 4689810352316375), (Int.ofNat 1625581200498120), (Int.ofNat 167647590616896), (Int.negSucc 10431632248127)], [(Int.ofNat 0), (Int.ofNat 6623461717920), (Int.negSucc 27350107348463), (Int.negSucc 104254258462775), (Int.negSucc 686618186850575), (Int.ofNat 456430139863776), (Int.negSucc 89206940769407), (Int.ofNat 2664047706445728), (Int.ofNat 733016488230432), (Int.negSucc 581072701084559), (Int.ofNat 25533039122496)], [(Int.ofNat 0), (Int.negSucc 896875580159), (Int.ofNat 6288248070432), (Int.ofNat 39043086601968), (Int.ofNat 280911066867864), (Int.ofNat 34233126106032), (Int.negSucc 404733574864079), (Int.negSucc 357434396309663), (Int.negSucc 1583966764074959), (Int.ofNat 329758543133424), (Int.ofNat 18828768091968)], [(Int.ofNat 0), (Int.ofNat 54123862320), (Int.negSucc 855290116727), (Int.negSucc 11103555839903), (Int.negSucc 78479869255919), (Int.negSucc 153945973241927), (Int.ofNat 369879137312544), (Int.negSucc 110265838459487), (Int.ofNat 743292159431616), (Int.ofNat 176436608470848), (Int.negSucc 54594216798335)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 53078502096), (Int.ofNat 1871134329096), (Int.ofNat 14558736984840), (Int.ofNat 76066341661152), (Int.negSucc 100321674150239), (Int.negSucc 64021810827167), (Int.negSucc 66303382265279), (Int.negSucc 242892907839359), (Int.ofNat 17051660096256)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 135524367215), (Int.negSucc 1592472883103), (Int.negSucc 16954072971983), (Int.negSucc 4085095650623), (Int.ofNat 66792979230336), (Int.negSucc 25437783962303), (Int.ofNat 75310102299456), (Int.ofNat 17163134613504)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 73506314160), (Int.ofNat 1615552878384), (Int.ofNat 6195940858944), (Int.negSucc 14045990089535), (Int.negSucc 3791395926719), (Int.negSucc 1677998514239), (Int.negSucc 11561126319359)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 31675878143), (Int.negSucc 781906737599), (Int.ofNat 120846116160), (Int.ofNat 3349271908224), (Int.negSucc 1681877416319), (Int.ofNat 1889390707200)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 8478281664), (Int.ofNat 124747739712), (Int.negSucc 283408606079)]]

theorem h5n122_arithmetic_row0 :
    (BiPoly.mul h5p34 h5p121).getD 0 []=h5p122.getD 0 [] := by
  decide +kernel

theorem h5n122_arithmetic_row1 :
    (BiPoly.mul h5p34 h5p121).getD 1 []=h5p122.getD 1 [] := by
  decide +kernel

theorem h5n122_arithmetic_row2 :
    (BiPoly.mul h5p34 h5p121).getD 2 []=h5p122.getD 2 [] := by
  decide +kernel

theorem h5n122_arithmetic_row3 :
    (BiPoly.mul h5p34 h5p121).getD 3 []=h5p122.getD 3 [] := by
  decide +kernel

theorem h5n122_arithmetic_row4 :
    (BiPoly.mul h5p34 h5p121).getD 4 []=h5p122.getD 4 [] := by
  decide +kernel

theorem h5n122_arithmetic_row5 :
    (BiPoly.mul h5p34 h5p121).getD 5 []=h5p122.getD 5 [] := by
  decide +kernel

theorem h5n122_arithmetic_row6 :
    (BiPoly.mul h5p34 h5p121).getD 6 []=h5p122.getD 6 [] := by
  decide +kernel

theorem h5n122_arithmetic_row7 :
    (BiPoly.mul h5p34 h5p121).getD 7 []=h5p122.getD 7 [] := by
  decide +kernel

theorem h5n122_arithmetic_row8 :
    (BiPoly.mul h5p34 h5p121).getD 8 []=h5p122.getD 8 [] := by
  decide +kernel

theorem h5n122_arithmetic_row9 :
    (BiPoly.mul h5p34 h5p121).getD 9 []=h5p122.getD 9 [] := by
  decide +kernel

theorem h5n122_arithmetic_row10 :
    (BiPoly.mul h5p34 h5p121).getD 10 []=h5p122.getD 10 [] := by
  decide +kernel

theorem h5n122_arithmetic_row11 :
    (BiPoly.mul h5p34 h5p121).getD 11 []=h5p122.getD 11 [] := by
  decide +kernel

theorem h5n122_arithmetic_row12 :
    (BiPoly.mul h5p34 h5p121).getD 12 []=h5p122.getD 12 [] := by
  decide +kernel

theorem h5n122_arithmetic_row13 :
    (BiPoly.mul h5p34 h5p121).getD 13 []=h5p122.getD 13 [] := by
  decide +kernel

theorem h5n122_arithmetic_row14 :
    (BiPoly.mul h5p34 h5p121).getD 14 []=h5p122.getD 14 [] := by
  decide +kernel

theorem h5n122_arithmetic_row15 :
    (BiPoly.mul h5p34 h5p121).getD 15 []=h5p122.getD 15 [] := by
  decide +kernel

theorem h5n122_arithmetic_row16 :
    (BiPoly.mul h5p34 h5p121).getD 16 []=h5p122.getD 16 [] := by
  decide +kernel

theorem h5n122_arithmetic : BiPoly.mul h5p34 h5p121=h5p122 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p34 h5p121).getD j.val []=h5p122.getD j.val [] :=
      (fun j => Fin.cases h5n122_arithmetic_row0 (fun j => Fin.cases h5n122_arithmetic_row1 (fun j => Fin.cases h5n122_arithmetic_row2 (fun j => Fin.cases h5n122_arithmetic_row3 (fun j => Fin.cases h5n122_arithmetic_row4 (fun j => Fin.cases h5n122_arithmetic_row5 (fun j => Fin.cases h5n122_arithmetic_row6 (fun j => Fin.cases h5n122_arithmetic_row7 (fun j => Fin.cases h5n122_arithmetic_row8 (fun j => Fin.cases h5n122_arithmetic_row9 (fun j => Fin.cases h5n122_arithmetic_row10 (fun j => Fin.cases h5n122_arithmetic_row11 (fun j => Fin.cases h5n122_arithmetic_row12 (fun j => Fin.cases h5n122_arithmetic_row13 (fun j => Fin.cases h5n122_arithmetic_row14 (fun j => Fin.cases h5n122_arithmetic_row15 (fun j => Fin.cases h5n122_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n122 : h5e122.toBi mapPolyEnv=h5p122 := by
  change BiPoly.mul (h5e34.toBi mapPolyEnv) (h5e121.toBi mapPolyEnv)=h5p122
  rw [h5n34, h5n121]
  exact h5n122_arithmetic

#print axioms h5n122_arithmetic
end StackSorting.RationalLift
