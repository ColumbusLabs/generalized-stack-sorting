import BivariateRowEquality
import Horner1Base
import Horner1Node020
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p30 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 26244), (Int.ofNat 52488), (Int.ofNat 26244)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 175931), (Int.negSucc 267299), (Int.negSucc 102059), (Int.negSucc 10691)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 510309), (Int.ofNat 607248), (Int.ofNat 299718), (Int.ofNat 110304), (Int.negSucc 6038)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 835265), (Int.negSucc 899579), (Int.negSucc 729107), (Int.negSucc 247523), (Int.negSucc 9341), (Int.ofNat 1452)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 842299), (Int.ofNat 1089510), (Int.ofNat 1093064), (Int.ofNat 345260), (Int.ofNat 137533), (Int.negSucc 13089), (Int.ofNat 484)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 534759), (Int.negSucc 1100457), (Int.negSucc 987923), (Int.negSucc 533283), (Int.negSucc 208295), (Int.ofNat 338), (Int.ofNat 220)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 208251), (Int.ofNat 804780), (Int.ofNat 652027), (Int.ofNat 602876), (Int.ofNat 135942), (Int.ofNat 72416), (Int.negSucc 4990)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 45369), (Int.negSucc 370367), (Int.negSucc 411111), (Int.negSucc 356003), (Int.negSucc 136539), (Int.negSucc 65591), (Int.negSucc 347)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4225), (Int.ofNat 93430), (Int.ofNat 217390), (Int.ofNat 122424), (Int.ofNat 121770), (Int.ofNat 12720), (Int.ofNat 13176)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 9749), (Int.negSucc 66203), (Int.negSucc 49235), (Int.negSucc 39131), (Int.negSucc 11771), (Int.negSucc 4103)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7965), (Int.ofNat 18576), (Int.ofNat 5652), (Int.ofNat 5832), (Int.ofNat 324)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2699), (Int.negSucc 1727), (Int.negSucc 647)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 324)]]

theorem h1n30_arithmetic_row0 :
    (BiPoly.mul h1p9 h1p20).getD 0 []=h1p30.getD 0 [] := by
  decide +kernel

theorem h1n30_arithmetic_row1 :
    (BiPoly.mul h1p9 h1p20).getD 1 []=h1p30.getD 1 [] := by
  decide +kernel

theorem h1n30_arithmetic_row2 :
    (BiPoly.mul h1p9 h1p20).getD 2 []=h1p30.getD 2 [] := by
  decide +kernel

theorem h1n30_arithmetic_row3 :
    (BiPoly.mul h1p9 h1p20).getD 3 []=h1p30.getD 3 [] := by
  decide +kernel

theorem h1n30_arithmetic_row4 :
    (BiPoly.mul h1p9 h1p20).getD 4 []=h1p30.getD 4 [] := by
  decide +kernel

theorem h1n30_arithmetic_row5 :
    (BiPoly.mul h1p9 h1p20).getD 5 []=h1p30.getD 5 [] := by
  decide +kernel

theorem h1n30_arithmetic_row6 :
    (BiPoly.mul h1p9 h1p20).getD 6 []=h1p30.getD 6 [] := by
  decide +kernel

theorem h1n30_arithmetic_row7 :
    (BiPoly.mul h1p9 h1p20).getD 7 []=h1p30.getD 7 [] := by
  decide +kernel

theorem h1n30_arithmetic_row8 :
    (BiPoly.mul h1p9 h1p20).getD 8 []=h1p30.getD 8 [] := by
  decide +kernel

theorem h1n30_arithmetic_row9 :
    (BiPoly.mul h1p9 h1p20).getD 9 []=h1p30.getD 9 [] := by
  decide +kernel

theorem h1n30_arithmetic_row10 :
    (BiPoly.mul h1p9 h1p20).getD 10 []=h1p30.getD 10 [] := by
  decide +kernel

theorem h1n30_arithmetic_row11 :
    (BiPoly.mul h1p9 h1p20).getD 11 []=h1p30.getD 11 [] := by
  decide +kernel

theorem h1n30_arithmetic_row12 :
    (BiPoly.mul h1p9 h1p20).getD 12 []=h1p30.getD 12 [] := by
  decide +kernel

theorem h1n30_arithmetic : BiPoly.mul h1p9 h1p20=h1p30 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<13 at hk
    have hf : ∀ j : Fin 13, (BiPoly.mul h1p9 h1p20).getD j.val []=h1p30.getD j.val [] :=
      (fun j => Fin.cases h1n30_arithmetic_row0 (fun j => Fin.cases h1n30_arithmetic_row1 (fun j => Fin.cases h1n30_arithmetic_row2 (fun j => Fin.cases h1n30_arithmetic_row3 (fun j => Fin.cases h1n30_arithmetic_row4 (fun j => Fin.cases h1n30_arithmetic_row5 (fun j => Fin.cases h1n30_arithmetic_row6 (fun j => Fin.cases h1n30_arithmetic_row7 (fun j => Fin.cases h1n30_arithmetic_row8 (fun j => Fin.cases h1n30_arithmetic_row9 (fun j => Fin.cases h1n30_arithmetic_row10 (fun j => Fin.cases h1n30_arithmetic_row11 (fun j => Fin.cases h1n30_arithmetic_row12 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n30 : h1e30.toBi mapPolyEnv=h1p30 := by
  change BiPoly.mul (h1e9.toBi mapPolyEnv) (h1e20.toBi mapPolyEnv)=h1p30
  rw [h1n9, h1n20]
  exact h1n30_arithmetic

#print axioms h1n30_arithmetic
end StackSorting.RationalLift
