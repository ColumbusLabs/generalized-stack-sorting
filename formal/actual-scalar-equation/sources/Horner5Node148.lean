import BivariateRowEquality
import Horner5Base
import Horner5Node147
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p148 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 835854336), (Int.negSucc 91907711), (Int.ofNat 7799105664), (Int.ofNat 4030812288), (Int.negSucc 14844723839), (Int.negSucc 10148668415)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3932474879), (Int.ofNat 1349026752), (Int.negSucc 50669747327), (Int.negSucc 27773351807), (Int.ofNat 50855166336), (Int.ofNat 24896065728), (Int.negSucc 2819074559)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7624775424), (Int.negSucc 276351743), (Int.ofNat 129935168640), (Int.ofNat 65036734080), (Int.negSucc 60212663807), (Int.negSucc 23398227455), (Int.negSucc 1452711935)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 7894839167), (Int.negSucc 9198279359), (Int.negSucc 166195934207), (Int.negSucc 92120970623), (Int.negSucc 4210084607), (Int.ofNat 10537872960), (Int.ofNat 11522624256)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4758039552), (Int.ofNat 17937884544), (Int.ofNat 113136538368), (Int.ofNat 107107248768), (Int.ofNat 69148468224), (Int.negSucc 2468956031), (Int.negSucc 7478832383)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1718655743), (Int.negSucc 14068448447), (Int.negSucc 42538068863), (Int.negSucc 88298923391), (Int.negSucc 59818060799), (Int.negSucc 9128350079), (Int.negSucc 3608340479)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 362541312), (Int.ofNat 5066535168), (Int.ofNat 10674458496), (Int.ofNat 39182030208), (Int.ofNat 25926175872), (Int.ofNat 13721619456), (Int.ofNat 3958958592)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 35240831), (Int.negSucc 737681471), (Int.negSucc 2479196159), (Int.negSucc 7441469567), (Int.negSucc 8303440895), (Int.negSucc 5777298431)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 19222272), (Int.ofNat 337675392), (Int.ofNat 330780672), (Int.ofNat 1818339840)]]

theorem h5n148_arithmetic_row0 :
    (BiPoly.mul h5p4 h5p147).getD 0 []=h5p148.getD 0 [] := by
  decide +kernel

theorem h5n148_arithmetic_row1 :
    (BiPoly.mul h5p4 h5p147).getD 1 []=h5p148.getD 1 [] := by
  decide +kernel

theorem h5n148_arithmetic_row2 :
    (BiPoly.mul h5p4 h5p147).getD 2 []=h5p148.getD 2 [] := by
  decide +kernel

theorem h5n148_arithmetic_row3 :
    (BiPoly.mul h5p4 h5p147).getD 3 []=h5p148.getD 3 [] := by
  decide +kernel

theorem h5n148_arithmetic_row4 :
    (BiPoly.mul h5p4 h5p147).getD 4 []=h5p148.getD 4 [] := by
  decide +kernel

theorem h5n148_arithmetic_row5 :
    (BiPoly.mul h5p4 h5p147).getD 5 []=h5p148.getD 5 [] := by
  decide +kernel

theorem h5n148_arithmetic_row6 :
    (BiPoly.mul h5p4 h5p147).getD 6 []=h5p148.getD 6 [] := by
  decide +kernel

theorem h5n148_arithmetic_row7 :
    (BiPoly.mul h5p4 h5p147).getD 7 []=h5p148.getD 7 [] := by
  decide +kernel

theorem h5n148_arithmetic_row8 :
    (BiPoly.mul h5p4 h5p147).getD 8 []=h5p148.getD 8 [] := by
  decide +kernel

theorem h5n148_arithmetic : BiPoly.mul h5p4 h5p147=h5p148 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<9 at hk
    have hf : ∀ j : Fin 9, (BiPoly.mul h5p4 h5p147).getD j.val []=h5p148.getD j.val [] :=
      (fun j => Fin.cases h5n148_arithmetic_row0 (fun j => Fin.cases h5n148_arithmetic_row1 (fun j => Fin.cases h5n148_arithmetic_row2 (fun j => Fin.cases h5n148_arithmetic_row3 (fun j => Fin.cases h5n148_arithmetic_row4 (fun j => Fin.cases h5n148_arithmetic_row5 (fun j => Fin.cases h5n148_arithmetic_row6 (fun j => Fin.cases h5n148_arithmetic_row7 (fun j => Fin.cases h5n148_arithmetic_row8 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n148 : h5e148.toBi mapPolyEnv=h5p148 := by
  change BiPoly.mul (h5e4.toBi mapPolyEnv) (h5e147.toBi mapPolyEnv)=h5p148
  rw [h5n4, h5n147]
  exact h5n148_arithmetic

#print axioms h5n148_arithmetic
end StackSorting.RationalLift
