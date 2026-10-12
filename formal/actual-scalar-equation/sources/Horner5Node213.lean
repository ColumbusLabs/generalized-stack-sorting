import BivariateRowEquality
import Horner5Base
import Horner5Node212
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p213 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 58069223999), (Int.negSucc 231387049439), (Int.ofNat 34615486080), (Int.ofNat 207933311520)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 310734869760), (Int.ofNat 1115774289792), (Int.negSucc 422783919359), (Int.negSucc 810957858047), (Int.ofNat 93683568384)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 698959892879), (Int.negSucc 2327396397335), (Int.ofNat 874122088968), (Int.ofNat 1032176705976), (Int.negSucc 24982908407), (Int.ofNat 9948811392)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 854972541360), (Int.ofNat 2775954825144), (Int.negSucc 18685043711), (Int.negSucc 557659841399), (Int.negSucc 532762945919), (Int.ofNat 35919177840)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 613067624639), (Int.negSucc 2093390056511), (Int.negSucc 1824308569079), (Int.ofNat 140648126544), (Int.ofNat 659922927840), (Int.negSucc 31203999575)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 257397212160), (Int.ofNat 1022467259520), (Int.ofNat 2454579843768), (Int.ofNat 316418646456), (Int.negSucc 94366192103), (Int.negSucc 116010241631)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 58606901999), (Int.negSucc 309735311399), (Int.negSucc 1497703191119), (Int.negSucc 801632105351), (Int.negSucc 202868108927), (Int.ofNat 95347655712)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5599020240), (Int.ofNat 50909695560), (Int.ofNat 459732356856), (Int.ofNat 699778661616), (Int.ofNat 162090052560), (Int.ofNat 31454105328)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3197255327), (Int.negSucc 60936310367), (Int.negSucc 264870852767), (Int.negSucc 109010580191), (Int.negSucc 40036483007)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1367257968), (Int.ofNat 37991007504), (Int.ofNat 48379959936), (Int.ofNat 7872461280)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 471015647), (Int.negSucc 7872461279)]]

theorem h5n213_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p212).getD 0 []=h5p213.getD 0 [] := by
  decide +kernel

theorem h5n213_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p212).getD 1 []=h5p213.getD 1 [] := by
  decide +kernel

theorem h5n213_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p212).getD 2 []=h5p213.getD 2 [] := by
  decide +kernel

theorem h5n213_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p212).getD 3 []=h5p213.getD 3 [] := by
  decide +kernel

theorem h5n213_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p212).getD 4 []=h5p213.getD 4 [] := by
  decide +kernel

theorem h5n213_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p212).getD 5 []=h5p213.getD 5 [] := by
  decide +kernel

theorem h5n213_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p212).getD 6 []=h5p213.getD 6 [] := by
  decide +kernel

theorem h5n213_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p212).getD 7 []=h5p213.getD 7 [] := by
  decide +kernel

theorem h5n213_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p212).getD 8 []=h5p213.getD 8 [] := by
  decide +kernel

theorem h5n213_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p212).getD 9 []=h5p213.getD 9 [] := by
  decide +kernel

theorem h5n213_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p212).getD 10 []=h5p213.getD 10 [] := by
  decide +kernel

theorem h5n213_arithmetic : BiPoly.mul h5p6 h5p212=h5p213 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p212).getD j.val []=h5p213.getD j.val [] :=
      (fun j => Fin.cases h5n213_arithmetic_row0 (fun j => Fin.cases h5n213_arithmetic_row1 (fun j => Fin.cases h5n213_arithmetic_row2 (fun j => Fin.cases h5n213_arithmetic_row3 (fun j => Fin.cases h5n213_arithmetic_row4 (fun j => Fin.cases h5n213_arithmetic_row5 (fun j => Fin.cases h5n213_arithmetic_row6 (fun j => Fin.cases h5n213_arithmetic_row7 (fun j => Fin.cases h5n213_arithmetic_row8 (fun j => Fin.cases h5n213_arithmetic_row9 (fun j => Fin.cases h5n213_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n213 : h5e213.toBi mapPolyEnv=h5p213 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e212.toBi mapPolyEnv)=h5p213
  rw [h5n6, h5n212]
  exact h5n213_arithmetic

#print axioms h5n213_arithmetic
end StackSorting.RationalLift
