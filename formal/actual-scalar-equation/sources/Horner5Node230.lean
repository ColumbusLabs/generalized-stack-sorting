import BivariateRowEquality
import Horner5Base
import Horner5Node229
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p230 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 58069224000), (Int.ofNat 231387049440), (Int.negSucc 34615486079), (Int.negSucc 207933311519)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 310734869759), (Int.negSucc 1115774289791), (Int.ofNat 422783919360), (Int.ofNat 810957858048), (Int.negSucc 93683568383)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 698959892880), (Int.ofNat 2327396397336), (Int.negSucc 874122088967), (Int.negSucc 1032176705975), (Int.ofNat 24982908408), (Int.negSucc 9948811391)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 854972541359), (Int.negSucc 2775954825143), (Int.ofNat 18685043712), (Int.ofNat 557659841400), (Int.ofNat 532762945920), (Int.negSucc 35919177839)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 613067624640), (Int.ofNat 2093390056512), (Int.ofNat 1824308569080), (Int.negSucc 140648126543), (Int.negSucc 659922927839), (Int.ofNat 31203999576)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 257397212159), (Int.negSucc 1022467259519), (Int.negSucc 2454579843767), (Int.negSucc 316418646455), (Int.ofNat 94366192104), (Int.ofNat 116010241632)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 58606902000), (Int.ofNat 309735311400), (Int.ofNat 1497703191120), (Int.ofNat 801632105352), (Int.ofNat 202868108928), (Int.negSucc 95347655711)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 5599020239), (Int.negSucc 50909695559), (Int.negSucc 459732356855), (Int.negSucc 699778661615), (Int.negSucc 162090052559), (Int.negSucc 31454105327)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3197255328), (Int.ofNat 60936310368), (Int.ofNat 264870852768), (Int.ofNat 109010580192), (Int.ofNat 40036483008)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1367257967), (Int.negSucc 37991007503), (Int.negSucc 48379959935), (Int.negSucc 7872461279)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 471015648), (Int.ofNat 7872461280)]]

theorem h5n230_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p229).getD 0 []=h5p230.getD 0 [] := by
  decide +kernel

theorem h5n230_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p229).getD 1 []=h5p230.getD 1 [] := by
  decide +kernel

theorem h5n230_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p229).getD 2 []=h5p230.getD 2 [] := by
  decide +kernel

theorem h5n230_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p229).getD 3 []=h5p230.getD 3 [] := by
  decide +kernel

theorem h5n230_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p229).getD 4 []=h5p230.getD 4 [] := by
  decide +kernel

theorem h5n230_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p229).getD 5 []=h5p230.getD 5 [] := by
  decide +kernel

theorem h5n230_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p229).getD 6 []=h5p230.getD 6 [] := by
  decide +kernel

theorem h5n230_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p229).getD 7 []=h5p230.getD 7 [] := by
  decide +kernel

theorem h5n230_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p229).getD 8 []=h5p230.getD 8 [] := by
  decide +kernel

theorem h5n230_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p229).getD 9 []=h5p230.getD 9 [] := by
  decide +kernel

theorem h5n230_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p229).getD 10 []=h5p230.getD 10 [] := by
  decide +kernel

theorem h5n230_arithmetic : BiPoly.mul h5p6 h5p229=h5p230 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p229).getD j.val []=h5p230.getD j.val [] :=
      (fun j => Fin.cases h5n230_arithmetic_row0 (fun j => Fin.cases h5n230_arithmetic_row1 (fun j => Fin.cases h5n230_arithmetic_row2 (fun j => Fin.cases h5n230_arithmetic_row3 (fun j => Fin.cases h5n230_arithmetic_row4 (fun j => Fin.cases h5n230_arithmetic_row5 (fun j => Fin.cases h5n230_arithmetic_row6 (fun j => Fin.cases h5n230_arithmetic_row7 (fun j => Fin.cases h5n230_arithmetic_row8 (fun j => Fin.cases h5n230_arithmetic_row9 (fun j => Fin.cases h5n230_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n230 : h5e230.toBi mapPolyEnv=h5p230 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e229.toBi mapPolyEnv)=h5p230
  rw [h5n6, h5n229]
  exact h5n230_arithmetic

#print axioms h5n230_arithmetic
end StackSorting.RationalLift
