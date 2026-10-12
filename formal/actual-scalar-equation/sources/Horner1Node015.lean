import BivariateRowEquality
import Horner1Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p15 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 268838999), (Int.negSucc 802397339), (Int.ofNat 962654220)], [(Int.ofNat 0), (Int.ofNat 1169748360), (Int.ofNat 3193476012), (Int.negSucc 4188154751), (Int.ofNat 433720224)], [(Int.ofNat 0), (Int.negSucc 2066177069), (Int.negSucc 5515330238), (Int.ofNat 5374037010), (Int.negSucc 161720924), (Int.ofNat 46059312)], [(Int.ofNat 0), (Int.ofNat 1892029140), (Int.ofNat 5444283330), (Int.negSucc 156751151), (Int.negSucc 2586728297), (Int.ofNat 166292490)], [(Int.ofNat 0), (Int.negSucc 946246899), (Int.negSucc 3301090401), (Int.negSucc 5301533754), (Int.ofNat 3365954191), (Int.negSucc 144462960)], [(Int.ofNat 0), (Int.ofNat 245406860), (Int.ofNat 1187147458), (Int.ofNat 4875114360), (Int.negSucc 44259027), (Int.negSucc 537084451)], [(Int.ofNat 0), (Int.negSucc 25921389), (Int.negSucc 220890926), (Int.negSucc 1837805782), (Int.negSucc 1917712991), (Int.ofNat 441424332)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 14802108), (Int.ofNat 275782650), (Int.ofNat 1046220384), (Int.ofNat 145620858)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 6329897), (Int.negSucc 173703665), (Int.negSucc 185354087)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2180628), (Int.ofNat 36446580)]]

theorem h1n15_arithmetic_row0 :
    (BiPoly.mul h1p6 h1p9).getD 0 []=h1p15.getD 0 [] := by
  decide +kernel

theorem h1n15_arithmetic_row1 :
    (BiPoly.mul h1p6 h1p9).getD 1 []=h1p15.getD 1 [] := by
  decide +kernel

theorem h1n15_arithmetic_row2 :
    (BiPoly.mul h1p6 h1p9).getD 2 []=h1p15.getD 2 [] := by
  decide +kernel

theorem h1n15_arithmetic_row3 :
    (BiPoly.mul h1p6 h1p9).getD 3 []=h1p15.getD 3 [] := by
  decide +kernel

theorem h1n15_arithmetic_row4 :
    (BiPoly.mul h1p6 h1p9).getD 4 []=h1p15.getD 4 [] := by
  decide +kernel

theorem h1n15_arithmetic_row5 :
    (BiPoly.mul h1p6 h1p9).getD 5 []=h1p15.getD 5 [] := by
  decide +kernel

theorem h1n15_arithmetic_row6 :
    (BiPoly.mul h1p6 h1p9).getD 6 []=h1p15.getD 6 [] := by
  decide +kernel

theorem h1n15_arithmetic_row7 :
    (BiPoly.mul h1p6 h1p9).getD 7 []=h1p15.getD 7 [] := by
  decide +kernel

theorem h1n15_arithmetic_row8 :
    (BiPoly.mul h1p6 h1p9).getD 8 []=h1p15.getD 8 [] := by
  decide +kernel

theorem h1n15_arithmetic_row9 :
    (BiPoly.mul h1p6 h1p9).getD 9 []=h1p15.getD 9 [] := by
  decide +kernel

theorem h1n15_arithmetic : BiPoly.mul h1p6 h1p9=h1p15 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<10 at hk
    have hf : ∀ j : Fin 10, (BiPoly.mul h1p6 h1p9).getD j.val []=h1p15.getD j.val [] :=
      (fun j => Fin.cases h1n15_arithmetic_row0 (fun j => Fin.cases h1n15_arithmetic_row1 (fun j => Fin.cases h1n15_arithmetic_row2 (fun j => Fin.cases h1n15_arithmetic_row3 (fun j => Fin.cases h1n15_arithmetic_row4 (fun j => Fin.cases h1n15_arithmetic_row5 (fun j => Fin.cases h1n15_arithmetic_row6 (fun j => Fin.cases h1n15_arithmetic_row7 (fun j => Fin.cases h1n15_arithmetic_row8 (fun j => Fin.cases h1n15_arithmetic_row9 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n15 : h1e15.toBi mapPolyEnv=h1p15 := by
  change BiPoly.mul (h1e6.toBi mapPolyEnv) (h1e9.toBi mapPolyEnv)=h1p15
  rw [h1n6, h1n9]
  exact h1n15_arithmetic

#print axioms h1n15_arithmetic
end StackSorting.RationalLift
