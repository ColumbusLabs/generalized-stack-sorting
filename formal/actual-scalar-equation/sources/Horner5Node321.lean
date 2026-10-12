import BivariateRowEquality
import Horner5Node023
import Horner5Node320
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p321 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 47), (Int.negSucc 47)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 48)]]

theorem h5n321_arithmetic_row0 :
    (BiPoly.mul h5p23 h5p320).getD 0 []=h5p321.getD 0 [] := by
  decide +kernel

theorem h5n321_arithmetic_row1 :
    (BiPoly.mul h5p23 h5p320).getD 1 []=h5p321.getD 1 [] := by
  decide +kernel

theorem h5n321_arithmetic : BiPoly.mul h5p23 h5p320=h5p321 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p23 h5p320).getD j.val []=h5p321.getD j.val [] :=
      (fun j => Fin.cases h5n321_arithmetic_row0 (fun j => Fin.cases h5n321_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n321 : h5e321.toBi mapPolyEnv=h5p321 := by
  change BiPoly.mul (h5e23.toBi mapPolyEnv) (h5e320.toBi mapPolyEnv)=h5p321
  rw [h5n23, h5n320]
  exact h5n321_arithmetic

#print axioms h5n321_arithmetic
end StackSorting.RationalLift
