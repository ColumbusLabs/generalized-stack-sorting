import BivariateRowEquality
import Horner5Base
import Horner5Node098
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p99 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 47), (Int.negSucc 23)], [(Int.ofNat 0), (Int.ofNat 72)]]

theorem h5n99_arithmetic_row0 :
    (BiPoly.mul h5p11 h5p98).getD 0 []=h5p99.getD 0 [] := by
  decide +kernel

theorem h5n99_arithmetic_row1 :
    (BiPoly.mul h5p11 h5p98).getD 1 []=h5p99.getD 1 [] := by
  decide +kernel

theorem h5n99_arithmetic : BiPoly.mul h5p11 h5p98=h5p99 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p11 h5p98).getD j.val []=h5p99.getD j.val [] :=
      (fun j => Fin.cases h5n99_arithmetic_row0 (fun j => Fin.cases h5n99_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n99 : h5e99.toBi mapPolyEnv=h5p99 := by
  change BiPoly.mul (h5e11.toBi mapPolyEnv) (h5e98.toBi mapPolyEnv)=h5p99
  rw [h5n11, h5n98]
  exact h5n99_arithmetic

#print axioms h5n99_arithmetic
end StackSorting.RationalLift
