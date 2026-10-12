import BivariateRowEquality
import Horner5Base
import Horner5Node170
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p171 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 11), (Int.negSucc 23), (Int.negSucc 35)], [(Int.ofNat 0), (Int.ofNat 12), (Int.ofNat 12)]]

theorem h5n171_arithmetic_row0 :
    (BiPoly.mul h5p11 h5p170).getD 0 []=h5p171.getD 0 [] := by
  decide +kernel

theorem h5n171_arithmetic_row1 :
    (BiPoly.mul h5p11 h5p170).getD 1 []=h5p171.getD 1 [] := by
  decide +kernel

theorem h5n171_arithmetic : BiPoly.mul h5p11 h5p170=h5p171 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p11 h5p170).getD j.val []=h5p171.getD j.val [] :=
      (fun j => Fin.cases h5n171_arithmetic_row0 (fun j => Fin.cases h5n171_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n171 : h5e171.toBi mapPolyEnv=h5p171 := by
  change BiPoly.mul (h5e11.toBi mapPolyEnv) (h5e170.toBi mapPolyEnv)=h5p171
  rw [h5n11, h5n170]
  exact h5n171_arithmetic

#print axioms h5n171_arithmetic
end StackSorting.RationalLift
