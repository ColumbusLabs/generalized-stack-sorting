import BivariateRowEquality
import Horner5Base
import Horner5Node411
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p412 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 15), (Int.negSucc 31)]]

theorem h5n412_arithmetic_row0 :
    (BiPoly.mul h5p11 h5p411).getD 0 []=h5p412.getD 0 [] := by
  decide +kernel

theorem h5n412_arithmetic : BiPoly.mul h5p11 h5p411=h5p412 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<1 at hk
    have hf : ∀ j : Fin 1, (BiPoly.mul h5p11 h5p411).getD j.val []=h5p412.getD j.val [] :=
      (fun j => Fin.cases h5n412_arithmetic_row0 (fun j => Fin.elim0 j) j)
    exact hf ⟨k,hk⟩

theorem h5n412 : h5e412.toBi mapPolyEnv=h5p412 := by
  change BiPoly.mul (h5e11.toBi mapPolyEnv) (h5e411.toBi mapPolyEnv)=h5p412
  rw [h5n11, h5n411]
  exact h5n412_arithmetic

#print axioms h5n412_arithmetic
end StackSorting.RationalLift
