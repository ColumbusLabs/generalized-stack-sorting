import BivariateRowEquality
import Horner5Base
import Horner5Node216
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p217 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 143), (Int.negSucc 287)]]

theorem h5n217_arithmetic_row0 :
    (BiPoly.mul h5p11 h5p216).getD 0 []=h5p217.getD 0 [] := by
  decide +kernel

theorem h5n217_arithmetic : BiPoly.mul h5p11 h5p216=h5p217 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<1 at hk
    have hf : ∀ j : Fin 1, (BiPoly.mul h5p11 h5p216).getD j.val []=h5p217.getD j.val [] :=
      (fun j => Fin.cases h5n217_arithmetic_row0 (fun j => Fin.elim0 j) j)
    exact hf ⟨k,hk⟩

theorem h5n217 : h5e217.toBi mapPolyEnv=h5p217 := by
  change BiPoly.mul (h5e11.toBi mapPolyEnv) (h5e216.toBi mapPolyEnv)=h5p217
  rw [h5n11, h5n216]
  exact h5n217_arithmetic

#print axioms h5n217_arithmetic
end StackSorting.RationalLift
