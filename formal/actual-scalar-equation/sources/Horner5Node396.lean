import BivariateRowEquality
import Horner5Base
import Horner5Node395
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p396 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 8), (Int.ofNat 16)]]

theorem h5n396_arithmetic_row0 :
    (BiPoly.mul h5p11 h5p395).getD 0 []=h5p396.getD 0 [] := by
  decide +kernel

theorem h5n396_arithmetic : BiPoly.mul h5p11 h5p395=h5p396 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<1 at hk
    have hf : ∀ j : Fin 1, (BiPoly.mul h5p11 h5p395).getD j.val []=h5p396.getD j.val [] :=
      (fun j => Fin.cases h5n396_arithmetic_row0 (fun j => Fin.elim0 j) j)
    exact hf ⟨k,hk⟩

theorem h5n396 : h5e396.toBi mapPolyEnv=h5p396 := by
  change BiPoly.mul (h5e11.toBi mapPolyEnv) (h5e395.toBi mapPolyEnv)=h5p396
  rw [h5n11, h5n395]
  exact h5n396_arithmetic

#print axioms h5n396_arithmetic
end StackSorting.RationalLift
