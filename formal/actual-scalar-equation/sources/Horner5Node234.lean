import BivariateRowEquality
import Horner5Base
import Horner5Node233
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p234 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 144), (Int.ofNat 288)]]

theorem h5n234_arithmetic_row0 :
    (BiPoly.mul h5p11 h5p233).getD 0 []=h5p234.getD 0 [] := by
  decide +kernel

theorem h5n234_arithmetic : BiPoly.mul h5p11 h5p233=h5p234 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<1 at hk
    have hf : ∀ j : Fin 1, (BiPoly.mul h5p11 h5p233).getD j.val []=h5p234.getD j.val [] :=
      (fun j => Fin.cases h5n234_arithmetic_row0 (fun j => Fin.elim0 j) j)
    exact hf ⟨k,hk⟩

theorem h5n234 : h5e234.toBi mapPolyEnv=h5p234 := by
  change BiPoly.mul (h5e11.toBi mapPolyEnv) (h5e233.toBi mapPolyEnv)=h5p234
  rw [h5n11, h5n233]
  exact h5n234_arithmetic

#print axioms h5n234_arithmetic
end StackSorting.RationalLift
