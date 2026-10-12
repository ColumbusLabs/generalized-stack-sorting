import BivariateRowEquality
import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p23 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1)]]

theorem h5n23_arithmetic_row0 :
    (BiPoly.mul h5p11 h5p11).getD 0 []=h5p23.getD 0 [] := by
  decide +kernel

theorem h5n23_arithmetic : BiPoly.mul h5p11 h5p11=h5p23 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<1 at hk
    have hf : ∀ j : Fin 1, (BiPoly.mul h5p11 h5p11).getD j.val []=h5p23.getD j.val [] :=
      (fun j => Fin.cases h5n23_arithmetic_row0 (fun j => Fin.elim0 j) j)
    exact hf ⟨k,hk⟩

theorem h5n23 : h5e23.toBi mapPolyEnv=h5p23 := by
  change BiPoly.mul (h5e11.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p23
  rw [h5n11]
  exact h5n23_arithmetic

#print axioms h5n23_arithmetic
end StackSorting.RationalLift
