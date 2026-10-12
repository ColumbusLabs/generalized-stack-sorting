import BivariateRowEquality
import Horner5Base
import Horner5Node398
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p399 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 8), (Int.ofNat 8), (Int.ofNat 16)], [(Int.ofNat 0), (Int.negSucc 7)]]

theorem h5n399_arithmetic_row0 :
    (BiPoly.mul h5p11 h5p398).getD 0 []=h5p399.getD 0 [] := by
  decide +kernel

theorem h5n399_arithmetic_row1 :
    (BiPoly.mul h5p11 h5p398).getD 1 []=h5p399.getD 1 [] := by
  decide +kernel

theorem h5n399_arithmetic : BiPoly.mul h5p11 h5p398=h5p399 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p11 h5p398).getD j.val []=h5p399.getD j.val [] :=
      (fun j => Fin.cases h5n399_arithmetic_row0 (fun j => Fin.cases h5n399_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n399 : h5e399.toBi mapPolyEnv=h5p399 := by
  change BiPoly.mul (h5e11.toBi mapPolyEnv) (h5e398.toBi mapPolyEnv)=h5p399
  rw [h5n11, h5n398]
  exact h5n399_arithmetic

#print axioms h5n399_arithmetic
end StackSorting.RationalLift
