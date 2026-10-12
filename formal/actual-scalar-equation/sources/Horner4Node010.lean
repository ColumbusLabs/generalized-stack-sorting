import BivariateRowEquality
import Horner4Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p10 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1)]]

theorem h4n10_arithmetic_row0 :
    (BiPoly.mul h4p9 h4p9).getD 0 []=h4p10.getD 0 [] := by
  decide +kernel

theorem h4n10_arithmetic : BiPoly.mul h4p9 h4p9=h4p10 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<1 at hk
    have hf : ∀ j : Fin 1, (BiPoly.mul h4p9 h4p9).getD j.val []=h4p10.getD j.val [] :=
      (fun j => Fin.cases h4n10_arithmetic_row0 (fun j => Fin.elim0 j) j)
    exact hf ⟨k,hk⟩

theorem h4n10 : h4e10.toBi mapPolyEnv=h4p10 := by
  change BiPoly.mul (h4e9.toBi mapPolyEnv) (h4e9.toBi mapPolyEnv)=h4p10
  rw [h4n9]
  exact h4n10_arithmetic

#print axioms h4n10_arithmetic
end StackSorting.RationalLift
