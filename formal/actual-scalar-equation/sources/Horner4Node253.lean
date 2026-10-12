import BivariateRowEquality
import Horner4Base
import Horner4Node252
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p253 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 15), (Int.negSucc 31)]]

theorem h4n253_arithmetic_row0 :
    (BiPoly.mul h4p9 h4p252).getD 0 []=h4p253.getD 0 [] := by
  decide +kernel

theorem h4n253_arithmetic : BiPoly.mul h4p9 h4p252=h4p253 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<1 at hk
    have hf : ∀ j : Fin 1, (BiPoly.mul h4p9 h4p252).getD j.val []=h4p253.getD j.val [] :=
      (fun j => Fin.cases h4n253_arithmetic_row0 (fun j => Fin.elim0 j) j)
    exact hf ⟨k,hk⟩

theorem h4n253 : h4e253.toBi mapPolyEnv=h4p253 := by
  change BiPoly.mul (h4e9.toBi mapPolyEnv) (h4e252.toBi mapPolyEnv)=h4p253
  rw [h4n9, h4n252]
  exact h4n253_arithmetic

#print axioms h4n253_arithmetic
end StackSorting.RationalLift
