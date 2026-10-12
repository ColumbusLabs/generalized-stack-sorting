import BivariateRowEquality
import Horner4Base
import Horner4Node137
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p138 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 143), (Int.negSucc 287)]]

theorem h4n138_arithmetic_row0 :
    (BiPoly.mul h4p9 h4p137).getD 0 []=h4p138.getD 0 [] := by
  decide +kernel

theorem h4n138_arithmetic : BiPoly.mul h4p9 h4p137=h4p138 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<1 at hk
    have hf : ∀ j : Fin 1, (BiPoly.mul h4p9 h4p137).getD j.val []=h4p138.getD j.val [] :=
      (fun j => Fin.cases h4n138_arithmetic_row0 (fun j => Fin.elim0 j) j)
    exact hf ⟨k,hk⟩

theorem h4n138 : h4e138.toBi mapPolyEnv=h4p138 := by
  change BiPoly.mul (h4e9.toBi mapPolyEnv) (h4e137.toBi mapPolyEnv)=h4p138
  rw [h4n9, h4n137]
  exact h4n138_arithmetic

#print axioms h4n138_arithmetic
end StackSorting.RationalLift
