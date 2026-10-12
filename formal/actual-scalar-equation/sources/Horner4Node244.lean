import BivariateRowEquality
import Horner4Base
import Horner4Node243
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p244 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 8), (Int.ofNat 16)]]

theorem h4n244_arithmetic_row0 :
    (BiPoly.mul h4p9 h4p243).getD 0 []=h4p244.getD 0 [] := by
  decide +kernel

theorem h4n244_arithmetic : BiPoly.mul h4p9 h4p243=h4p244 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<1 at hk
    have hf : ∀ j : Fin 1, (BiPoly.mul h4p9 h4p243).getD j.val []=h4p244.getD j.val [] :=
      (fun j => Fin.cases h4n244_arithmetic_row0 (fun j => Fin.elim0 j) j)
    exact hf ⟨k,hk⟩

theorem h4n244 : h4e244.toBi mapPolyEnv=h4p244 := by
  change BiPoly.mul (h4e9.toBi mapPolyEnv) (h4e243.toBi mapPolyEnv)=h4p244
  rw [h4n9, h4n243]
  exact h4n244_arithmetic

#print axioms h4n244_arithmetic
end StackSorting.RationalLift
