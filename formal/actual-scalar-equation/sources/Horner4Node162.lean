import BivariateRowEquality
import Horner4Base
import Horner4Node161
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p162 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 36), (Int.ofNat 72)]]

theorem h4n162_arithmetic_row0 :
    (BiPoly.mul h4p9 h4p161).getD 0 []=h4p162.getD 0 [] := by
  decide +kernel

theorem h4n162_arithmetic : BiPoly.mul h4p9 h4p161=h4p162 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<1 at hk
    have hf : ∀ j : Fin 1, (BiPoly.mul h4p9 h4p161).getD j.val []=h4p162.getD j.val [] :=
      (fun j => Fin.cases h4n162_arithmetic_row0 (fun j => Fin.elim0 j) j)
    exact hf ⟨k,hk⟩

theorem h4n162 : h4e162.toBi mapPolyEnv=h4p162 := by
  change BiPoly.mul (h4e9.toBi mapPolyEnv) (h4e161.toBi mapPolyEnv)=h4p162
  rw [h4n9, h4n161]
  exact h4n162_arithmetic

#print axioms h4n162_arithmetic
end StackSorting.RationalLift
