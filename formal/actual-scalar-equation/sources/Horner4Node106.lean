import BivariateRowEquality
import Horner4Base
import Horner4Node105
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p106 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 11), (Int.negSucc 35)]]

theorem h4n106_arithmetic_row0 :
    (BiPoly.mul h4p9 h4p105).getD 0 []=h4p106.getD 0 [] := by
  decide +kernel

theorem h4n106_arithmetic : BiPoly.mul h4p9 h4p105=h4p106 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<1 at hk
    have hf : ∀ j : Fin 1, (BiPoly.mul h4p9 h4p105).getD j.val []=h4p106.getD j.val [] :=
      (fun j => Fin.cases h4n106_arithmetic_row0 (fun j => Fin.elim0 j) j)
    exact hf ⟨k,hk⟩

theorem h4n106 : h4e106.toBi mapPolyEnv=h4p106 := by
  change BiPoly.mul (h4e9.toBi mapPolyEnv) (h4e105.toBi mapPolyEnv)=h4p106
  rw [h4n9, h4n105]
  exact h4n106_arithmetic

#print axioms h4n106_arithmetic
end StackSorting.RationalLift
