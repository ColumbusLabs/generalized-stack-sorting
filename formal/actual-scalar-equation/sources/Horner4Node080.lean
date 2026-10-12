import BivariateRowEquality
import Horner4Base
import Horner4Node079
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p80 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 24), (Int.ofNat 24)]]

theorem h4n80_arithmetic_row0 :
    (BiPoly.mul h4p9 h4p79).getD 0 []=h4p80.getD 0 [] := by
  decide +kernel

theorem h4n80_arithmetic : BiPoly.mul h4p9 h4p79=h4p80 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<1 at hk
    have hf : ∀ j : Fin 1, (BiPoly.mul h4p9 h4p79).getD j.val []=h4p80.getD j.val [] :=
      (fun j => Fin.cases h4n80_arithmetic_row0 (fun j => Fin.elim0 j) j)
    exact hf ⟨k,hk⟩

theorem h4n80 : h4e80.toBi mapPolyEnv=h4p80 := by
  change BiPoly.mul (h4e9.toBi mapPolyEnv) (h4e79.toBi mapPolyEnv)=h4p80
  rw [h4n9, h4n79]
  exact h4n80_arithmetic

#print axioms h4n80_arithmetic
end StackSorting.RationalLift
