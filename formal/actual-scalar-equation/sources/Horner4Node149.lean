import BivariateRowEquality
import Horner4Base
import Horner4Node148
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p149 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 144), (Int.ofNat 288)]]

theorem h4n149_arithmetic_row0 :
    (BiPoly.mul h4p9 h4p148).getD 0 []=h4p149.getD 0 [] := by
  decide +kernel

theorem h4n149_arithmetic : BiPoly.mul h4p9 h4p148=h4p149 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<1 at hk
    have hf : ∀ j : Fin 1, (BiPoly.mul h4p9 h4p148).getD j.val []=h4p149.getD j.val [] :=
      (fun j => Fin.cases h4n149_arithmetic_row0 (fun j => Fin.elim0 j) j)
    exact hf ⟨k,hk⟩

theorem h4n149 : h4e149.toBi mapPolyEnv=h4p149 := by
  change BiPoly.mul (h4e9.toBi mapPolyEnv) (h4e148.toBi mapPolyEnv)=h4p149
  rw [h4n9, h4n148]
  exact h4n149_arithmetic

#print axioms h4n149_arithmetic
end StackSorting.RationalLift
