import BivariateRowEquality
import Horner5Node023
import Horner5Node186
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p187 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 59), (Int.negSucc 59)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 60)]]

theorem h5n187_arithmetic_row0 :
    (BiPoly.mul h5p23 h5p186).getD 0 []=h5p187.getD 0 [] := by
  decide +kernel

theorem h5n187_arithmetic_row1 :
    (BiPoly.mul h5p23 h5p186).getD 1 []=h5p187.getD 1 [] := by
  decide +kernel

theorem h5n187_arithmetic : BiPoly.mul h5p23 h5p186=h5p187 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p23 h5p186).getD j.val []=h5p187.getD j.val [] :=
      (fun j => Fin.cases h5n187_arithmetic_row0 (fun j => Fin.cases h5n187_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n187 : h5e187.toBi mapPolyEnv=h5p187 := by
  change BiPoly.mul (h5e23.toBi mapPolyEnv) (h5e186.toBi mapPolyEnv)=h5p187
  rw [h5n23, h5n186]
  exact h5n187_arithmetic

#print axioms h5n187_arithmetic
end StackSorting.RationalLift
