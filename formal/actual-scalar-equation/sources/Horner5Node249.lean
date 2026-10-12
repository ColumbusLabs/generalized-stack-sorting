import BivariateRowEquality
import Horner5Node023
import Horner5Node248
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p249 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 53), (Int.negSucc 53)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 54)]]

theorem h5n249_arithmetic_row0 :
    (BiPoly.mul h5p23 h5p248).getD 0 []=h5p249.getD 0 [] := by
  decide +kernel

theorem h5n249_arithmetic_row1 :
    (BiPoly.mul h5p23 h5p248).getD 1 []=h5p249.getD 1 [] := by
  decide +kernel

theorem h5n249_arithmetic : BiPoly.mul h5p23 h5p248=h5p249 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p23 h5p248).getD j.val []=h5p249.getD j.val [] :=
      (fun j => Fin.cases h5n249_arithmetic_row0 (fun j => Fin.cases h5n249_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n249 : h5e249.toBi mapPolyEnv=h5p249 := by
  change BiPoly.mul (h5e23.toBi mapPolyEnv) (h5e248.toBi mapPolyEnv)=h5p249
  rw [h5n23, h5n248]
  exact h5n249_arithmetic

#print axioms h5n249_arithmetic
end StackSorting.RationalLift
