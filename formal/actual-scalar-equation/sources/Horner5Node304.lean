import BivariateRowEquality
import Horner5Node023
import Horner5Node303
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p304 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 23), (Int.negSucc 23)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 24)]]

theorem h5n304_arithmetic_row0 :
    (BiPoly.mul h5p23 h5p303).getD 0 []=h5p304.getD 0 [] := by
  decide +kernel

theorem h5n304_arithmetic_row1 :
    (BiPoly.mul h5p23 h5p303).getD 1 []=h5p304.getD 1 [] := by
  decide +kernel

theorem h5n304_arithmetic : BiPoly.mul h5p23 h5p303=h5p304 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p23 h5p303).getD j.val []=h5p304.getD j.val [] :=
      (fun j => Fin.cases h5n304_arithmetic_row0 (fun j => Fin.cases h5n304_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n304 : h5e304.toBi mapPolyEnv=h5p304 := by
  change BiPoly.mul (h5e23.toBi mapPolyEnv) (h5e303.toBi mapPolyEnv)=h5p304
  rw [h5n23, h5n303]
  exact h5n304_arithmetic

#print axioms h5n304_arithmetic
end StackSorting.RationalLift
