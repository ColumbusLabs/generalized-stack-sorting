import BivariateRowEquality
import Horner5Node023
import Horner5Node228
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p229 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 215), (Int.negSucc 215)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 216)]]

theorem h5n229_arithmetic_row0 :
    (BiPoly.mul h5p23 h5p228).getD 0 []=h5p229.getD 0 [] := by
  decide +kernel

theorem h5n229_arithmetic_row1 :
    (BiPoly.mul h5p23 h5p228).getD 1 []=h5p229.getD 1 [] := by
  decide +kernel

theorem h5n229_arithmetic : BiPoly.mul h5p23 h5p228=h5p229 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p23 h5p228).getD j.val []=h5p229.getD j.val [] :=
      (fun j => Fin.cases h5n229_arithmetic_row0 (fun j => Fin.cases h5n229_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n229 : h5e229.toBi mapPolyEnv=h5p229 := by
  change BiPoly.mul (h5e23.toBi mapPolyEnv) (h5e228.toBi mapPolyEnv)=h5p229
  rw [h5n23, h5n228]
  exact h5n229_arithmetic

#print axioms h5n229_arithmetic
end StackSorting.RationalLift
