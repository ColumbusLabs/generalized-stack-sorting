import BivariateRowEquality
import Horner5Node023
import Horner5Node211
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p212 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 216), (Int.ofNat 216)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 215)]]

theorem h5n212_arithmetic_row0 :
    (BiPoly.mul h5p23 h5p211).getD 0 []=h5p212.getD 0 [] := by
  decide +kernel

theorem h5n212_arithmetic_row1 :
    (BiPoly.mul h5p23 h5p211).getD 1 []=h5p212.getD 1 [] := by
  decide +kernel

theorem h5n212_arithmetic : BiPoly.mul h5p23 h5p211=h5p212 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p23 h5p211).getD j.val []=h5p212.getD j.val [] :=
      (fun j => Fin.cases h5n212_arithmetic_row0 (fun j => Fin.cases h5n212_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n212 : h5e212.toBi mapPolyEnv=h5p212 := by
  change BiPoly.mul (h5e23.toBi mapPolyEnv) (h5e211.toBi mapPolyEnv)=h5p212
  rw [h5n23, h5n211]
  exact h5n212_arithmetic

#print axioms h5n212_arithmetic
end StackSorting.RationalLift
