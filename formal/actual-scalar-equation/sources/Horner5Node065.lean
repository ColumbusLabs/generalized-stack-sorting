import BivariateRowEquality
import Horner5Base
import Horner5Node064
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p65 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 192), (Int.ofNat 96)], [(Int.ofNat 0), (Int.negSucc 287)]]

theorem h5n65_arithmetic_row0 :
    (BiPoly.mul h5p11 h5p64).getD 0 []=h5p65.getD 0 [] := by
  decide +kernel

theorem h5n65_arithmetic_row1 :
    (BiPoly.mul h5p11 h5p64).getD 1 []=h5p65.getD 1 [] := by
  decide +kernel

theorem h5n65_arithmetic : BiPoly.mul h5p11 h5p64=h5p65 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p11 h5p64).getD j.val []=h5p65.getD j.val [] :=
      (fun j => Fin.cases h5n65_arithmetic_row0 (fun j => Fin.cases h5n65_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n65 : h5e65.toBi mapPolyEnv=h5p65 := by
  change BiPoly.mul (h5e11.toBi mapPolyEnv) (h5e64.toBi mapPolyEnv)=h5p65
  rw [h5n11, h5n64]
  exact h5n65_arithmetic

#print axioms h5n65_arithmetic
end StackSorting.RationalLift
