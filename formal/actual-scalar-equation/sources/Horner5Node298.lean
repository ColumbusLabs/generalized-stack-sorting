import BivariateRowEquality
import Horner5Base
import Horner5Node297
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p298 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 64), (Int.ofNat 32)], [(Int.ofNat 0), (Int.negSucc 95)]]

theorem h5n298_arithmetic_row0 :
    (BiPoly.mul h5p11 h5p297).getD 0 []=h5p298.getD 0 [] := by
  decide +kernel

theorem h5n298_arithmetic_row1 :
    (BiPoly.mul h5p11 h5p297).getD 1 []=h5p298.getD 1 [] := by
  decide +kernel

theorem h5n298_arithmetic : BiPoly.mul h5p11 h5p297=h5p298 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p11 h5p297).getD j.val []=h5p298.getD j.val [] :=
      (fun j => Fin.cases h5n298_arithmetic_row0 (fun j => Fin.cases h5n298_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n298 : h5e298.toBi mapPolyEnv=h5p298 := by
  change BiPoly.mul (h5e11.toBi mapPolyEnv) (h5e297.toBi mapPolyEnv)=h5p298
  rw [h5n11, h5n297]
  exact h5n298_arithmetic

#print axioms h5n298_arithmetic
end StackSorting.RationalLift
