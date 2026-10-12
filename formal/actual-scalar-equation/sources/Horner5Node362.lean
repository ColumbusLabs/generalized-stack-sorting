import BivariateRowEquality
import Horner5Base
import Horner5Node361
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p362 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 16), (Int.ofNat 8)], [(Int.ofNat 0), (Int.negSucc 23)]]

theorem h5n362_arithmetic_row0 :
    (BiPoly.mul h5p11 h5p361).getD 0 []=h5p362.getD 0 [] := by
  decide +kernel

theorem h5n362_arithmetic_row1 :
    (BiPoly.mul h5p11 h5p361).getD 1 []=h5p362.getD 1 [] := by
  decide +kernel

theorem h5n362_arithmetic : BiPoly.mul h5p11 h5p361=h5p362 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p11 h5p361).getD j.val []=h5p362.getD j.val [] :=
      (fun j => Fin.cases h5n362_arithmetic_row0 (fun j => Fin.cases h5n362_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n362 : h5e362.toBi mapPolyEnv=h5p362 := by
  change BiPoly.mul (h5e11.toBi mapPolyEnv) (h5e361.toBi mapPolyEnv)=h5p362
  rw [h5n11, h5n361]
  exact h5n362_arithmetic

#print axioms h5n362_arithmetic
end StackSorting.RationalLift
