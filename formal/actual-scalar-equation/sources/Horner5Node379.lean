import BivariateRowEquality
import Horner5Base
import Horner5Node378
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p379 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 12), (Int.negSucc 11)], [(Int.ofNat 0), (Int.negSucc 11), (Int.ofNat 24)]]

theorem h5n379_arithmetic_row0 :
    (BiPoly.mul h5p11 h5p378).getD 0 []=h5p379.getD 0 [] := by
  decide +kernel

theorem h5n379_arithmetic_row1 :
    (BiPoly.mul h5p11 h5p378).getD 1 []=h5p379.getD 1 [] := by
  decide +kernel

theorem h5n379_arithmetic : BiPoly.mul h5p11 h5p378=h5p379 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p11 h5p378).getD j.val []=h5p379.getD j.val [] :=
      (fun j => Fin.cases h5n379_arithmetic_row0 (fun j => Fin.cases h5n379_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n379 : h5e379.toBi mapPolyEnv=h5p379 := by
  change BiPoly.mul (h5e11.toBi mapPolyEnv) (h5e378.toBi mapPolyEnv)=h5p379
  rw [h5n11, h5n378]
  exact h5n379_arithmetic

#print axioms h5n379_arithmetic
end StackSorting.RationalLift
