import BivariateRowEquality
import Horner5Base
import Horner5Node040
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p41 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 144)], [(Int.ofNat 0), (Int.negSucc 287)]]

theorem h5n41_arithmetic_row0 :
    (BiPoly.mul h5p11 h5p40).getD 0 []=h5p41.getD 0 [] := by
  decide +kernel

theorem h5n41_arithmetic_row1 :
    (BiPoly.mul h5p11 h5p40).getD 1 []=h5p41.getD 1 [] := by
  decide +kernel

theorem h5n41_arithmetic : BiPoly.mul h5p11 h5p40=h5p41 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p11 h5p40).getD j.val []=h5p41.getD j.val [] :=
      (fun j => Fin.cases h5n41_arithmetic_row0 (fun j => Fin.cases h5n41_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n41 : h5e41.toBi mapPolyEnv=h5p41 := by
  change BiPoly.mul (h5e11.toBi mapPolyEnv) (h5e40.toBi mapPolyEnv)=h5p41
  rw [h5n11, h5n40]
  exact h5n41_arithmetic

#print axioms h5n41_arithmetic
end StackSorting.RationalLift
