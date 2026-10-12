import BivariateRowEquality
import Horner5Base
import Horner5Node139
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p140 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 24), (Int.ofNat 0), (Int.ofNat 24)], [(Int.ofNat 0), (Int.negSucc 23), (Int.ofNat 24)]]

theorem h5n140_arithmetic_row0 :
    (BiPoly.mul h5p11 h5p139).getD 0 []=h5p140.getD 0 [] := by
  decide +kernel

theorem h5n140_arithmetic_row1 :
    (BiPoly.mul h5p11 h5p139).getD 1 []=h5p140.getD 1 [] := by
  decide +kernel

theorem h5n140_arithmetic : BiPoly.mul h5p11 h5p139=h5p140 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p11 h5p139).getD j.val []=h5p140.getD j.val [] :=
      (fun j => Fin.cases h5n140_arithmetic_row0 (fun j => Fin.cases h5n140_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n140 : h5e140.toBi mapPolyEnv=h5p140 := by
  change BiPoly.mul (h5e11.toBi mapPolyEnv) (h5e139.toBi mapPolyEnv)=h5p140
  rw [h5n11, h5n139]
  exact h5n140_arithmetic

#print axioms h5n140_arithmetic
end StackSorting.RationalLift
