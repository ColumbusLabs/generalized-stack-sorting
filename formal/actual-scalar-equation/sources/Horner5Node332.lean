import BivariateRowEquality
import Horner5Base
import Horner5Node331
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p332 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 63), (Int.negSucc 31)], [(Int.ofNat 0), (Int.ofNat 96)]]

theorem h5n332_arithmetic_row0 :
    (BiPoly.mul h5p11 h5p331).getD 0 []=h5p332.getD 0 [] := by
  decide +kernel

theorem h5n332_arithmetic_row1 :
    (BiPoly.mul h5p11 h5p331).getD 1 []=h5p332.getD 1 [] := by
  decide +kernel

theorem h5n332_arithmetic : BiPoly.mul h5p11 h5p331=h5p332 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p11 h5p331).getD j.val []=h5p332.getD j.val [] :=
      (fun j => Fin.cases h5n332_arithmetic_row0 (fun j => Fin.cases h5n332_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n332 : h5e332.toBi mapPolyEnv=h5p332 := by
  change BiPoly.mul (h5e11.toBi mapPolyEnv) (h5e331.toBi mapPolyEnv)=h5p332
  rw [h5n11, h5n331]
  exact h5n332_arithmetic

#print axioms h5n332_arithmetic
end StackSorting.RationalLift
