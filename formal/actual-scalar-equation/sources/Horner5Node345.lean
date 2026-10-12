import BivariateRowEquality
import Horner5Base
import Horner5Node344
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p345 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 48)], [(Int.ofNat 0), (Int.negSucc 95)]]

theorem h5n345_arithmetic_row0 :
    (BiPoly.mul h5p11 h5p344).getD 0 []=h5p345.getD 0 [] := by
  decide +kernel

theorem h5n345_arithmetic_row1 :
    (BiPoly.mul h5p11 h5p344).getD 1 []=h5p345.getD 1 [] := by
  decide +kernel

theorem h5n345_arithmetic : BiPoly.mul h5p11 h5p344=h5p345 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p11 h5p344).getD j.val []=h5p345.getD j.val [] :=
      (fun j => Fin.cases h5n345_arithmetic_row0 (fun j => Fin.cases h5n345_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n345 : h5e345.toBi mapPolyEnv=h5p345 := by
  change BiPoly.mul (h5e11.toBi mapPolyEnv) (h5e344.toBi mapPolyEnv)=h5p345
  rw [h5n11, h5n344]
  exact h5n345_arithmetic

#print axioms h5n345_arithmetic
end StackSorting.RationalLift
