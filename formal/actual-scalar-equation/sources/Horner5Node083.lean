import BivariateRowEquality
import Horner5Base
import Horner5Node082
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p83 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 144), (Int.negSucc 143)], [(Int.ofNat 0), (Int.negSucc 143), (Int.ofNat 288)]]

theorem h5n83_arithmetic_row0 :
    (BiPoly.mul h5p11 h5p82).getD 0 []=h5p83.getD 0 [] := by
  decide +kernel

theorem h5n83_arithmetic_row1 :
    (BiPoly.mul h5p11 h5p82).getD 1 []=h5p83.getD 1 [] := by
  decide +kernel

theorem h5n83_arithmetic : BiPoly.mul h5p11 h5p82=h5p83 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p11 h5p82).getD j.val []=h5p83.getD j.val [] :=
      (fun j => Fin.cases h5n83_arithmetic_row0 (fun j => Fin.cases h5n83_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n83 : h5e83.toBi mapPolyEnv=h5p83 := by
  change BiPoly.mul (h5e11.toBi mapPolyEnv) (h5e82.toBi mapPolyEnv)=h5p83
  rw [h5n11, h5n82]
  exact h5n83_arithmetic

#print axioms h5n83_arithmetic
end StackSorting.RationalLift
