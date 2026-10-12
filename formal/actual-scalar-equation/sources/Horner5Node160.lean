import BivariateRowEquality
import Horner5Node023
import Horner5Node159
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p160 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 18), (Int.ofNat 18)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 17)]]

theorem h5n160_arithmetic_row0 :
    (BiPoly.mul h5p23 h5p159).getD 0 []=h5p160.getD 0 [] := by
  decide +kernel

theorem h5n160_arithmetic_row1 :
    (BiPoly.mul h5p23 h5p159).getD 1 []=h5p160.getD 1 [] := by
  decide +kernel

theorem h5n160_arithmetic : BiPoly.mul h5p23 h5p159=h5p160 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p23 h5p159).getD j.val []=h5p160.getD j.val [] :=
      (fun j => Fin.cases h5n160_arithmetic_row0 (fun j => Fin.cases h5n160_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n160 : h5e160.toBi mapPolyEnv=h5p160 := by
  change BiPoly.mul (h5e23.toBi mapPolyEnv) (h5e159.toBi mapPolyEnv)=h5p160
  rw [h5n23, h5n159]
  exact h5n160_arithmetic

#print axioms h5n160_arithmetic
end StackSorting.RationalLift
