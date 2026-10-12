import BivariateRowEquality
import Horner5Node023
import Horner5Node195
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p196 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 48), (Int.ofNat 48)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 47)]]

theorem h5n196_arithmetic_row0 :
    (BiPoly.mul h5p23 h5p195).getD 0 []=h5p196.getD 0 [] := by
  decide +kernel

theorem h5n196_arithmetic_row1 :
    (BiPoly.mul h5p23 h5p195).getD 1 []=h5p196.getD 1 [] := by
  decide +kernel

theorem h5n196_arithmetic : BiPoly.mul h5p23 h5p195=h5p196 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p23 h5p195).getD j.val []=h5p196.getD j.val [] :=
      (fun j => Fin.cases h5n196_arithmetic_row0 (fun j => Fin.cases h5n196_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n196 : h5e196.toBi mapPolyEnv=h5p196 := by
  change BiPoly.mul (h5e23.toBi mapPolyEnv) (h5e195.toBi mapPolyEnv)=h5p196
  rw [h5n23, h5n195]
  exact h5n196_arithmetic

#print axioms h5n196_arithmetic
end StackSorting.RationalLift
