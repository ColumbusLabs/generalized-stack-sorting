import BivariateRowEquality
import Horner5Node023
import Horner5Node130
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p131 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 35), (Int.negSucc 35)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 36)]]

theorem h5n131_arithmetic_row0 :
    (BiPoly.mul h5p23 h5p130).getD 0 []=h5p131.getD 0 [] := by
  decide +kernel

theorem h5n131_arithmetic_row1 :
    (BiPoly.mul h5p23 h5p130).getD 1 []=h5p131.getD 1 [] := by
  decide +kernel

theorem h5n131_arithmetic : BiPoly.mul h5p23 h5p130=h5p131 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p23 h5p130).getD j.val []=h5p131.getD j.val [] :=
      (fun j => Fin.cases h5n131_arithmetic_row0 (fun j => Fin.cases h5n131_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n131 : h5e131.toBi mapPolyEnv=h5p131 := by
  change BiPoly.mul (h5e23.toBi mapPolyEnv) (h5e130.toBi mapPolyEnv)=h5p131
  rw [h5n23, h5n130]
  exact h5n131_arithmetic

#print axioms h5n131_arithmetic
end StackSorting.RationalLift
