import BivariateRowEquality
import Horner5Base
import Horner5Node414
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p415 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 15), (Int.negSucc 15), (Int.negSucc 31)], [(Int.ofNat 0), (Int.ofNat 16)]]

theorem h5n415_arithmetic_row0 :
    (BiPoly.mul h5p11 h5p414).getD 0 []=h5p415.getD 0 [] := by
  decide +kernel

theorem h5n415_arithmetic_row1 :
    (BiPoly.mul h5p11 h5p414).getD 1 []=h5p415.getD 1 [] := by
  decide +kernel

theorem h5n415_arithmetic : BiPoly.mul h5p11 h5p414=h5p415 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p11 h5p414).getD j.val []=h5p415.getD j.val [] :=
      (fun j => Fin.cases h5n415_arithmetic_row0 (fun j => Fin.cases h5n415_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n415 : h5e415.toBi mapPolyEnv=h5p415 := by
  change BiPoly.mul (h5e11.toBi mapPolyEnv) (h5e414.toBi mapPolyEnv)=h5p415
  rw [h5n11, h5n414]
  exact h5n415_arithmetic

#print axioms h5n415_arithmetic
end StackSorting.RationalLift
