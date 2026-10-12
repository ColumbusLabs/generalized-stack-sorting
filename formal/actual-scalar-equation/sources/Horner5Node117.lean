import BivariateRowEquality
import Horner5Base
import Horner5Node116
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p117 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 36)], [(Int.ofNat 0), (Int.negSucc 71)]]

theorem h5n117_arithmetic_row0 :
    (BiPoly.mul h5p11 h5p116).getD 0 []=h5p117.getD 0 [] := by
  decide +kernel

theorem h5n117_arithmetic_row1 :
    (BiPoly.mul h5p11 h5p116).getD 1 []=h5p117.getD 1 [] := by
  decide +kernel

theorem h5n117_arithmetic : BiPoly.mul h5p11 h5p116=h5p117 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p11 h5p116).getD j.val []=h5p117.getD j.val [] :=
      (fun j => Fin.cases h5n117_arithmetic_row0 (fun j => Fin.cases h5n117_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n117 : h5e117.toBi mapPolyEnv=h5p117 := by
  change BiPoly.mul (h5e11.toBi mapPolyEnv) (h5e116.toBi mapPolyEnv)=h5p117
  rw [h5n11, h5n116]
  exact h5n117_arithmetic

#print axioms h5n117_arithmetic
end StackSorting.RationalLift
