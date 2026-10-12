import BivariateRowEquality
import Horner5Base
import Horner5Node043
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p44 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 143), (Int.ofNat 144)], [(Int.ofNat 0), (Int.ofNat 144), (Int.negSucc 287)]]

theorem h5n44_arithmetic_row0 :
    (BiPoly.mul h5p11 h5p43).getD 0 []=h5p44.getD 0 [] := by
  decide +kernel

theorem h5n44_arithmetic_row1 :
    (BiPoly.mul h5p11 h5p43).getD 1 []=h5p44.getD 1 [] := by
  decide +kernel

theorem h5n44_arithmetic : BiPoly.mul h5p11 h5p43=h5p44 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p11 h5p43).getD j.val []=h5p44.getD j.val [] :=
      (fun j => Fin.cases h5n44_arithmetic_row0 (fun j => Fin.cases h5n44_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n44 : h5e44.toBi mapPolyEnv=h5p44 := by
  change BiPoly.mul (h5e11.toBi mapPolyEnv) (h5e43.toBi mapPolyEnv)=h5p44
  rw [h5n11, h5n43]
  exact h5n44_arithmetic

#print axioms h5n44_arithmetic
end StackSorting.RationalLift
