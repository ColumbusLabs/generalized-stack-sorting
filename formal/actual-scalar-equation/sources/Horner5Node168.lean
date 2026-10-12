import BivariateRowEquality
import Horner5Base
import Horner5Node167
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p168 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 23), (Int.negSucc 35)], [(Int.ofNat 0), (Int.ofNat 12)]]

theorem h5n168_arithmetic_row0 :
    (BiPoly.mul h5p11 h5p167).getD 0 []=h5p168.getD 0 [] := by
  decide +kernel

theorem h5n168_arithmetic_row1 :
    (BiPoly.mul h5p11 h5p167).getD 1 []=h5p168.getD 1 [] := by
  decide +kernel

theorem h5n168_arithmetic : BiPoly.mul h5p11 h5p167=h5p168 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p11 h5p167).getD j.val []=h5p168.getD j.val [] :=
      (fun j => Fin.cases h5n168_arithmetic_row0 (fun j => Fin.cases h5n168_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n168 : h5e168.toBi mapPolyEnv=h5p168 := by
  change BiPoly.mul (h5e11.toBi mapPolyEnv) (h5e167.toBi mapPolyEnv)=h5p168
  rw [h5n11, h5n167]
  exact h5n168_arithmetic

#print axioms h5n168_arithmetic
end StackSorting.RationalLift
