import BivariateRowEquality
import Horner5Base
import Horner5Node079
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p80 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 143)], [(Int.ofNat 0), (Int.ofNat 288)]]

theorem h5n80_arithmetic_row0 :
    (BiPoly.mul h5p11 h5p79).getD 0 []=h5p80.getD 0 [] := by
  decide +kernel

theorem h5n80_arithmetic_row1 :
    (BiPoly.mul h5p11 h5p79).getD 1 []=h5p80.getD 1 [] := by
  decide +kernel

theorem h5n80_arithmetic : BiPoly.mul h5p11 h5p79=h5p80 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<2 at hk
    have hf : ∀ j : Fin 2, (BiPoly.mul h5p11 h5p79).getD j.val []=h5p80.getD j.val [] :=
      (fun j => Fin.cases h5n80_arithmetic_row0 (fun j => Fin.cases h5n80_arithmetic_row1 (fun j => Fin.elim0 j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n80 : h5e80.toBi mapPolyEnv=h5p80 := by
  change BiPoly.mul (h5e11.toBi mapPolyEnv) (h5e79.toBi mapPolyEnv)=h5p80
  rw [h5n11, h5n79]
  exact h5n80_arithmetic

#print axioms h5n80_arithmetic
end StackSorting.RationalLift
