import BivariateRowEquality
import Horner5Base
import Horner5Node253
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p254 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 36), (Int.ofNat 72)]]

theorem h5n254_arithmetic_row0 :
    (BiPoly.mul h5p11 h5p253).getD 0 []=h5p254.getD 0 [] := by
  decide +kernel

theorem h5n254_arithmetic : BiPoly.mul h5p11 h5p253=h5p254 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<1 at hk
    have hf : ∀ j : Fin 1, (BiPoly.mul h5p11 h5p253).getD j.val []=h5p254.getD j.val [] :=
      (fun j => Fin.cases h5n254_arithmetic_row0 (fun j => Fin.elim0 j) j)
    exact hf ⟨k,hk⟩

theorem h5n254 : h5e254.toBi mapPolyEnv=h5p254 := by
  change BiPoly.mul (h5e11.toBi mapPolyEnv) (h5e253.toBi mapPolyEnv)=h5p254
  rw [h5n11, h5n253]
  exact h5n254_arithmetic

#print axioms h5n254_arithmetic
end StackSorting.RationalLift
