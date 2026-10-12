import BivariateRowEquality
import Horner4Base
import Horner4Node069
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p120 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 6452135999), (Int.negSucc 19257536159), (Int.ofNat 23103701280)], [(Int.ofNat 0), (Int.ofNat 28073960640), (Int.ofNat 76643424288), (Int.negSucc 100515714047), (Int.ofNat 10409285376)], [(Int.ofNat 0), (Int.negSucc 49588249679), (Int.negSucc 132367925735), (Int.ofNat 128976888240), (Int.negSucc 3881302199), (Int.ofNat 1105423488)], [(Int.ofNat 0), (Int.ofNat 45408699360), (Int.ofNat 130662799920), (Int.negSucc 3762027647), (Int.negSucc 62081479151), (Int.ofNat 3991019760)], [(Int.ofNat 0), (Int.negSucc 22709925599), (Int.negSucc 79226169647), (Int.negSucc 127236810119), (Int.ofNat 80782900584), (Int.negSucc 3467111063)], [(Int.ofNat 0), (Int.ofNat 5889764640), (Int.ofNat 28491538992), (Int.ofNat 117002744640), (Int.negSucc 1062216671), (Int.negSucc 12890026847)], [(Int.ofNat 0), (Int.negSucc 622113359), (Int.negSucc 5301382247), (Int.negSucc 44107338791), (Int.negSucc 46025111807), (Int.ofNat 10594183968)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 355250592), (Int.ofNat 6618783600), (Int.ofNat 25109289216), (Int.ofNat 3494900592)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 151917551), (Int.negSucc 4168887983), (Int.negSucc 4448498111)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 52335072), (Int.ofNat 874717920)]]

theorem h4n120_arithmetic_row0 :
    (BiPoly.mul h4p53 h4p69).getD 0 []=h4p120.getD 0 [] := by
  decide +kernel

theorem h4n120_arithmetic_row1 :
    (BiPoly.mul h4p53 h4p69).getD 1 []=h4p120.getD 1 [] := by
  decide +kernel

theorem h4n120_arithmetic_row2 :
    (BiPoly.mul h4p53 h4p69).getD 2 []=h4p120.getD 2 [] := by
  decide +kernel

theorem h4n120_arithmetic_row3 :
    (BiPoly.mul h4p53 h4p69).getD 3 []=h4p120.getD 3 [] := by
  decide +kernel

theorem h4n120_arithmetic_row4 :
    (BiPoly.mul h4p53 h4p69).getD 4 []=h4p120.getD 4 [] := by
  decide +kernel

theorem h4n120_arithmetic_row5 :
    (BiPoly.mul h4p53 h4p69).getD 5 []=h4p120.getD 5 [] := by
  decide +kernel

theorem h4n120_arithmetic_row6 :
    (BiPoly.mul h4p53 h4p69).getD 6 []=h4p120.getD 6 [] := by
  decide +kernel

theorem h4n120_arithmetic_row7 :
    (BiPoly.mul h4p53 h4p69).getD 7 []=h4p120.getD 7 [] := by
  decide +kernel

theorem h4n120_arithmetic_row8 :
    (BiPoly.mul h4p53 h4p69).getD 8 []=h4p120.getD 8 [] := by
  decide +kernel

theorem h4n120_arithmetic_row9 :
    (BiPoly.mul h4p53 h4p69).getD 9 []=h4p120.getD 9 [] := by
  decide +kernel

theorem h4n120_arithmetic : BiPoly.mul h4p53 h4p69=h4p120 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<10 at hk
    have hf : ∀ j : Fin 10, (BiPoly.mul h4p53 h4p69).getD j.val []=h4p120.getD j.val [] :=
      (fun j => Fin.cases h4n120_arithmetic_row0 (fun j => Fin.cases h4n120_arithmetic_row1 (fun j => Fin.cases h4n120_arithmetic_row2 (fun j => Fin.cases h4n120_arithmetic_row3 (fun j => Fin.cases h4n120_arithmetic_row4 (fun j => Fin.cases h4n120_arithmetic_row5 (fun j => Fin.cases h4n120_arithmetic_row6 (fun j => Fin.cases h4n120_arithmetic_row7 (fun j => Fin.cases h4n120_arithmetic_row8 (fun j => Fin.cases h4n120_arithmetic_row9 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n120 : h4e120.toBi mapPolyEnv=h4p120 := by
  change BiPoly.mul (h4e53.toBi mapPolyEnv) (h4e69.toBi mapPolyEnv)=h4p120
  rw [h4n53, h4n69]
  exact h4n120_arithmetic

#print axioms h4n120_arithmetic
end StackSorting.RationalLift
