import BivariateRowEquality
import Horner5Base
import Horner5Node030
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p31 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 34002816336), (Int.ofNat 121627945008), (Int.negSucc 88785944207), (Int.negSucc 176411072879)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 200055027743), (Int.negSucc 736336481039), (Int.ofNat 467661969792), (Int.ofNat 725600768688), (Int.negSucc 48309269183)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 549095880672), (Int.ofNat 1750799117088), (Int.negSucc 1069848174527), (Int.negSucc 1124273017871), (Int.ofNat 8697327984), (Int.ofNat 245171520)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 917238158567), (Int.negSucc 2022472312991), (Int.ofNat 868447432368), (Int.ofNat 572715166320), (Int.ofNat 281431522296), (Int.negSucc 8896123295)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1003489872480), (Int.ofNat 1101452142384), (Int.ofNat 626827995648), (Int.ofNat 167274690192), (Int.negSucc 436604195519), (Int.negSucc 14900567183)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 721641134735), (Int.negSucc 210239125271), (Int.negSucc 1590610278671), (Int.negSucc 300635485919), (Int.ofNat 84081733920), (Int.ofNat 27171515880)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 329741482464), (Int.ofNat 68107831776), (Int.ofNat 999340618896), (Int.ofNat 327498074208), (Int.ofNat 184585747680), (Int.ofNat 6551299440)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 89094563207), (Int.negSucc 140900883983), (Int.negSucc 207658288223), (Int.negSucc 277505727983), (Int.negSucc 120882864671), (Int.negSucc 17980246511)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 12252517200), (Int.ofNat 89470754784), (Int.negSucc 14424515855), (Int.ofNat 94884316272), (Int.ofNat 33535253232), (Int.ofNat 5140060416)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 553684895), (Int.negSucc 24158224295), (Int.ofNat 10893104640), (Int.negSucc 8754553871), (Int.negSucc 5140060415)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2649236544), (Int.negSucc 1660392431)]]

theorem h5n31_arithmetic_row0 :
    (BiPoly.mul h5p22 h5p30).getD 0 []=h5p31.getD 0 [] := by
  decide +kernel

theorem h5n31_arithmetic_row1 :
    (BiPoly.mul h5p22 h5p30).getD 1 []=h5p31.getD 1 [] := by
  decide +kernel

theorem h5n31_arithmetic_row2 :
    (BiPoly.mul h5p22 h5p30).getD 2 []=h5p31.getD 2 [] := by
  decide +kernel

theorem h5n31_arithmetic_row3 :
    (BiPoly.mul h5p22 h5p30).getD 3 []=h5p31.getD 3 [] := by
  decide +kernel

theorem h5n31_arithmetic_row4 :
    (BiPoly.mul h5p22 h5p30).getD 4 []=h5p31.getD 4 [] := by
  decide +kernel

theorem h5n31_arithmetic_row5 :
    (BiPoly.mul h5p22 h5p30).getD 5 []=h5p31.getD 5 [] := by
  decide +kernel

theorem h5n31_arithmetic_row6 :
    (BiPoly.mul h5p22 h5p30).getD 6 []=h5p31.getD 6 [] := by
  decide +kernel

theorem h5n31_arithmetic_row7 :
    (BiPoly.mul h5p22 h5p30).getD 7 []=h5p31.getD 7 [] := by
  decide +kernel

theorem h5n31_arithmetic_row8 :
    (BiPoly.mul h5p22 h5p30).getD 8 []=h5p31.getD 8 [] := by
  decide +kernel

theorem h5n31_arithmetic_row9 :
    (BiPoly.mul h5p22 h5p30).getD 9 []=h5p31.getD 9 [] := by
  decide +kernel

theorem h5n31_arithmetic_row10 :
    (BiPoly.mul h5p22 h5p30).getD 10 []=h5p31.getD 10 [] := by
  decide +kernel

theorem h5n31_arithmetic : BiPoly.mul h5p22 h5p30=h5p31 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p22 h5p30).getD j.val []=h5p31.getD j.val [] :=
      (fun j => Fin.cases h5n31_arithmetic_row0 (fun j => Fin.cases h5n31_arithmetic_row1 (fun j => Fin.cases h5n31_arithmetic_row2 (fun j => Fin.cases h5n31_arithmetic_row3 (fun j => Fin.cases h5n31_arithmetic_row4 (fun j => Fin.cases h5n31_arithmetic_row5 (fun j => Fin.cases h5n31_arithmetic_row6 (fun j => Fin.cases h5n31_arithmetic_row7 (fun j => Fin.cases h5n31_arithmetic_row8 (fun j => Fin.cases h5n31_arithmetic_row9 (fun j => Fin.cases h5n31_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n31 : h5e31.toBi mapPolyEnv=h5p31 := by
  change BiPoly.mul (h5e22.toBi mapPolyEnv) (h5e30.toBi mapPolyEnv)=h5p31
  rw [h5n22, h5n30]
  exact h5n31_arithmetic

#print axioms h5n31_arithmetic
end StackSorting.RationalLift
