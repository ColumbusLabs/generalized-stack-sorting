import BivariateRowEquality
import Horner5Base
import Horner5Node334
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p335 : BiPoly.Poly := [[(Int.negSucc 8602847999), (Int.negSucc 8471018879), (Int.ofNat 90761212800), (Int.negSucc 35933155199), (Int.negSucc 30804935039)], [(Int.ofNat 46034795520), (Int.ofNat 27195508224), (Int.negSucc 483670444031), (Int.ofNat 272144524032), (Int.ofNat 106262857728), (Int.negSucc 13879047167)], [(Int.negSucc 103549613759), (Int.negSucc 34150624991), (Int.ofNat 1031662635072), (Int.negSucc 588564773951), (Int.negSucc 118508005631), (Int.ofNat 2227273632), (Int.negSucc 1473897983)], [(Int.ofNat 126662598720), (Int.ofNat 31264770528), (Int.negSucc 1115435989727), (Int.ofNat 274122324192), (Int.ofNat 158888900832), (Int.ofNat 76554280128), (Int.negSucc 5321359679)], [(Int.negSucc 90824833279), (Int.negSucc 37657360383), (Int.ofNat 599567842912), (Int.ofNat 620370782240), (Int.negSucc 304042079103), (Int.negSucc 82500825567), (Int.ofNat 4622814752)], [(Int.ofNat 38132920320), (Int.ofNat 37077870080), (Int.negSucc 75082395743), (Int.negSucc 968070101183), (Int.ofNat 157396632896), (Int.ofNat 21921249568), (Int.ofNat 17186702464)], [(Int.negSucc 8682503999), (Int.negSucc 19839200799), (Int.negSucc 85880784799), (Int.ofNat 532748531488), (Int.ofNat 208606830944), (Int.negSucc 18444448895), (Int.negSucc 14125578623)], [(Int.ofNat 829484480), (Int.ofNat 5053723680), (Int.ofNat 45481965952), (Int.negSucc 99707244191), (Int.negSucc 269349307775), (Int.negSucc 422051327), (Int.negSucc 4659867455)], [(Int.ofNat 0), (Int.negSucc 473667455), (Int.negSucc 7606599167), (Int.negSucc 12157321727), (Int.ofNat 101165549952), (Int.ofNat 31400781312), (Int.ofNat 5931330816)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 202556736), (Int.ofNat 5020627200), (Int.negSucc 9717490751), (Int.negSucc 20196353663), (Int.negSucc 1166290559)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 69780095), (Int.negSucc 956950271), (Int.ofNat 3498871680)]]

theorem h5n335_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p334).getD 0 []=h5p335.getD 0 [] := by
  decide +kernel

theorem h5n335_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p334).getD 1 []=h5p335.getD 1 [] := by
  decide +kernel

theorem h5n335_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p334).getD 2 []=h5p335.getD 2 [] := by
  decide +kernel

theorem h5n335_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p334).getD 3 []=h5p335.getD 3 [] := by
  decide +kernel

theorem h5n335_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p334).getD 4 []=h5p335.getD 4 [] := by
  decide +kernel

theorem h5n335_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p334).getD 5 []=h5p335.getD 5 [] := by
  decide +kernel

theorem h5n335_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p334).getD 6 []=h5p335.getD 6 [] := by
  decide +kernel

theorem h5n335_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p334).getD 7 []=h5p335.getD 7 [] := by
  decide +kernel

theorem h5n335_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p334).getD 8 []=h5p335.getD 8 [] := by
  decide +kernel

theorem h5n335_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p334).getD 9 []=h5p335.getD 9 [] := by
  decide +kernel

theorem h5n335_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p334).getD 10 []=h5p335.getD 10 [] := by
  decide +kernel

theorem h5n335_arithmetic : BiPoly.mul h5p6 h5p334=h5p335 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p334).getD j.val []=h5p335.getD j.val [] :=
      (fun j => Fin.cases h5n335_arithmetic_row0 (fun j => Fin.cases h5n335_arithmetic_row1 (fun j => Fin.cases h5n335_arithmetic_row2 (fun j => Fin.cases h5n335_arithmetic_row3 (fun j => Fin.cases h5n335_arithmetic_row4 (fun j => Fin.cases h5n335_arithmetic_row5 (fun j => Fin.cases h5n335_arithmetic_row6 (fun j => Fin.cases h5n335_arithmetic_row7 (fun j => Fin.cases h5n335_arithmetic_row8 (fun j => Fin.cases h5n335_arithmetic_row9 (fun j => Fin.cases h5n335_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n335 : h5e335.toBi mapPolyEnv=h5p335 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e334.toBi mapPolyEnv)=h5p335
  rw [h5n6, h5n334]
  exact h5n335_arithmetic

#print axioms h5n335_arithmetic
end StackSorting.RationalLift
