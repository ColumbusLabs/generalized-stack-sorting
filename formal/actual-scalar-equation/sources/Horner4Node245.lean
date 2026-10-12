import BivariateRowEquality
import Horner4Base
import Horner4Node244
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p245 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 3778090704), (Int.ofNat 17292306816), (Int.negSucc 128979503), (Int.negSucc 39202460639)], [(Int.ofNat 0), (Int.negSucc 18450245711), (Int.negSucc 90529284863), (Int.negSucc 21267582671), (Int.ofNat 166612311840), (Int.negSucc 10735393151)], [(Int.ofNat 0), (Int.ofNat 42560407696), (Int.ofNat 183464849488), (Int.ofNat 65462018912), (Int.negSucc 261512970063), (Int.ofNat 1905498272), (Int.ofNat 54482560)], [(Int.ofNat 0), (Int.negSucc 59354943255), (Int.negSucc 185730055047), (Int.negSucc 101752058663), (Int.ofNat 96862425384), (Int.ofNat 63583278992), (Int.negSucc 1976916287)], [(Int.ofNat 0), (Int.ofNat 52143931464), (Int.ofNat 107507334304), (Int.ofNat 105155304856), (Int.ofNat 149588307360), (Int.negSucc 97344452271), (Int.negSucc 3311237151)], [(Int.ofNat 0), (Int.negSucc 28038416839), (Int.negSucc 48178848271), (Int.negSucc 70120127895), (Int.negSucc 167164458439), (Int.ofNat 12354535288), (Int.ofNat 6038114640)], [(Int.ofNat 0), (Int.ofNat 8599525656), (Int.ofNat 24065047928), (Int.ofNat 31987744448), (Int.ofNat 59312165112), (Int.ofNat 46329247520), (Int.ofNat 1455844320)], [(Int.ofNat 0), (Int.negSucc 1299870255), (Int.negSucc 10089527415), (Int.negSucc 12307178823), (Int.negSucc 5360912111), (Int.negSucc 23409209327), (Int.negSucc 3995610335)], [(Int.ofNat 0), (Int.ofNat 61520544), (Int.ofNat 2512928616), (Int.ofNat 3459558528), (Int.negSucc 1483216799), (Int.ofNat 2885550336), (Int.ofNat 1142235648)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 294359615), (Int.negSucc 404231183), (Int.ofNat 368976096)]]

theorem h4n245_arithmetic_row0 :
    (BiPoly.mul h4p7 h4p244).getD 0 []=h4p245.getD 0 [] := by
  decide +kernel

theorem h4n245_arithmetic_row1 :
    (BiPoly.mul h4p7 h4p244).getD 1 []=h4p245.getD 1 [] := by
  decide +kernel

theorem h4n245_arithmetic_row2 :
    (BiPoly.mul h4p7 h4p244).getD 2 []=h4p245.getD 2 [] := by
  decide +kernel

theorem h4n245_arithmetic_row3 :
    (BiPoly.mul h4p7 h4p244).getD 3 []=h4p245.getD 3 [] := by
  decide +kernel

theorem h4n245_arithmetic_row4 :
    (BiPoly.mul h4p7 h4p244).getD 4 []=h4p245.getD 4 [] := by
  decide +kernel

theorem h4n245_arithmetic_row5 :
    (BiPoly.mul h4p7 h4p244).getD 5 []=h4p245.getD 5 [] := by
  decide +kernel

theorem h4n245_arithmetic_row6 :
    (BiPoly.mul h4p7 h4p244).getD 6 []=h4p245.getD 6 [] := by
  decide +kernel

theorem h4n245_arithmetic_row7 :
    (BiPoly.mul h4p7 h4p244).getD 7 []=h4p245.getD 7 [] := by
  decide +kernel

theorem h4n245_arithmetic_row8 :
    (BiPoly.mul h4p7 h4p244).getD 8 []=h4p245.getD 8 [] := by
  decide +kernel

theorem h4n245_arithmetic_row9 :
    (BiPoly.mul h4p7 h4p244).getD 9 []=h4p245.getD 9 [] := by
  decide +kernel

theorem h4n245_arithmetic : BiPoly.mul h4p7 h4p244=h4p245 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<10 at hk
    have hf : ∀ j : Fin 10, (BiPoly.mul h4p7 h4p244).getD j.val []=h4p245.getD j.val [] :=
      (fun j => Fin.cases h4n245_arithmetic_row0 (fun j => Fin.cases h4n245_arithmetic_row1 (fun j => Fin.cases h4n245_arithmetic_row2 (fun j => Fin.cases h4n245_arithmetic_row3 (fun j => Fin.cases h4n245_arithmetic_row4 (fun j => Fin.cases h4n245_arithmetic_row5 (fun j => Fin.cases h4n245_arithmetic_row6 (fun j => Fin.cases h4n245_arithmetic_row7 (fun j => Fin.cases h4n245_arithmetic_row8 (fun j => Fin.cases h4n245_arithmetic_row9 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n245 : h4e245.toBi mapPolyEnv=h4p245 := by
  change BiPoly.mul (h4e7.toBi mapPolyEnv) (h4e244.toBi mapPolyEnv)=h4p245
  rw [h4n7, h4n244]
  exact h4n245_arithmetic

#print axioms h4n245_arithmetic
end StackSorting.RationalLift
