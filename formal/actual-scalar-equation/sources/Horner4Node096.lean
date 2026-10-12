import BivariateRowEquality
import Horner4Base
import Horner4Node071
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p96 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 8500704084), (Int.ofNat 21906282168), (Int.negSucc 44102768219)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 41513052851), (Int.negSucc 120664785239), (Int.ofNat 193477509468), (Int.negSucc 12077317295)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 95760917316), (Int.ofNat 221274076716), (Int.negSucc 295258610879), (Int.ofNat 2113039116), (Int.ofNat 61292880)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 133548622325), (Int.negSucc 150795379205), (Int.ofNat 72648626418), (Int.ofNat 72643204278), (Int.negSucc 2224030823)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 117323845794), (Int.ofNat 7243810596), (Int.ofNat 222111814734), (Int.negSucc 107649937907), (Int.negSucc 3725141795)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 63086437889), (Int.ofNat 17770467168), (Int.negSucc 193311222101), (Int.ofNat 10502412714), (Int.ofNat 6792878970)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 19348932726), (Int.ofNat 15448492386), (Int.ofNat 41075440236), (Int.ofNat 51301491030), (Int.ofNat 1637824860)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2924708075), (Int.negSucc 16852020533), (Int.ofNat 6012888714), (Int.negSucc 24087829679), (Int.negSucc 4495061627)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 138421224), (Int.ofNat 5377246938), (Int.negSucc 2970487187), (Int.ofNat 2603736576), (Int.ofNat 1285015104)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 662309135), (Int.ofNat 415098108)]]

theorem h4n96_arithmetic_row0 :
    (BiPoly.mul h4p95 h4p71).getD 0 []=h4p96.getD 0 [] := by
  decide +kernel

theorem h4n96_arithmetic_row1 :
    (BiPoly.mul h4p95 h4p71).getD 1 []=h4p96.getD 1 [] := by
  decide +kernel

theorem h4n96_arithmetic_row2 :
    (BiPoly.mul h4p95 h4p71).getD 2 []=h4p96.getD 2 [] := by
  decide +kernel

theorem h4n96_arithmetic_row3 :
    (BiPoly.mul h4p95 h4p71).getD 3 []=h4p96.getD 3 [] := by
  decide +kernel

theorem h4n96_arithmetic_row4 :
    (BiPoly.mul h4p95 h4p71).getD 4 []=h4p96.getD 4 [] := by
  decide +kernel

theorem h4n96_arithmetic_row5 :
    (BiPoly.mul h4p95 h4p71).getD 5 []=h4p96.getD 5 [] := by
  decide +kernel

theorem h4n96_arithmetic_row6 :
    (BiPoly.mul h4p95 h4p71).getD 6 []=h4p96.getD 6 [] := by
  decide +kernel

theorem h4n96_arithmetic_row7 :
    (BiPoly.mul h4p95 h4p71).getD 7 []=h4p96.getD 7 [] := by
  decide +kernel

theorem h4n96_arithmetic_row8 :
    (BiPoly.mul h4p95 h4p71).getD 8 []=h4p96.getD 8 [] := by
  decide +kernel

theorem h4n96_arithmetic_row9 :
    (BiPoly.mul h4p95 h4p71).getD 9 []=h4p96.getD 9 [] := by
  decide +kernel

theorem h4n96_arithmetic : BiPoly.mul h4p95 h4p71=h4p96 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<10 at hk
    have hf : ∀ j : Fin 10, (BiPoly.mul h4p95 h4p71).getD j.val []=h4p96.getD j.val [] :=
      (fun j => Fin.cases h4n96_arithmetic_row0 (fun j => Fin.cases h4n96_arithmetic_row1 (fun j => Fin.cases h4n96_arithmetic_row2 (fun j => Fin.cases h4n96_arithmetic_row3 (fun j => Fin.cases h4n96_arithmetic_row4 (fun j => Fin.cases h4n96_arithmetic_row5 (fun j => Fin.cases h4n96_arithmetic_row6 (fun j => Fin.cases h4n96_arithmetic_row7 (fun j => Fin.cases h4n96_arithmetic_row8 (fun j => Fin.cases h4n96_arithmetic_row9 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n96 : h4e96.toBi mapPolyEnv=h4p96 := by
  change BiPoly.mul (h4e95.toBi mapPolyEnv) (h4e71.toBi mapPolyEnv)=h4p96
  rw [h4n95, h4n71]
  exact h4n96_arithmetic

#print axioms h4n96_arithmetic
end StackSorting.RationalLift
