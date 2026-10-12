import BivariateRowEquality
import Horner4Base
import Horner4Node138
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p139 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 68005632671), (Int.negSucc 311261522687), (Int.ofNat 2321631072), (Int.ofNat 705644291520)], [(Int.ofNat 0), (Int.ofNat 332104422816), (Int.ofNat 1629527127552), (Int.ofNat 382816488096), (Int.negSucc 2999021613119), (Int.ofNat 193237076736)], [(Int.ofNat 0), (Int.negSucc 766087338527), (Int.negSucc 3302367290783), (Int.negSucc 1178316340415), (Int.ofNat 4707233461152), (Int.negSucc 34298968895), (Int.negSucc 980686079)], [(Int.ofNat 0), (Int.ofNat 1068388978608), (Int.ofNat 3343140990864), (Int.ofNat 1831537055952), (Int.negSucc 1743523656911), (Int.negSucc 1144499021855), (Int.ofNat 35584493184)], [(Int.ofNat 0), (Int.negSucc 938590766351), (Int.negSucc 1935132017471), (Int.negSucc 1892795487407), (Int.negSucc 2692589532479), (Int.ofNat 1752200140896), (Int.ofNat 59602268736)], [(Int.ofNat 0), (Int.ofNat 504691503120), (Int.ofNat 867219268896), (Int.ofNat 1262162302128), (Int.ofNat 3008960251920), (Int.negSucc 222381635183), (Int.negSucc 108686063519)], [(Int.ofNat 0), (Int.negSucc 154791461807), (Int.negSucc 433170862703), (Int.negSucc 575779400063), (Int.negSucc 1067618972015), (Int.negSucc 833926455359), (Int.negSucc 26205197759)], [(Int.ofNat 0), (Int.ofNat 23397664608), (Int.ofNat 181611493488), (Int.ofNat 221529218832), (Int.ofNat 96496418016), (Int.ofNat 421365767904), (Int.ofNat 71920986048)], [(Int.ofNat 0), (Int.negSucc 1107369791), (Int.negSucc 45232715087), (Int.negSucc 62272053503), (Int.ofNat 26697902400), (Int.negSucc 51939906047), (Int.negSucc 20560241663)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5298473088), (Int.ofNat 7276161312), (Int.negSucc 6641569727)]]

theorem h4n139_arithmetic_row0 :
    (BiPoly.mul h4p7 h4p138).getD 0 []=h4p139.getD 0 [] := by
  decide +kernel

theorem h4n139_arithmetic_row1 :
    (BiPoly.mul h4p7 h4p138).getD 1 []=h4p139.getD 1 [] := by
  decide +kernel

theorem h4n139_arithmetic_row2 :
    (BiPoly.mul h4p7 h4p138).getD 2 []=h4p139.getD 2 [] := by
  decide +kernel

theorem h4n139_arithmetic_row3 :
    (BiPoly.mul h4p7 h4p138).getD 3 []=h4p139.getD 3 [] := by
  decide +kernel

theorem h4n139_arithmetic_row4 :
    (BiPoly.mul h4p7 h4p138).getD 4 []=h4p139.getD 4 [] := by
  decide +kernel

theorem h4n139_arithmetic_row5 :
    (BiPoly.mul h4p7 h4p138).getD 5 []=h4p139.getD 5 [] := by
  decide +kernel

theorem h4n139_arithmetic_row6 :
    (BiPoly.mul h4p7 h4p138).getD 6 []=h4p139.getD 6 [] := by
  decide +kernel

theorem h4n139_arithmetic_row7 :
    (BiPoly.mul h4p7 h4p138).getD 7 []=h4p139.getD 7 [] := by
  decide +kernel

theorem h4n139_arithmetic_row8 :
    (BiPoly.mul h4p7 h4p138).getD 8 []=h4p139.getD 8 [] := by
  decide +kernel

theorem h4n139_arithmetic_row9 :
    (BiPoly.mul h4p7 h4p138).getD 9 []=h4p139.getD 9 [] := by
  decide +kernel

theorem h4n139_arithmetic : BiPoly.mul h4p7 h4p138=h4p139 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<10 at hk
    have hf : ∀ j : Fin 10, (BiPoly.mul h4p7 h4p138).getD j.val []=h4p139.getD j.val [] :=
      (fun j => Fin.cases h4n139_arithmetic_row0 (fun j => Fin.cases h4n139_arithmetic_row1 (fun j => Fin.cases h4n139_arithmetic_row2 (fun j => Fin.cases h4n139_arithmetic_row3 (fun j => Fin.cases h4n139_arithmetic_row4 (fun j => Fin.cases h4n139_arithmetic_row5 (fun j => Fin.cases h4n139_arithmetic_row6 (fun j => Fin.cases h4n139_arithmetic_row7 (fun j => Fin.cases h4n139_arithmetic_row8 (fun j => Fin.cases h4n139_arithmetic_row9 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n139 : h4e139.toBi mapPolyEnv=h4p139 := by
  change BiPoly.mul (h4e7.toBi mapPolyEnv) (h4e138.toBi mapPolyEnv)=h4p139
  rw [h4n7, h4n138]
  exact h4n139_arithmetic

#print axioms h4n139_arithmetic
end StackSorting.RationalLift
