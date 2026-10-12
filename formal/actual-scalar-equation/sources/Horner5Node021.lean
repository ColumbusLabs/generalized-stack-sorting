import BivariateRowEquality
import Horner5Base
import Horner5Node020
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p21 : BiPoly.Poly := [[(Int.negSucc 25808543999), (Int.negSucc 25413056639), (Int.ofNat 272283638400), (Int.negSucc 107799465599), (Int.negSucc 92414805119)], [(Int.ofNat 138104386560), (Int.ofNat 81586524672), (Int.negSucc 1451011332095), (Int.ofNat 816433572096), (Int.ofNat 318788573184), (Int.negSucc 41637141503)], [(Int.negSucc 310648841279), (Int.negSucc 102451874975), (Int.ofNat 3094987905216), (Int.negSucc 1765694321855), (Int.negSucc 355524016895), (Int.ofNat 6681820896), (Int.negSucc 4421693951)], [(Int.ofNat 379987796160), (Int.ofNat 93794311584), (Int.negSucc 3346307969183), (Int.ofNat 822366972576), (Int.ofNat 476666702496), (Int.ofNat 229662840384), (Int.negSucc 15964079039)], [(Int.negSucc 272474499839), (Int.negSucc 112972081151), (Int.ofNat 1798703528736), (Int.ofNat 1861112346720), (Int.negSucc 912126237311), (Int.negSucc 247502476703), (Int.ofNat 13868444256)], [(Int.ofNat 114398760960), (Int.ofNat 111233610240), (Int.negSucc 225247187231), (Int.negSucc 2904210303551), (Int.ofNat 472189898688), (Int.ofNat 65763748704), (Int.ofNat 51560107392)], [(Int.negSucc 26047511999), (Int.negSucc 59517602399), (Int.negSucc 257642354399), (Int.ofNat 1598245594464), (Int.ofNat 625820492832), (Int.negSucc 55333346687), (Int.negSucc 42376735871)], [(Int.ofNat 2488453440), (Int.ofNat 15161171040), (Int.ofNat 136445897856), (Int.negSucc 299121732575), (Int.negSucc 808047923327), (Int.negSucc 1266153983), (Int.negSucc 13979602367)], [(Int.ofNat 0), (Int.negSucc 1421002367), (Int.negSucc 22819797503), (Int.negSucc 36471965183), (Int.ofNat 303496649856), (Int.ofNat 94202343936), (Int.ofNat 17793992448)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 607670208), (Int.ofNat 15061881600), (Int.negSucc 29152472255), (Int.negSucc 60589060991), (Int.negSucc 3498871679)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 209340287), (Int.negSucc 2870850815), (Int.ofNat 10496615040)]]

theorem h5n21_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p20).getD 0 []=h5p21.getD 0 [] := by
  decide +kernel

theorem h5n21_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p20).getD 1 []=h5p21.getD 1 [] := by
  decide +kernel

theorem h5n21_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p20).getD 2 []=h5p21.getD 2 [] := by
  decide +kernel

theorem h5n21_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p20).getD 3 []=h5p21.getD 3 [] := by
  decide +kernel

theorem h5n21_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p20).getD 4 []=h5p21.getD 4 [] := by
  decide +kernel

theorem h5n21_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p20).getD 5 []=h5p21.getD 5 [] := by
  decide +kernel

theorem h5n21_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p20).getD 6 []=h5p21.getD 6 [] := by
  decide +kernel

theorem h5n21_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p20).getD 7 []=h5p21.getD 7 [] := by
  decide +kernel

theorem h5n21_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p20).getD 8 []=h5p21.getD 8 [] := by
  decide +kernel

theorem h5n21_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p20).getD 9 []=h5p21.getD 9 [] := by
  decide +kernel

theorem h5n21_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p20).getD 10 []=h5p21.getD 10 [] := by
  decide +kernel

theorem h5n21_arithmetic : BiPoly.mul h5p6 h5p20=h5p21 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p20).getD j.val []=h5p21.getD j.val [] :=
      (fun j => Fin.cases h5n21_arithmetic_row0 (fun j => Fin.cases h5n21_arithmetic_row1 (fun j => Fin.cases h5n21_arithmetic_row2 (fun j => Fin.cases h5n21_arithmetic_row3 (fun j => Fin.cases h5n21_arithmetic_row4 (fun j => Fin.cases h5n21_arithmetic_row5 (fun j => Fin.cases h5n21_arithmetic_row6 (fun j => Fin.cases h5n21_arithmetic_row7 (fun j => Fin.cases h5n21_arithmetic_row8 (fun j => Fin.cases h5n21_arithmetic_row9 (fun j => Fin.cases h5n21_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n21 : h5e21.toBi mapPolyEnv=h5p21 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e20.toBi mapPolyEnv)=h5p21
  rw [h5n6, h5n20]
  exact h5n21_arithmetic

#print axioms h5n21_arithmetic
end StackSorting.RationalLift
