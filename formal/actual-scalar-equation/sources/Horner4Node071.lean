import BivariateRowEquality
import Horner4Base
import Horner4Node010
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p71 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 472261338), (Int.ofNat 1217015676), (Int.negSucc 2450153789)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2306280713), (Int.negSucc 6703599179), (Int.ofNat 10748750526), (Int.negSucc 670962071)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5320050962), (Int.ofNat 12293004262), (Int.negSucc 16403256159), (Int.ofNat 117391062), (Int.ofNat 3405160)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 7419367906), (Int.negSucc 8377521066), (Int.ofNat 4036034801), (Int.ofNat 4035733571), (Int.negSucc 123557267)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 6517991433), (Int.ofNat 402433922), (Int.ofNat 12339545263), (Int.negSucc 5980552105), (Int.negSucc 206952321)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3504802104), (Int.ofNat 987248176), (Int.negSucc 10739512338), (Int.ofNat 583467373), (Int.ofNat 377382165)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1074940707), (Int.ofNat 858249577), (Int.ofNat 2281968902), (Int.ofNat 2850082835), (Int.ofNat 90990270)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 162483781), (Int.negSucc 936223362), (Int.ofNat 334049373), (Int.negSucc 1338212759), (Int.negSucc 249725645)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7690068), (Int.ofNat 298735941), (Int.negSucc 165027065), (Int.ofNat 144652032), (Int.ofNat 71389728)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 36794951), (Int.ofNat 23061006)]]

theorem h4n71_arithmetic_row0 :
    (BiPoly.mul h4p7 h4p10).getD 0 []=h4p71.getD 0 [] := by
  decide +kernel

theorem h4n71_arithmetic_row1 :
    (BiPoly.mul h4p7 h4p10).getD 1 []=h4p71.getD 1 [] := by
  decide +kernel

theorem h4n71_arithmetic_row2 :
    (BiPoly.mul h4p7 h4p10).getD 2 []=h4p71.getD 2 [] := by
  decide +kernel

theorem h4n71_arithmetic_row3 :
    (BiPoly.mul h4p7 h4p10).getD 3 []=h4p71.getD 3 [] := by
  decide +kernel

theorem h4n71_arithmetic_row4 :
    (BiPoly.mul h4p7 h4p10).getD 4 []=h4p71.getD 4 [] := by
  decide +kernel

theorem h4n71_arithmetic_row5 :
    (BiPoly.mul h4p7 h4p10).getD 5 []=h4p71.getD 5 [] := by
  decide +kernel

theorem h4n71_arithmetic_row6 :
    (BiPoly.mul h4p7 h4p10).getD 6 []=h4p71.getD 6 [] := by
  decide +kernel

theorem h4n71_arithmetic_row7 :
    (BiPoly.mul h4p7 h4p10).getD 7 []=h4p71.getD 7 [] := by
  decide +kernel

theorem h4n71_arithmetic_row8 :
    (BiPoly.mul h4p7 h4p10).getD 8 []=h4p71.getD 8 [] := by
  decide +kernel

theorem h4n71_arithmetic_row9 :
    (BiPoly.mul h4p7 h4p10).getD 9 []=h4p71.getD 9 [] := by
  decide +kernel

theorem h4n71_arithmetic : BiPoly.mul h4p7 h4p10=h4p71 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<10 at hk
    have hf : ∀ j : Fin 10, (BiPoly.mul h4p7 h4p10).getD j.val []=h4p71.getD j.val [] :=
      (fun j => Fin.cases h4n71_arithmetic_row0 (fun j => Fin.cases h4n71_arithmetic_row1 (fun j => Fin.cases h4n71_arithmetic_row2 (fun j => Fin.cases h4n71_arithmetic_row3 (fun j => Fin.cases h4n71_arithmetic_row4 (fun j => Fin.cases h4n71_arithmetic_row5 (fun j => Fin.cases h4n71_arithmetic_row6 (fun j => Fin.cases h4n71_arithmetic_row7 (fun j => Fin.cases h4n71_arithmetic_row8 (fun j => Fin.cases h4n71_arithmetic_row9 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n71 : h4e71.toBi mapPolyEnv=h4p71 := by
  change BiPoly.mul (h4e7.toBi mapPolyEnv) (h4e10.toBi mapPolyEnv)=h4p71
  rw [h4n7, h4n10]
  exact h4n71_arithmetic

#print axioms h4n71_arithmetic
end StackSorting.RationalLift
