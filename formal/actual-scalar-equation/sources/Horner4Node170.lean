import BivariateRowEquality
import Horner4Base
import Horner4Node069
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p170 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 19356407999), (Int.negSucc 57772608479), (Int.ofNat 69311103840)], [(Int.ofNat 0), (Int.ofNat 84221881920), (Int.ofNat 229930272864), (Int.negSucc 301547142143), (Int.ofNat 31227856128)], [(Int.ofNat 0), (Int.negSucc 148764749039), (Int.negSucc 397103777207), (Int.ofNat 386930664720), (Int.negSucc 11643906599), (Int.ofNat 3316270464)], [(Int.ofNat 0), (Int.ofNat 136226098080), (Int.ofNat 391988399760), (Int.negSucc 11286082943), (Int.negSucc 186244437455), (Int.ofNat 11973059280)], [(Int.ofNat 0), (Int.negSucc 68129776799), (Int.negSucc 237678508943), (Int.negSucc 381710430359), (Int.ofNat 242348701752), (Int.negSucc 10401333191)], [(Int.ofNat 0), (Int.ofNat 17669293920), (Int.ofNat 85474616976), (Int.ofNat 351008233920), (Int.negSucc 3186650015), (Int.negSucc 38670080543)], [(Int.ofNat 0), (Int.negSucc 1866340079), (Int.negSucc 15904146743), (Int.negSucc 132322016375), (Int.negSucc 138075335423), (Int.ofNat 31782551904)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1065751776), (Int.ofNat 19856350800), (Int.ofNat 75327867648), (Int.ofNat 10484701776)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 455752655), (Int.negSucc 12506663951), (Int.negSucc 13345494335)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 157005216), (Int.ofNat 2624153760)]]

theorem h4n170_arithmetic_row0 :
    (BiPoly.mul h4p6 h4p69).getD 0 []=h4p170.getD 0 [] := by
  decide +kernel

theorem h4n170_arithmetic_row1 :
    (BiPoly.mul h4p6 h4p69).getD 1 []=h4p170.getD 1 [] := by
  decide +kernel

theorem h4n170_arithmetic_row2 :
    (BiPoly.mul h4p6 h4p69).getD 2 []=h4p170.getD 2 [] := by
  decide +kernel

theorem h4n170_arithmetic_row3 :
    (BiPoly.mul h4p6 h4p69).getD 3 []=h4p170.getD 3 [] := by
  decide +kernel

theorem h4n170_arithmetic_row4 :
    (BiPoly.mul h4p6 h4p69).getD 4 []=h4p170.getD 4 [] := by
  decide +kernel

theorem h4n170_arithmetic_row5 :
    (BiPoly.mul h4p6 h4p69).getD 5 []=h4p170.getD 5 [] := by
  decide +kernel

theorem h4n170_arithmetic_row6 :
    (BiPoly.mul h4p6 h4p69).getD 6 []=h4p170.getD 6 [] := by
  decide +kernel

theorem h4n170_arithmetic_row7 :
    (BiPoly.mul h4p6 h4p69).getD 7 []=h4p170.getD 7 [] := by
  decide +kernel

theorem h4n170_arithmetic_row8 :
    (BiPoly.mul h4p6 h4p69).getD 8 []=h4p170.getD 8 [] := by
  decide +kernel

theorem h4n170_arithmetic_row9 :
    (BiPoly.mul h4p6 h4p69).getD 9 []=h4p170.getD 9 [] := by
  decide +kernel

theorem h4n170_arithmetic : BiPoly.mul h4p6 h4p69=h4p170 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<10 at hk
    have hf : ∀ j : Fin 10, (BiPoly.mul h4p6 h4p69).getD j.val []=h4p170.getD j.val [] :=
      (fun j => Fin.cases h4n170_arithmetic_row0 (fun j => Fin.cases h4n170_arithmetic_row1 (fun j => Fin.cases h4n170_arithmetic_row2 (fun j => Fin.cases h4n170_arithmetic_row3 (fun j => Fin.cases h4n170_arithmetic_row4 (fun j => Fin.cases h4n170_arithmetic_row5 (fun j => Fin.cases h4n170_arithmetic_row6 (fun j => Fin.cases h4n170_arithmetic_row7 (fun j => Fin.cases h4n170_arithmetic_row8 (fun j => Fin.cases h4n170_arithmetic_row9 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n170 : h4e170.toBi mapPolyEnv=h4p170 := by
  change BiPoly.mul (h4e6.toBi mapPolyEnv) (h4e69.toBi mapPolyEnv)=h4p170
  rw [h4n6, h4n69]
  exact h4n170_arithmetic

#print axioms h4n170_arithmetic
end StackSorting.RationalLift
