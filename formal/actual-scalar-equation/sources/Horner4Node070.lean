import BivariateRowEquality
import Horner4Base
import Horner4Node069
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p70 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 19356408000), (Int.ofNat 57772608480), (Int.negSucc 69311103839)], [(Int.ofNat 0), (Int.negSucc 84221881919), (Int.negSucc 229930272863), (Int.ofNat 301547142144), (Int.negSucc 31227856127)], [(Int.ofNat 0), (Int.ofNat 148764749040), (Int.ofNat 397103777208), (Int.negSucc 386930664719), (Int.ofNat 11643906600), (Int.negSucc 3316270463)], [(Int.ofNat 0), (Int.negSucc 136226098079), (Int.negSucc 391988399759), (Int.ofNat 11286082944), (Int.ofNat 186244437456), (Int.negSucc 11973059279)], [(Int.ofNat 0), (Int.ofNat 68129776800), (Int.ofNat 237678508944), (Int.ofNat 381710430360), (Int.negSucc 242348701751), (Int.ofNat 10401333192)], [(Int.ofNat 0), (Int.negSucc 17669293919), (Int.negSucc 85474616975), (Int.negSucc 351008233919), (Int.ofNat 3186650016), (Int.ofNat 38670080544)], [(Int.ofNat 0), (Int.ofNat 1866340080), (Int.ofNat 15904146744), (Int.ofNat 132322016376), (Int.ofNat 138075335424), (Int.negSucc 31782551903)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1065751775), (Int.negSucc 19856350799), (Int.negSucc 75327867647), (Int.negSucc 10484701775)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 455752656), (Int.ofNat 12506663952), (Int.ofNat 13345494336)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 157005215), (Int.negSucc 2624153759)]]

theorem h4n70_arithmetic_row0 :
    (BiPoly.mul h4p68 h4p69).getD 0 []=h4p70.getD 0 [] := by
  decide +kernel

theorem h4n70_arithmetic_row1 :
    (BiPoly.mul h4p68 h4p69).getD 1 []=h4p70.getD 1 [] := by
  decide +kernel

theorem h4n70_arithmetic_row2 :
    (BiPoly.mul h4p68 h4p69).getD 2 []=h4p70.getD 2 [] := by
  decide +kernel

theorem h4n70_arithmetic_row3 :
    (BiPoly.mul h4p68 h4p69).getD 3 []=h4p70.getD 3 [] := by
  decide +kernel

theorem h4n70_arithmetic_row4 :
    (BiPoly.mul h4p68 h4p69).getD 4 []=h4p70.getD 4 [] := by
  decide +kernel

theorem h4n70_arithmetic_row5 :
    (BiPoly.mul h4p68 h4p69).getD 5 []=h4p70.getD 5 [] := by
  decide +kernel

theorem h4n70_arithmetic_row6 :
    (BiPoly.mul h4p68 h4p69).getD 6 []=h4p70.getD 6 [] := by
  decide +kernel

theorem h4n70_arithmetic_row7 :
    (BiPoly.mul h4p68 h4p69).getD 7 []=h4p70.getD 7 [] := by
  decide +kernel

theorem h4n70_arithmetic_row8 :
    (BiPoly.mul h4p68 h4p69).getD 8 []=h4p70.getD 8 [] := by
  decide +kernel

theorem h4n70_arithmetic_row9 :
    (BiPoly.mul h4p68 h4p69).getD 9 []=h4p70.getD 9 [] := by
  decide +kernel

theorem h4n70_arithmetic : BiPoly.mul h4p68 h4p69=h4p70 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<10 at hk
    have hf : ∀ j : Fin 10, (BiPoly.mul h4p68 h4p69).getD j.val []=h4p70.getD j.val [] :=
      (fun j => Fin.cases h4n70_arithmetic_row0 (fun j => Fin.cases h4n70_arithmetic_row1 (fun j => Fin.cases h4n70_arithmetic_row2 (fun j => Fin.cases h4n70_arithmetic_row3 (fun j => Fin.cases h4n70_arithmetic_row4 (fun j => Fin.cases h4n70_arithmetic_row5 (fun j => Fin.cases h4n70_arithmetic_row6 (fun j => Fin.cases h4n70_arithmetic_row7 (fun j => Fin.cases h4n70_arithmetic_row8 (fun j => Fin.cases h4n70_arithmetic_row9 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n70 : h4e70.toBi mapPolyEnv=h4p70 := by
  change BiPoly.mul (h4e68.toBi mapPolyEnv) (h4e69.toBi mapPolyEnv)=h4p70
  rw [h4n68, h4n69]
  exact h4n70_arithmetic

#print axioms h4n70_arithmetic
end StackSorting.RationalLift
