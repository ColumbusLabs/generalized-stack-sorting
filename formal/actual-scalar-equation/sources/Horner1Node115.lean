import BivariateRowEquality
import Horner1Base
import Horner1Node114
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p115 : BiPoly.Poly := [[(Int.negSucc 537677999), (Int.negSucc 5906218679), (Int.negSucc 10913048999), (Int.ofNat 15402467520)], [(Int.ofNat 2339496720), (Int.ofNat 25102925784), (Int.ofNat 42719306688), (Int.negSucc 66143035583), (Int.ofNat 6939523584)], [(Int.negSucc 4132354139), (Int.negSucc 44089493597), (Int.negSucc 77497209803), (Int.ofNat 85661150310), (Int.negSucc 2495416175), (Int.ofNat 736948992)], [(Int.ofNat 3784058280), (Int.ofNat 41161032900), (Int.ofNat 86795030976), (Int.negSucc 7681475027), (Int.negSucc 41055067787), (Int.ofNat 2660679840)], [(Int.negSucc 1892493799), (Int.negSucc 21742131203), (Int.negSucc 63420513941), (Int.negSucc 78092631697), (Int.ofNat 53566341134), (Int.negSucc 2311407375)], [(Int.ofNat 490813720), (Int.ofNat 6300804676), (Int.ofNat 28744588048), (Int.ofNat 77913311704), (Int.negSucc 1782313351), (Int.negSucc 8593351231)], [(Int.negSucc 51842779), (Int.negSucc 856524093), (Int.negSucc 7209866397), (Int.negSucc 33240318511), (Int.negSucc 29800559207), (Int.ofNat 7062789312)], [(Int.ofNat 0), (Int.ofNat 29604216), (Int.ofNat 788399028), (Int.ofNat 6504963168), (Int.ofNat 17030767860), (Int.ofNat 2329933728)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 12659795), (Int.negSucc 448685699), (Int.negSucc 3149966831), (Int.negSucc 2965665407)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4361256), (Int.ofNat 107783208), (Int.ofNat 583145280)]]

theorem h1n115_arithmetic_row0 :
    (BiPoly.mul h1p6 h1p114).getD 0 []=h1p115.getD 0 [] := by
  decide +kernel

theorem h1n115_arithmetic_row1 :
    (BiPoly.mul h1p6 h1p114).getD 1 []=h1p115.getD 1 [] := by
  decide +kernel

theorem h1n115_arithmetic_row2 :
    (BiPoly.mul h1p6 h1p114).getD 2 []=h1p115.getD 2 [] := by
  decide +kernel

theorem h1n115_arithmetic_row3 :
    (BiPoly.mul h1p6 h1p114).getD 3 []=h1p115.getD 3 [] := by
  decide +kernel

theorem h1n115_arithmetic_row4 :
    (BiPoly.mul h1p6 h1p114).getD 4 []=h1p115.getD 4 [] := by
  decide +kernel

theorem h1n115_arithmetic_row5 :
    (BiPoly.mul h1p6 h1p114).getD 5 []=h1p115.getD 5 [] := by
  decide +kernel

theorem h1n115_arithmetic_row6 :
    (BiPoly.mul h1p6 h1p114).getD 6 []=h1p115.getD 6 [] := by
  decide +kernel

theorem h1n115_arithmetic_row7 :
    (BiPoly.mul h1p6 h1p114).getD 7 []=h1p115.getD 7 [] := by
  decide +kernel

theorem h1n115_arithmetic_row8 :
    (BiPoly.mul h1p6 h1p114).getD 8 []=h1p115.getD 8 [] := by
  decide +kernel

theorem h1n115_arithmetic_row9 :
    (BiPoly.mul h1p6 h1p114).getD 9 []=h1p115.getD 9 [] := by
  decide +kernel

theorem h1n115_arithmetic : BiPoly.mul h1p6 h1p114=h1p115 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<10 at hk
    have hf : ∀ j : Fin 10, (BiPoly.mul h1p6 h1p114).getD j.val []=h1p115.getD j.val [] :=
      (fun j => Fin.cases h1n115_arithmetic_row0 (fun j => Fin.cases h1n115_arithmetic_row1 (fun j => Fin.cases h1n115_arithmetic_row2 (fun j => Fin.cases h1n115_arithmetic_row3 (fun j => Fin.cases h1n115_arithmetic_row4 (fun j => Fin.cases h1n115_arithmetic_row5 (fun j => Fin.cases h1n115_arithmetic_row6 (fun j => Fin.cases h1n115_arithmetic_row7 (fun j => Fin.cases h1n115_arithmetic_row8 (fun j => Fin.cases h1n115_arithmetic_row9 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n115 : h1e115.toBi mapPolyEnv=h1p115 := by
  change BiPoly.mul (h1e6.toBi mapPolyEnv) (h1e114.toBi mapPolyEnv)=h1p115
  rw [h1n6, h1n114]
  exact h1n115_arithmetic

#print axioms h1n115_arithmetic
end StackSorting.RationalLift
