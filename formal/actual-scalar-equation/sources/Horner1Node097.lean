import BivariateRowEquality
import Horner1Base
import Horner1Node096
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p97 : BiPoly.Poly := [[(Int.ofNat 1075356000), (Int.ofNat 11812437360), (Int.ofNat 21826098000), (Int.negSucc 30804935039)], [(Int.negSucc 4678993439), (Int.negSucc 50205851567), (Int.negSucc 85438613375), (Int.ofNat 132286071168), (Int.negSucc 13879047167)], [(Int.ofNat 8264708280), (Int.ofNat 88178987196), (Int.ofNat 154994419608), (Int.negSucc 171322300619), (Int.ofNat 4990832352), (Int.negSucc 1473897983)], [(Int.negSucc 7568116559), (Int.negSucc 82322065799), (Int.negSucc 173590061951), (Int.ofNat 15362950056), (Int.ofNat 82110135576), (Int.negSucc 5321359679)], [(Int.ofNat 3784987600), (Int.ofNat 43484262408), (Int.ofNat 126841027884), (Int.ofNat 156185263396), (Int.negSucc 107132682267), (Int.ofNat 4622814752)], [(Int.negSucc 981627439), (Int.negSucc 12601609351), (Int.negSucc 57489176095), (Int.negSucc 155826623407), (Int.ofNat 3564626704), (Int.ofNat 17186702464)], [(Int.ofNat 103685560), (Int.ofNat 1713048188), (Int.ofNat 14419732796), (Int.ofNat 66480637024), (Int.ofNat 59601118416), (Int.negSucc 14125578623)], [(Int.ofNat 0), (Int.negSucc 59208431), (Int.negSucc 1576798055), (Int.negSucc 13009926335), (Int.negSucc 34061535719), (Int.negSucc 4659867455)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 25319592), (Int.ofNat 897371400), (Int.ofNat 6299933664), (Int.ofNat 5931330816)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 8722511), (Int.negSucc 215566415), (Int.negSucc 1166290559)]]

theorem h1n97_arithmetic_row0 :
    (BiPoly.mul h1p6 h1p96).getD 0 []=h1p97.getD 0 [] := by
  decide +kernel

theorem h1n97_arithmetic_row1 :
    (BiPoly.mul h1p6 h1p96).getD 1 []=h1p97.getD 1 [] := by
  decide +kernel

theorem h1n97_arithmetic_row2 :
    (BiPoly.mul h1p6 h1p96).getD 2 []=h1p97.getD 2 [] := by
  decide +kernel

theorem h1n97_arithmetic_row3 :
    (BiPoly.mul h1p6 h1p96).getD 3 []=h1p97.getD 3 [] := by
  decide +kernel

theorem h1n97_arithmetic_row4 :
    (BiPoly.mul h1p6 h1p96).getD 4 []=h1p97.getD 4 [] := by
  decide +kernel

theorem h1n97_arithmetic_row5 :
    (BiPoly.mul h1p6 h1p96).getD 5 []=h1p97.getD 5 [] := by
  decide +kernel

theorem h1n97_arithmetic_row6 :
    (BiPoly.mul h1p6 h1p96).getD 6 []=h1p97.getD 6 [] := by
  decide +kernel

theorem h1n97_arithmetic_row7 :
    (BiPoly.mul h1p6 h1p96).getD 7 []=h1p97.getD 7 [] := by
  decide +kernel

theorem h1n97_arithmetic_row8 :
    (BiPoly.mul h1p6 h1p96).getD 8 []=h1p97.getD 8 [] := by
  decide +kernel

theorem h1n97_arithmetic_row9 :
    (BiPoly.mul h1p6 h1p96).getD 9 []=h1p97.getD 9 [] := by
  decide +kernel

theorem h1n97_arithmetic : BiPoly.mul h1p6 h1p96=h1p97 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<10 at hk
    have hf : ∀ j : Fin 10, (BiPoly.mul h1p6 h1p96).getD j.val []=h1p97.getD j.val [] :=
      (fun j => Fin.cases h1n97_arithmetic_row0 (fun j => Fin.cases h1n97_arithmetic_row1 (fun j => Fin.cases h1n97_arithmetic_row2 (fun j => Fin.cases h1n97_arithmetic_row3 (fun j => Fin.cases h1n97_arithmetic_row4 (fun j => Fin.cases h1n97_arithmetic_row5 (fun j => Fin.cases h1n97_arithmetic_row6 (fun j => Fin.cases h1n97_arithmetic_row7 (fun j => Fin.cases h1n97_arithmetic_row8 (fun j => Fin.cases h1n97_arithmetic_row9 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n97 : h1e97.toBi mapPolyEnv=h1p97 := by
  change BiPoly.mul (h1e6.toBi mapPolyEnv) (h1e96.toBi mapPolyEnv)=h1p97
  rw [h1n6, h1n96]
  exact h1n97_arithmetic

#print axioms h1n97_arithmetic
end StackSorting.RationalLift
