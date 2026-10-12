import BivariateRowEquality
import Horner5Base
import Horner5Node131
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p132 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 9678204000), (Int.ofNat 38564508240), (Int.negSucc 5769247679), (Int.negSucc 34655551919)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 51789144959), (Int.negSucc 185962381631), (Int.ofNat 70463986560), (Int.ofNat 135159643008), (Int.negSucc 15613928063)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 116493315480), (Int.ofNat 387899399556), (Int.negSucc 145687014827), (Int.negSucc 172029450995), (Int.ofNat 4163818068), (Int.negSucc 1658135231)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 142495423559), (Int.negSucc 462659137523), (Int.ofNat 3114173952), (Int.ofNat 92943306900), (Int.ofNat 88793824320), (Int.negSucc 5986529639)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 102177937440), (Int.ofNat 348898342752), (Int.ofNat 304051428180), (Int.negSucc 23441354423), (Int.negSucc 109987154639), (Int.ofNat 5200666596)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 42899535359), (Int.negSucc 170411209919), (Int.negSucc 409096640627), (Int.negSucc 52736441075), (Int.ofNat 15727698684), (Int.ofNat 19335040272)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 9767817000), (Int.ofNat 51622551900), (Int.ofNat 249617198520), (Int.ofNat 133605350892), (Int.ofNat 33811351488), (Int.negSucc 15891275951)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 933170039), (Int.negSucc 8484949259), (Int.negSucc 76622059475), (Int.negSucc 116629776935), (Int.negSucc 27015008759), (Int.negSucc 5242350887)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 532875888), (Int.ofNat 10156051728), (Int.ofNat 44145142128), (Int.ofNat 18168430032), (Int.ofNat 6672747168)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 227876327), (Int.negSucc 6331834583), (Int.negSucc 8063326655), (Int.negSucc 1312076879)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 78502608), (Int.ofNat 1312076880)]]

theorem h5n132_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p131).getD 0 []=h5p132.getD 0 [] := by
  decide +kernel

theorem h5n132_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p131).getD 1 []=h5p132.getD 1 [] := by
  decide +kernel

theorem h5n132_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p131).getD 2 []=h5p132.getD 2 [] := by
  decide +kernel

theorem h5n132_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p131).getD 3 []=h5p132.getD 3 [] := by
  decide +kernel

theorem h5n132_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p131).getD 4 []=h5p132.getD 4 [] := by
  decide +kernel

theorem h5n132_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p131).getD 5 []=h5p132.getD 5 [] := by
  decide +kernel

theorem h5n132_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p131).getD 6 []=h5p132.getD 6 [] := by
  decide +kernel

theorem h5n132_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p131).getD 7 []=h5p132.getD 7 [] := by
  decide +kernel

theorem h5n132_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p131).getD 8 []=h5p132.getD 8 [] := by
  decide +kernel

theorem h5n132_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p131).getD 9 []=h5p132.getD 9 [] := by
  decide +kernel

theorem h5n132_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p131).getD 10 []=h5p132.getD 10 [] := by
  decide +kernel

theorem h5n132_arithmetic : BiPoly.mul h5p6 h5p131=h5p132 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p131).getD j.val []=h5p132.getD j.val [] :=
      (fun j => Fin.cases h5n132_arithmetic_row0 (fun j => Fin.cases h5n132_arithmetic_row1 (fun j => Fin.cases h5n132_arithmetic_row2 (fun j => Fin.cases h5n132_arithmetic_row3 (fun j => Fin.cases h5n132_arithmetic_row4 (fun j => Fin.cases h5n132_arithmetic_row5 (fun j => Fin.cases h5n132_arithmetic_row6 (fun j => Fin.cases h5n132_arithmetic_row7 (fun j => Fin.cases h5n132_arithmetic_row8 (fun j => Fin.cases h5n132_arithmetic_row9 (fun j => Fin.cases h5n132_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n132 : h5e132.toBi mapPolyEnv=h5p132 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e131.toBi mapPolyEnv)=h5p132
  rw [h5n6, h5n131]
  exact h5n132_arithmetic

#print axioms h5n132_arithmetic
end StackSorting.RationalLift
