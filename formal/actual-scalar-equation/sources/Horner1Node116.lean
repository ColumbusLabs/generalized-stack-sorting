import BivariateRowEquality
import Horner1Base
import Horner1Node115
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p116 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 87103836000), (Int.ofNat 1043911262160), (Int.ofNat 2724721364160), (Int.negSucc 727285800239), (Int.negSucc 2495199738239)], [(Int.ofNat 0), (Int.negSucc 670957622639), (Int.negSucc 7804374384887), (Int.negSucc 18596284309223), (Int.ofNat 8885798910072), (Int.ofNat 13574334167640), (Int.negSucc 615921392447)], [(Int.ofNat 0), (Int.ofNat 2297343959640), (Int.ofNat 26172148523508), (Int.ofNat 59030269052076), (Int.negSucc 29935013830595), (Int.negSucc 27814994828819), (Int.negSucc 4878742511375), (Int.ofNat 448472827008)], [(Int.ofNat 0), (Int.negSucc 4600300680179), (Int.negSucc 51966372792113), (Int.negSucc 117344422443635), (Int.ofNat 35197247039580), (Int.ofNat 31703182204536), (Int.ofNat 31789827822870), (Int.negSucc 3800248390511), (Int.ofNat 176988835584)], [(Int.ofNat 0), (Int.ofNat 5960776570020), (Int.ofNat 67872247083954), (Int.ofNat 164833225516284), (Int.ofNat 23654790720360), (Int.negSucc 32230702673219), (Int.negSucc 58903755118181), (Int.ofNat 1855440553032), (Int.negSucc 157168545791), (Int.ofNat 16212877824)], [(Int.ofNat 0), (Int.negSucc 5217793593899), (Int.negSucc 61200467539025), (Int.negSucc 172313742498731), (Int.negSucc 130487281835231), (Int.ofNat 26414273218476), (Int.ofNat 41099448161442), (Int.ofNat 21944185973184), (Int.negSucc 2411814705383), (Int.ofNat 62219701440)], [(Int.ofNat 0), (Int.ofNat 3122658116140), (Int.ofNat 38834203621566), (Int.ofNat 135325449759118), (Int.ofNat 198143352200672), (Int.ofNat 17722622627816), (Int.ofNat 426507350694), (Int.negSucc 41078383134833), (Int.ofNat 2450555212072), (Int.negSucc 121559748159)], [(Int.ofNat 0), (Int.negSucc 1260985877739), (Int.negSucc 17301888080289), (Int.negSucc 78456657016981), (Int.negSucc 176232110251493), (Int.negSucc 84843134307731), (Int.negSucc 18851518058927), (Int.ofNat 19287664649218), (Int.ofNat 7132277506894), (Int.negSucc 490663183887)], [(Int.ofNat 0), (Int.ofNat 328781533980), (Int.ofNat 5282365159902), (Int.ofNat 32424394737580), (Int.ofNat 102993107051204), (Int.ofNat 109540377506240), (Int.ofNat 24635906212020), (Int.ofNat 11636243521300), (Int.negSucc 11562439128235), (Int.ofNat 423807286688)], [(Int.ofNat 0), (Int.negSucc 49996022019), (Int.negSucc 1045159657205), (Int.negSucc 9055737033839), (Int.negSucc 40272373626383), (Int.negSucc 76723626539855), (Int.negSucc 32217349022003), (Int.negSucc 15942064222447), (Int.ofNat 2331967494300), (Int.ofNat 1024609196256)], [(Int.ofNat 0), (Int.ofNat 3369780700), (Int.ofNat 119199284974), (Int.ofNat 1565388045546), (Int.ofNat 10203935687972), (Int.ofNat 32067238824260), (Int.ofNat 28182062716932), (Int.ofNat 8857146051780), (Int.ofNat 4384626252612), (Int.negSucc 1013433274079)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 5812482539), (Int.negSucc 140581545329), (Int.negSucc 1533055931225), (Int.negSucc 7900101082355), (Int.negSucc 13879597968791), (Int.negSucc 5363285086787), (Int.negSucc 2952885134903), (Int.negSucc 140481368255)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3976372980), (Int.ofNat 110655507540), (Int.ofNat 1042081686756), (Int.ofNat 3645835896348), (Int.ofNat 2941984106016), (Int.ofNat 848897574480), (Int.ofNat 382940390016)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1765842227), (Int.negSucc 56834345627), (Int.negSucc 447144078887), (Int.negSucc 874964667023), (Int.negSucc 263774050415), (Int.negSucc 119860539263)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 554970528), (Int.ofNat 16369423488), (Int.ofNat 105687395568), (Int.ofNat 83313048528), (Int.ofNat 10496615040)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 78502607), (Int.negSucc 1940097743), (Int.negSucc 10496615039)]]

theorem h1n116_arithmetic_row0 :
    (BiPoly.mul h1p5 h1p115).getD 0 []=h1p116.getD 0 [] := by
  decide +kernel

theorem h1n116_arithmetic_row1 :
    (BiPoly.mul h1p5 h1p115).getD 1 []=h1p116.getD 1 [] := by
  decide +kernel

theorem h1n116_arithmetic_row2 :
    (BiPoly.mul h1p5 h1p115).getD 2 []=h1p116.getD 2 [] := by
  decide +kernel

theorem h1n116_arithmetic_row3 :
    (BiPoly.mul h1p5 h1p115).getD 3 []=h1p116.getD 3 [] := by
  decide +kernel

theorem h1n116_arithmetic_row4 :
    (BiPoly.mul h1p5 h1p115).getD 4 []=h1p116.getD 4 [] := by
  decide +kernel

theorem h1n116_arithmetic_row5 :
    (BiPoly.mul h1p5 h1p115).getD 5 []=h1p116.getD 5 [] := by
  decide +kernel

theorem h1n116_arithmetic_row6 :
    (BiPoly.mul h1p5 h1p115).getD 6 []=h1p116.getD 6 [] := by
  decide +kernel

theorem h1n116_arithmetic_row7 :
    (BiPoly.mul h1p5 h1p115).getD 7 []=h1p116.getD 7 [] := by
  decide +kernel

theorem h1n116_arithmetic_row8 :
    (BiPoly.mul h1p5 h1p115).getD 8 []=h1p116.getD 8 [] := by
  decide +kernel

theorem h1n116_arithmetic_row9 :
    (BiPoly.mul h1p5 h1p115).getD 9 []=h1p116.getD 9 [] := by
  decide +kernel

theorem h1n116_arithmetic_row10 :
    (BiPoly.mul h1p5 h1p115).getD 10 []=h1p116.getD 10 [] := by
  decide +kernel

theorem h1n116_arithmetic_row11 :
    (BiPoly.mul h1p5 h1p115).getD 11 []=h1p116.getD 11 [] := by
  decide +kernel

theorem h1n116_arithmetic_row12 :
    (BiPoly.mul h1p5 h1p115).getD 12 []=h1p116.getD 12 [] := by
  decide +kernel

theorem h1n116_arithmetic_row13 :
    (BiPoly.mul h1p5 h1p115).getD 13 []=h1p116.getD 13 [] := by
  decide +kernel

theorem h1n116_arithmetic_row14 :
    (BiPoly.mul h1p5 h1p115).getD 14 []=h1p116.getD 14 [] := by
  decide +kernel

theorem h1n116_arithmetic_row15 :
    (BiPoly.mul h1p5 h1p115).getD 15 []=h1p116.getD 15 [] := by
  decide +kernel

theorem h1n116_arithmetic : BiPoly.mul h1p5 h1p115=h1p116 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<16 at hk
    have hf : ∀ j : Fin 16, (BiPoly.mul h1p5 h1p115).getD j.val []=h1p116.getD j.val [] :=
      (fun j => Fin.cases h1n116_arithmetic_row0 (fun j => Fin.cases h1n116_arithmetic_row1 (fun j => Fin.cases h1n116_arithmetic_row2 (fun j => Fin.cases h1n116_arithmetic_row3 (fun j => Fin.cases h1n116_arithmetic_row4 (fun j => Fin.cases h1n116_arithmetic_row5 (fun j => Fin.cases h1n116_arithmetic_row6 (fun j => Fin.cases h1n116_arithmetic_row7 (fun j => Fin.cases h1n116_arithmetic_row8 (fun j => Fin.cases h1n116_arithmetic_row9 (fun j => Fin.cases h1n116_arithmetic_row10 (fun j => Fin.cases h1n116_arithmetic_row11 (fun j => Fin.cases h1n116_arithmetic_row12 (fun j => Fin.cases h1n116_arithmetic_row13 (fun j => Fin.cases h1n116_arithmetic_row14 (fun j => Fin.cases h1n116_arithmetic_row15 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n116 : h1e116.toBi mapPolyEnv=h1p116 := by
  change BiPoly.mul (h1e5.toBi mapPolyEnv) (h1e115.toBi mapPolyEnv)=h1p116
  rw [h1n5, h1n115]
  exact h1n116_arithmetic

#print axioms h1n116_arithmetic
end StackSorting.RationalLift
