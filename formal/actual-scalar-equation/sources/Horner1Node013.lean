import BivariateRowEquality
import Horner1Base
import Horner1Node012
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p13 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 1045246032000), (Int.ofNat 8345951017920), (Int.ofNat 16036788810240), (Int.negSucc 6235114605119), (Int.negSucc 14971198429439)], [(Int.ofNat 0), (Int.negSucc 8051491471679), (Int.negSucc 61446526731935), (Int.negSucc 106193168329823), (Int.ofNat 63553286716704), (Int.ofNat 80984063961504), (Int.negSucc 3695528354687)], [(Int.ofNat 0), (Int.ofNat 27568127515680), (Int.ofNat 203793272219376), (Int.ofNat 334280179998288), (Int.negSucc 200008691453807), (Int.negSucc 170591070183983), (Int.negSucc 28936100447999), (Int.ofNat 2690836962048)], [(Int.ofNat 0), (Int.negSucc 55203608162159), (Int.negSucc 402782040856727), (Int.negSucc 680262636491279), (Int.ofNat 231935779110672), (Int.ofNat 214419811468896), (Int.ofNat 187872187941000), (Int.negSucc 22668748716383), (Int.ofNat 1061933013504)], [(Int.ofNat 0), (Int.ofNat 71529318840240), (Int.ofNat 528349689646488), (Int.ofNat 1009069049053296), (Int.ofNat 123299920999584), (Int.negSucc 237737845498031), (Int.negSucc 352016025748487), (Int.ofNat 11013246951552), (Int.negSucc 930851616383), (Int.ofNat 97277266944)], [(Int.ofNat 0), (Int.negSucc 62613523126799), (Int.negSucc 483951517961111), (Int.negSucc 1133775208169135), (Int.negSucc 766705356608831), (Int.ofNat 187224603401232), (Int.ofNat 263281665214296), (Int.ofNat 129850421713056), (Int.negSucc 14424223456223), (Int.ofNat 373318208640)], [(Int.ofNat 0), (Int.ofNat 37471897393680), (Int.ofNat 316122853884072), (Int.ofNat 958964339872008), (Int.ofNat 1201627095869664), (Int.ofNat 110535610208736), (Int.negSucc 28480907326391), (Int.negSucc 244620986173559), (Int.ofNat 14612161461312), (Int.negSucc 729358488959)], [(Int.ofNat 0), (Int.negSucc 15131830532879), (Int.negSucc 147095334831959), (Int.negSucc 595207833402023), (Int.negSucc 1119042192616871), (Int.negSucc 524921362829519), (Int.negSucc 99317760842111), (Int.ofNat 121121195698968), (Int.ofNat 42425667653448), (Int.negSucc 2943979103327)], [(Int.ofNat 0), (Int.ofNat 3945378407760), (Int.ofNat 47606868287784), (Int.ofNat 261791318223984), (Int.ofNat 697957686226416), (Int.ofNat 674492178721344), (Int.ofNat 157631565073008), (Int.ofNat 61105899848496), (Int.negSucc 69056779304399), (Int.ofNat 2542843720128)], [(Int.ofNat 0), (Int.negSucc 599952264239), (Int.negSucc 10142106829511), (Int.negSucc 77699653315871), (Int.negSucc 296346634613951), (Int.negSucc 482984375633087), (Int.negSucc 205467257112431), (Int.negSucc 93999466826111), (Int.ofNat 14760261862992), (Int.ofNat 6147655177536)], [(Int.ofNat 0), (Int.ofNat 40437368400), (Int.ofNat 1268641946088), (Int.ofNat 14357086656600), (Int.ofNat 82729161189072), (Int.ofNat 212762489401200), (Int.ofNat 175312300958064), (Int.ofNat 56526355369584), (Int.ofNat 25547682560112), (Int.negSucc 6080599644479)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 69749790479), (Int.negSucc 1407979382039), (Int.negSucc 13880750294231), (Int.negSucc 57341895333263), (Int.negSucc 87024864912479), (Int.negSucc 34381204243631), (Int.negSucc 17822671835615), (Int.negSucc 842888209535)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 47716475760), (Int.ofNat 1137000187440), (Int.ofNat 8720443103472), (Int.ofNat 24006406892688), (Int.ofNat 18252677155392), (Int.ofNat 5380590739392), (Int.ofNat 2297642340096)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 21190106735), (Int.negSucc 597251720591), (Int.negSucc 3315763772063), (Int.negSucc 5436381614399), (Int.negSucc 1672539706943), (Int.negSucc 719163235583)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 6659646336), (Int.ofNat 169794496512), (Int.ofNat 695625102144), (Int.ofNat 507750752448), (Int.ofNat 62979690240)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 942031295), (Int.negSucc 19513047743), (Int.negSucc 62979690239)]]

theorem h1n13_arithmetic_row0 :
    (BiPoly.mul h1p5 h1p12).getD 0 []=h1p13.getD 0 [] := by
  decide +kernel

theorem h1n13_arithmetic_row1 :
    (BiPoly.mul h1p5 h1p12).getD 1 []=h1p13.getD 1 [] := by
  decide +kernel

theorem h1n13_arithmetic_row2 :
    (BiPoly.mul h1p5 h1p12).getD 2 []=h1p13.getD 2 [] := by
  decide +kernel

theorem h1n13_arithmetic_row3 :
    (BiPoly.mul h1p5 h1p12).getD 3 []=h1p13.getD 3 [] := by
  decide +kernel

theorem h1n13_arithmetic_row4 :
    (BiPoly.mul h1p5 h1p12).getD 4 []=h1p13.getD 4 [] := by
  decide +kernel

theorem h1n13_arithmetic_row5 :
    (BiPoly.mul h1p5 h1p12).getD 5 []=h1p13.getD 5 [] := by
  decide +kernel

theorem h1n13_arithmetic_row6 :
    (BiPoly.mul h1p5 h1p12).getD 6 []=h1p13.getD 6 [] := by
  decide +kernel

theorem h1n13_arithmetic_row7 :
    (BiPoly.mul h1p5 h1p12).getD 7 []=h1p13.getD 7 [] := by
  decide +kernel

theorem h1n13_arithmetic_row8 :
    (BiPoly.mul h1p5 h1p12).getD 8 []=h1p13.getD 8 [] := by
  decide +kernel

theorem h1n13_arithmetic_row9 :
    (BiPoly.mul h1p5 h1p12).getD 9 []=h1p13.getD 9 [] := by
  decide +kernel

theorem h1n13_arithmetic_row10 :
    (BiPoly.mul h1p5 h1p12).getD 10 []=h1p13.getD 10 [] := by
  decide +kernel

theorem h1n13_arithmetic_row11 :
    (BiPoly.mul h1p5 h1p12).getD 11 []=h1p13.getD 11 [] := by
  decide +kernel

theorem h1n13_arithmetic_row12 :
    (BiPoly.mul h1p5 h1p12).getD 12 []=h1p13.getD 12 [] := by
  decide +kernel

theorem h1n13_arithmetic_row13 :
    (BiPoly.mul h1p5 h1p12).getD 13 []=h1p13.getD 13 [] := by
  decide +kernel

theorem h1n13_arithmetic_row14 :
    (BiPoly.mul h1p5 h1p12).getD 14 []=h1p13.getD 14 [] := by
  decide +kernel

theorem h1n13_arithmetic_row15 :
    (BiPoly.mul h1p5 h1p12).getD 15 []=h1p13.getD 15 [] := by
  decide +kernel

theorem h1n13_arithmetic : BiPoly.mul h1p5 h1p12=h1p13 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<16 at hk
    have hf : ∀ j : Fin 16, (BiPoly.mul h1p5 h1p12).getD j.val []=h1p13.getD j.val [] :=
      (fun j => Fin.cases h1n13_arithmetic_row0 (fun j => Fin.cases h1n13_arithmetic_row1 (fun j => Fin.cases h1n13_arithmetic_row2 (fun j => Fin.cases h1n13_arithmetic_row3 (fun j => Fin.cases h1n13_arithmetic_row4 (fun j => Fin.cases h1n13_arithmetic_row5 (fun j => Fin.cases h1n13_arithmetic_row6 (fun j => Fin.cases h1n13_arithmetic_row7 (fun j => Fin.cases h1n13_arithmetic_row8 (fun j => Fin.cases h1n13_arithmetic_row9 (fun j => Fin.cases h1n13_arithmetic_row10 (fun j => Fin.cases h1n13_arithmetic_row11 (fun j => Fin.cases h1n13_arithmetic_row12 (fun j => Fin.cases h1n13_arithmetic_row13 (fun j => Fin.cases h1n13_arithmetic_row14 (fun j => Fin.cases h1n13_arithmetic_row15 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n13 : h1e13.toBi mapPolyEnv=h1p13 := by
  change BiPoly.mul (h1e5.toBi mapPolyEnv) (h1e12.toBi mapPolyEnv)=h1p13
  rw [h1n5, h1n12]
  exact h1n13_arithmetic

#print axioms h1n13_arithmetic
end StackSorting.RationalLift
