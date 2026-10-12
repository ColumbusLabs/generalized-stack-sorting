import BivariateRowEquality
import Horner1Base
import Horner1Node015
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p65 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 43551918000), (Int.ofNat 173540287080), (Int.negSucc 25961614559), (Int.negSucc 155949983639)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 335478811319), (Int.negSucc 1218356701883), (Int.ofNat 448711460460), (Int.ofNat 853207771356), (Int.negSucc 38495087027)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1148671979820), (Int.ofNat 3896698423194), (Int.negSucc 1658452859513), (Int.negSucc 1699884039185), (Int.negSucc 308425100921), (Int.ofNat 28029551688)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2300150340089), (Int.negSucc 7581983675336), (Int.ofNat 1983658180878), (Int.ofNat 1729358072766), (Int.ofNat 2016726520140), (Int.negSucc 238898249684), (Int.ofNat 11061802224)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2980388285010), (Int.ofNat 10093017261897), (Int.ofNat 1672474662966), (Int.negSucc 1552401943547), (Int.negSucc 3696135788225), (Int.ofNat 117208746717), (Int.negSucc 9949697219), (Int.ofNat 1013304864)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2608896796949), (Int.negSucc 9729059393912), (Int.negSucc 8324396098061), (Int.ofNat 1351527866880), (Int.ofNat 2394913674198), (Int.ofNat 1390414687137), (Int.negSucc 151224510503), (Int.ofNat 3888731340)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1561329058070), (Int.ofNat 6926469346223), (Int.ofNat 12250970109775), (Int.ofNat 1063915222136), (Int.ofNat 349989536820), (Int.negSucc 2586662619212), (Int.ofNat 154109386287), (Int.negSucc 7597484259)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 630492938869), (Int.negSucc 3607000529184), (Int.negSucc 10372324275010), (Int.negSucc 5137460925658), (Int.negSucc 1321879748593), (Int.ofNat 1149278959288), (Int.ofNat 449600650305), (Int.negSucc 30666448992)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 164390766990), (Int.ofNat 1326056444031), (Int.ofNat 5603745816542), (Int.ofNat 6666586993266), (Int.ofNat 1437492806992), (Int.ofNat 818010650074), (Int.negSucc 725963439941), (Int.ofNat 26487955418)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 24998011009), (Int.negSucc 322595740522), (Int.negSucc 1947102592735), (Int.negSucc 4559366071303), (Int.negSucc 1886884699495), (Int.negSucc 1013596915033), (Int.ofNat 137743209048), (Int.ofNat 64038074766)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1684890350), (Int.ofNat 46120519687), (Int.ofNat 413729865277), (Int.ofNat 1792128921770), (Int.ofNat 1696588037970), (Int.ofNat 518327054706), (Int.ofNat 281956588242), (Int.negSucc 63339579629)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2906241269), (Int.negSucc 47040842504), (Int.negSucc 390201225572), (Int.negSucc 828440736593), (Int.negSucc 312273091643), (Int.negSucc 183457810241), (Int.negSucc 8780085515)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1988186490), (Int.ofNat 39422261850), (Int.ofNat 205662748578), (Int.ofNat 177615959550), (Int.ofNat 50064376608), (Int.ofNat 23933774376)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 882921113), (Int.negSucc 21353803901), (Int.negSucc 52741608227), (Int.negSucc 15549467687), (Int.negSucc 7491283703)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 277485264), (Int.ofNat 5964829632), (Int.ofNat 5125060728), (Int.ofNat 656038440)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 39251303), (Int.negSucc 656038439)]]

theorem h1n65_arithmetic_row0 :
    (BiPoly.mul h1p5 h1p15).getD 0 []=h1p65.getD 0 [] := by
  decide +kernel

theorem h1n65_arithmetic_row1 :
    (BiPoly.mul h1p5 h1p15).getD 1 []=h1p65.getD 1 [] := by
  decide +kernel

theorem h1n65_arithmetic_row2 :
    (BiPoly.mul h1p5 h1p15).getD 2 []=h1p65.getD 2 [] := by
  decide +kernel

theorem h1n65_arithmetic_row3 :
    (BiPoly.mul h1p5 h1p15).getD 3 []=h1p65.getD 3 [] := by
  decide +kernel

theorem h1n65_arithmetic_row4 :
    (BiPoly.mul h1p5 h1p15).getD 4 []=h1p65.getD 4 [] := by
  decide +kernel

theorem h1n65_arithmetic_row5 :
    (BiPoly.mul h1p5 h1p15).getD 5 []=h1p65.getD 5 [] := by
  decide +kernel

theorem h1n65_arithmetic_row6 :
    (BiPoly.mul h1p5 h1p15).getD 6 []=h1p65.getD 6 [] := by
  decide +kernel

theorem h1n65_arithmetic_row7 :
    (BiPoly.mul h1p5 h1p15).getD 7 []=h1p65.getD 7 [] := by
  decide +kernel

theorem h1n65_arithmetic_row8 :
    (BiPoly.mul h1p5 h1p15).getD 8 []=h1p65.getD 8 [] := by
  decide +kernel

theorem h1n65_arithmetic_row9 :
    (BiPoly.mul h1p5 h1p15).getD 9 []=h1p65.getD 9 [] := by
  decide +kernel

theorem h1n65_arithmetic_row10 :
    (BiPoly.mul h1p5 h1p15).getD 10 []=h1p65.getD 10 [] := by
  decide +kernel

theorem h1n65_arithmetic_row11 :
    (BiPoly.mul h1p5 h1p15).getD 11 []=h1p65.getD 11 [] := by
  decide +kernel

theorem h1n65_arithmetic_row12 :
    (BiPoly.mul h1p5 h1p15).getD 12 []=h1p65.getD 12 [] := by
  decide +kernel

theorem h1n65_arithmetic_row13 :
    (BiPoly.mul h1p5 h1p15).getD 13 []=h1p65.getD 13 [] := by
  decide +kernel

theorem h1n65_arithmetic_row14 :
    (BiPoly.mul h1p5 h1p15).getD 14 []=h1p65.getD 14 [] := by
  decide +kernel

theorem h1n65_arithmetic_row15 :
    (BiPoly.mul h1p5 h1p15).getD 15 []=h1p65.getD 15 [] := by
  decide +kernel

theorem h1n65_arithmetic : BiPoly.mul h1p5 h1p15=h1p65 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<16 at hk
    have hf : ∀ j : Fin 16, (BiPoly.mul h1p5 h1p15).getD j.val []=h1p65.getD j.val [] :=
      (fun j => Fin.cases h1n65_arithmetic_row0 (fun j => Fin.cases h1n65_arithmetic_row1 (fun j => Fin.cases h1n65_arithmetic_row2 (fun j => Fin.cases h1n65_arithmetic_row3 (fun j => Fin.cases h1n65_arithmetic_row4 (fun j => Fin.cases h1n65_arithmetic_row5 (fun j => Fin.cases h1n65_arithmetic_row6 (fun j => Fin.cases h1n65_arithmetic_row7 (fun j => Fin.cases h1n65_arithmetic_row8 (fun j => Fin.cases h1n65_arithmetic_row9 (fun j => Fin.cases h1n65_arithmetic_row10 (fun j => Fin.cases h1n65_arithmetic_row11 (fun j => Fin.cases h1n65_arithmetic_row12 (fun j => Fin.cases h1n65_arithmetic_row13 (fun j => Fin.cases h1n65_arithmetic_row14 (fun j => Fin.cases h1n65_arithmetic_row15 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n65 : h1e65.toBi mapPolyEnv=h1p65 := by
  change BiPoly.mul (h1e5.toBi mapPolyEnv) (h1e15.toBi mapPolyEnv)=h1p65
  rw [h1n5, h1n15]
  exact h1n65_arithmetic

#print axioms h1n65_arithmetic
end StackSorting.RationalLift
