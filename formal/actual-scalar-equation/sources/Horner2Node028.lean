import BivariateRowEquality
import Horner2Base
import Horner2Node016
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p28 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 3264270368255), (Int.negSucc 13512434802911), (Int.ofNat 24805434191328), (Int.ofNat 80613990451296), (Int.negSucc 109022043039839)], [(Int.ofNat 0), (Int.ofNat 26515888175664), (Int.ofNat 100330676342496), (Int.negSucc 216499968774431), (Int.negSucc 571847908675103), (Int.ofNat 823939561085616), (Int.negSucc 65137342931711)], [(Int.ofNat 0), (Int.negSucc 100757452327199), (Int.negSucc 315286037152991), (Int.ofNat 891511681515264), (Int.ofNat 1641304010547360), (Int.negSucc 2433388953883391), (Int.ofNat 151165313986464), (Int.negSucc 10921626420479)], [(Int.ofNat 0), (Int.ofNat 236704703346864), (Int.ofNat 513467228925360), (Int.negSucc 2147805145518911), (Int.negSucc 2322994793401727), (Int.ofNat 3133471771785168), (Int.ofNat 592201135896624), (Int.negSucc 52248903554879), (Int.negSucc 337439849471)], [(Int.ofNat 0), (Int.negSucc 380609017994231), (Int.negSucc 372450007868615), (Int.ofNat 3194402757953616), (Int.ofNat 1650559337636688), (Int.negSucc 472558133916215), (Int.negSucc 2820538856197799), (Int.ofNat 227648565701568), (Int.negSucc 9112518721151), (Int.ofNat 1961372160)], [(Int.ofNat 0), (Int.ofNat 436702899525408), (Int.negSucc 140096075903207), (Int.negSucc 2933764911202031), (Int.negSucc 968249270169935), (Int.negSucc 3241523779577423), (Int.ofNat 3991575034147032), (Int.ofNat 89228246074704), (Int.negSucc 13929773785919), (Int.negSucc 32922229247)], [(Int.ofNat 0), (Int.negSucc 361924434010295), (Int.ofNat 581657853053520), (Int.ofNat 1601914495191408), (Int.ofNat 1751634782399376), (Int.ofNat 3363336875918808), (Int.negSucc 1158821605723679), (Int.negSucc 1230592166674127), (Int.ofNat 73032797332800), (Int.negSucc 1459926839807)], [(Int.ofNat 0), (Int.ofNat 215351591040576), (Int.negSucc 600120681718679), (Int.negSucc 527918245798679), (Int.negSucc 2567689319041199), (Int.negSucc 1104559614347327), (Int.negSucc 2499038352326807), (Int.ofNat 1605719388070440), (Int.ofNat 20946844314288), (Int.negSucc 3903433773695)], [(Int.ofNat 0), (Int.negSucc 90060905052935), (Int.ofNat 340949912101056), (Int.ofNat 248763883755240), (Int.ofNat 1899976292102232), (Int.ofNat 376563784024368), (Int.ofNat 2523343735046520), (Int.negSucc 235021569188615), (Int.negSucc 235687246608311), (Int.ofNat 4632862360032)], [(Int.ofNat 0), (Int.ofNat 25435943294256), (Int.negSucc 114050795413463), (Int.negSucc 264297798386423), (Int.negSucc 694809627940655), (Int.negSucc 815210342562239), (Int.negSucc 682494059028095), (Int.negSucc 901104852182039), (Int.ofNat 190565789525280), (Int.ofNat 11459295975744)], [(Int.ofNat 0), (Int.negSucc 4516157131271), (Int.ofNat 20038728390480), (Int.ofNat 191770223771520), (Int.ofNat 108160834534560), (Int.ofNat 678794061569328), (Int.negSucc 24745882261679), (Int.ofNat 628813510474464), (Int.ofNat 50838693558912), (Int.negSucc 11287694196863)], [(Int.ofNat 0), (Int.ofNat 437268363408), (Int.negSucc 576833292503), (Int.negSucc 79788101838407), (Int.negSucc 18976601236463), (Int.negSucc 223289264453903), (Int.negSucc 55151093152223), (Int.negSucc 111051663209855), (Int.negSucc 110405525510015), (Int.negSucc 5008825703807)], [(Int.ofNat 0), (Int.negSucc 16056861983), (Int.negSucc 403444699991), (Int.ofNat 19336065860664), (Int.ofNat 19693646873064), (Int.ofNat 18902174730336), (Int.ofNat 63375646868640), (Int.negSucc 12771041108255), (Int.ofNat 37258305456672), (Int.ofNat 7459780344192)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 51912039456), (Int.negSucc 2579485349015), (Int.negSucc 9052107545663), (Int.ofNat 5967083430432), (Int.negSucc 17359817745599), (Int.ofNat 3893928212448), (Int.negSucc 2916690882047), (Int.negSucc 1850421749759)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 149114628864), (Int.ofNat 1817956965312), (Int.negSucc 1529069863967), (Int.ofNat 1785115830240), (Int.negSucc 320178013055)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 143058773375), (Int.ofNat 89661191328)]]

theorem h2n28_arithmetic_row0 :
    (BiPoly.mul h2p27 h2p16).getD 0 []=h2p28.getD 0 [] := by
  decide +kernel

theorem h2n28_arithmetic_row1 :
    (BiPoly.mul h2p27 h2p16).getD 1 []=h2p28.getD 1 [] := by
  decide +kernel

theorem h2n28_arithmetic_row2 :
    (BiPoly.mul h2p27 h2p16).getD 2 []=h2p28.getD 2 [] := by
  decide +kernel

theorem h2n28_arithmetic_row3 :
    (BiPoly.mul h2p27 h2p16).getD 3 []=h2p28.getD 3 [] := by
  decide +kernel

theorem h2n28_arithmetic_row4 :
    (BiPoly.mul h2p27 h2p16).getD 4 []=h2p28.getD 4 [] := by
  decide +kernel

theorem h2n28_arithmetic_row5 :
    (BiPoly.mul h2p27 h2p16).getD 5 []=h2p28.getD 5 [] := by
  decide +kernel

theorem h2n28_arithmetic_row6 :
    (BiPoly.mul h2p27 h2p16).getD 6 []=h2p28.getD 6 [] := by
  decide +kernel

theorem h2n28_arithmetic_row7 :
    (BiPoly.mul h2p27 h2p16).getD 7 []=h2p28.getD 7 [] := by
  decide +kernel

theorem h2n28_arithmetic_row8 :
    (BiPoly.mul h2p27 h2p16).getD 8 []=h2p28.getD 8 [] := by
  decide +kernel

theorem h2n28_arithmetic_row9 :
    (BiPoly.mul h2p27 h2p16).getD 9 []=h2p28.getD 9 [] := by
  decide +kernel

theorem h2n28_arithmetic_row10 :
    (BiPoly.mul h2p27 h2p16).getD 10 []=h2p28.getD 10 [] := by
  decide +kernel

theorem h2n28_arithmetic_row11 :
    (BiPoly.mul h2p27 h2p16).getD 11 []=h2p28.getD 11 [] := by
  decide +kernel

theorem h2n28_arithmetic_row12 :
    (BiPoly.mul h2p27 h2p16).getD 12 []=h2p28.getD 12 [] := by
  decide +kernel

theorem h2n28_arithmetic_row13 :
    (BiPoly.mul h2p27 h2p16).getD 13 []=h2p28.getD 13 [] := by
  decide +kernel

theorem h2n28_arithmetic_row14 :
    (BiPoly.mul h2p27 h2p16).getD 14 []=h2p28.getD 14 [] := by
  decide +kernel

theorem h2n28_arithmetic_row15 :
    (BiPoly.mul h2p27 h2p16).getD 15 []=h2p28.getD 15 [] := by
  decide +kernel

theorem h2n28_arithmetic : BiPoly.mul h2p27 h2p16=h2p28 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<16 at hk
    have hf : ∀ j : Fin 16, (BiPoly.mul h2p27 h2p16).getD j.val []=h2p28.getD j.val [] :=
      (fun j => Fin.cases h2n28_arithmetic_row0 (fun j => Fin.cases h2n28_arithmetic_row1 (fun j => Fin.cases h2n28_arithmetic_row2 (fun j => Fin.cases h2n28_arithmetic_row3 (fun j => Fin.cases h2n28_arithmetic_row4 (fun j => Fin.cases h2n28_arithmetic_row5 (fun j => Fin.cases h2n28_arithmetic_row6 (fun j => Fin.cases h2n28_arithmetic_row7 (fun j => Fin.cases h2n28_arithmetic_row8 (fun j => Fin.cases h2n28_arithmetic_row9 (fun j => Fin.cases h2n28_arithmetic_row10 (fun j => Fin.cases h2n28_arithmetic_row11 (fun j => Fin.cases h2n28_arithmetic_row12 (fun j => Fin.cases h2n28_arithmetic_row13 (fun j => Fin.cases h2n28_arithmetic_row14 (fun j => Fin.cases h2n28_arithmetic_row15 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h2n28 : h2e28.toBi mapPolyEnv=h2p28 := by
  change BiPoly.mul (h2e27.toBi mapPolyEnv) (h2e16.toBi mapPolyEnv)=h2p28
  rw [h2n27, h2n16]
  exact h2n28_arithmetic

#print axioms h2n28_arithmetic
end StackSorting.RationalLift
