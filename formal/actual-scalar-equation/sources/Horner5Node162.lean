import BivariateRowEquality
import Horner5Base
import Horner5Node161
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p162 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 929107584000), (Int.ofNat 5153923391040), (Int.negSucc 750301613279), (Int.negSucc 28025186228639), (Int.negSucc 1632937721759), (Int.ofNat 21417131086560)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 7981679360159), (Int.negSucc 38136945459311), (Int.ofNat 28192282709760), (Int.ofNat 217772291271744), (Int.negSucc 41107497711263), (Int.negSucc 147755347995023), (Int.ofNat 16580517927552)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 30802970420640), (Int.ofNat 124212722565888), (Int.negSucc 169789080758039), (Int.negSucc 720036503472239), (Int.ofNat 232534940711904), (Int.ofNat 390190074837264), (Int.negSucc 39079604959559), (Int.ofNat 4424757601536)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 70421483504519), (Int.negSucc 232988745364235), (Int.ofNat 480207504725676), (Int.ofNat 1362116415194424), (Int.negSucc 348046103724479), (Int.negSucc 566487868465691), (Int.negSucc 123874478625923), (Int.ofNat 12794640963696), (Int.ofNat 456538470912)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 105859578814560), (Int.ofNat 275285035300968), (Int.negSucc 799469473405715), (Int.negSucc 1712266322568479), (Int.negSucc 265657403379671), (Int.ofNat 641816894246184), (Int.ofNat 538092494983836), (Int.negSucc 70825810173983), (Int.ofNat 4515058809504), (Int.ofNat 13265081856)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 109742734734479), (Int.negSucc 208066732626023), (Int.ofNat 863257857470172), (Int.ofNat 1661672187065304), (Int.ofNat 1553801231145168), (Int.negSucc 602445136149071), (Int.negSucc 734603777559323), (Int.negSucc 16384378765391), (Int.ofNat 1151552667312), (Int.ofNat 306561333312)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 79970053338720), (Int.ofNat 93467019665808), (Int.negSucc 643010530197023), (Int.negSucc 1461779806514435), (Int.negSucc 2346458198854031), (Int.ofNat 200898988488), (Int.ofNat 484695348276096), (Int.ofNat 308975630122188), (Int.negSucc 34937619529751), (Int.ofNat 1210655255616)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 40917768956639), (Int.negSucc 14907858514559), (Int.ofNat 354692202366780), (Int.ofNat 1217602644828480), (Int.ofNat 2014773987084012), (Int.ofNat 1080455957893836), (Int.negSucc 156180045578111), (Int.negSucc 385023301961111), (Int.ofNat 6943438615932), (Int.negSucc 413499303791)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 14392311397920), (Int.negSucc 9169744405823), (Int.negSucc 161711298915767), (Int.negSucc 866177232727859), (Int.negSucc 1229997308100767), (Int.negSucc 1582799549936471), (Int.negSucc 166808720724227), (Int.ofNat 127449529183908), (Int.ofNat 89700350803416), (Int.negSucc 6042814731647)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3311730858959), (Int.ofNat 7051591956312), (Int.ofNat 67073064861852), (Int.ofNat 473600566266552), (Int.ofNat 682242493500288), (Int.ofNat 1129126903712640), (Int.ofNat 495591723865008), (Int.ofNat 70917197408352), (Int.negSucc 86429608420535), (Int.ofNat 680890097952)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 448437790080), (Int.negSucc 2247248455055), (Int.negSucc 24070164073415), (Int.negSucc 187901897690771), (Int.negSucc 382217563278647), (Int.negSucc 476928892572263), (Int.negSucc 526483137322799), (Int.negSucc 109540563336935), (Int.negSucc 1236806645687), (Int.ofNat 10776164241888)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 27061931159), (Int.ofNat 373521196044), (Int.ofNat 6298820312040), (Int.ofNat 51784496749944), (Int.ofNat 178700213154780), (Int.ofNat 155873077672464), (Int.ofNat 274723877912832), (Int.ofNat 109653046697952), (Int.ofNat 32512254341616), (Int.negSucc 5744779915391)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 26539251047), (Int.negSucc 988645666643), (Int.negSucc 9256659825707), (Int.negSucc 56410966114775), (Int.negSucc 60871079851055), (Int.negSucc 70854534024191), (Int.negSucc 73840566889871), (Int.negSucc 17817956656415), (Int.negSucc 2963729782655)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 67762183608), (Int.ofNat 931760808768), (Int.ofNat 10340558103528), (Int.ofNat 22650157718208), (Int.ofNat 10172936192688), (Int.ofNat 24212148584544), (Int.ofNat 7692712619616), (Int.ofNat 2654107741440)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 36753157079), (Int.negSucc 881282753351), (Int.negSucc 4860535936175), (Int.negSucc 2666400949439), (Int.negSucc 2600323723295), (Int.negSucc 2942159902559), (Int.negSucc 472347676799)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 15837939072), (Int.ofNat 422629246944), (Int.ofNat 784835435808), (Int.negSucc 113443364159), (Int.ofNat 472347676800)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 4239140831), (Int.negSucc 70852151519)]]

theorem h5n162_arithmetic_row0 :
    (BiPoly.mul h5p34 h5p161).getD 0 []=h5p162.getD 0 [] := by
  decide +kernel

theorem h5n162_arithmetic_row1 :
    (BiPoly.mul h5p34 h5p161).getD 1 []=h5p162.getD 1 [] := by
  decide +kernel

theorem h5n162_arithmetic_row2 :
    (BiPoly.mul h5p34 h5p161).getD 2 []=h5p162.getD 2 [] := by
  decide +kernel

theorem h5n162_arithmetic_row3 :
    (BiPoly.mul h5p34 h5p161).getD 3 []=h5p162.getD 3 [] := by
  decide +kernel

theorem h5n162_arithmetic_row4 :
    (BiPoly.mul h5p34 h5p161).getD 4 []=h5p162.getD 4 [] := by
  decide +kernel

theorem h5n162_arithmetic_row5 :
    (BiPoly.mul h5p34 h5p161).getD 5 []=h5p162.getD 5 [] := by
  decide +kernel

theorem h5n162_arithmetic_row6 :
    (BiPoly.mul h5p34 h5p161).getD 6 []=h5p162.getD 6 [] := by
  decide +kernel

theorem h5n162_arithmetic_row7 :
    (BiPoly.mul h5p34 h5p161).getD 7 []=h5p162.getD 7 [] := by
  decide +kernel

theorem h5n162_arithmetic_row8 :
    (BiPoly.mul h5p34 h5p161).getD 8 []=h5p162.getD 8 [] := by
  decide +kernel

theorem h5n162_arithmetic_row9 :
    (BiPoly.mul h5p34 h5p161).getD 9 []=h5p162.getD 9 [] := by
  decide +kernel

theorem h5n162_arithmetic_row10 :
    (BiPoly.mul h5p34 h5p161).getD 10 []=h5p162.getD 10 [] := by
  decide +kernel

theorem h5n162_arithmetic_row11 :
    (BiPoly.mul h5p34 h5p161).getD 11 []=h5p162.getD 11 [] := by
  decide +kernel

theorem h5n162_arithmetic_row12 :
    (BiPoly.mul h5p34 h5p161).getD 12 []=h5p162.getD 12 [] := by
  decide +kernel

theorem h5n162_arithmetic_row13 :
    (BiPoly.mul h5p34 h5p161).getD 13 []=h5p162.getD 13 [] := by
  decide +kernel

theorem h5n162_arithmetic_row14 :
    (BiPoly.mul h5p34 h5p161).getD 14 []=h5p162.getD 14 [] := by
  decide +kernel

theorem h5n162_arithmetic_row15 :
    (BiPoly.mul h5p34 h5p161).getD 15 []=h5p162.getD 15 [] := by
  decide +kernel

theorem h5n162_arithmetic_row16 :
    (BiPoly.mul h5p34 h5p161).getD 16 []=h5p162.getD 16 [] := by
  decide +kernel

theorem h5n162_arithmetic : BiPoly.mul h5p34 h5p161=h5p162 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p34 h5p161).getD j.val []=h5p162.getD j.val [] :=
      (fun j => Fin.cases h5n162_arithmetic_row0 (fun j => Fin.cases h5n162_arithmetic_row1 (fun j => Fin.cases h5n162_arithmetic_row2 (fun j => Fin.cases h5n162_arithmetic_row3 (fun j => Fin.cases h5n162_arithmetic_row4 (fun j => Fin.cases h5n162_arithmetic_row5 (fun j => Fin.cases h5n162_arithmetic_row6 (fun j => Fin.cases h5n162_arithmetic_row7 (fun j => Fin.cases h5n162_arithmetic_row8 (fun j => Fin.cases h5n162_arithmetic_row9 (fun j => Fin.cases h5n162_arithmetic_row10 (fun j => Fin.cases h5n162_arithmetic_row11 (fun j => Fin.cases h5n162_arithmetic_row12 (fun j => Fin.cases h5n162_arithmetic_row13 (fun j => Fin.cases h5n162_arithmetic_row14 (fun j => Fin.cases h5n162_arithmetic_row15 (fun j => Fin.cases h5n162_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n162 : h5e162.toBi mapPolyEnv=h5p162 := by
  change BiPoly.mul (h5e34.toBi mapPolyEnv) (h5e161.toBi mapPolyEnv)=h5p162
  rw [h5n34, h5n161]
  exact h5n162_arithmetic

#print axioms h5n162_arithmetic
end StackSorting.RationalLift
