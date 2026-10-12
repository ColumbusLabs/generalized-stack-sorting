import BivariateRowEquality
import Horner1Base
import Horner1Node016
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p44 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 929107584000), (Int.ofNat 4224815807040), (Int.negSucc 4975117420319), (Int.negSucc 23050068808319), (Int.ofNat 21417131086560)], [(Int.ofNat 0), (Int.negSucc 7052571776159), (Int.negSucc 26859557876111), (Int.ofNat 50076723165552), (Int.ofNat 144645499297872), (Int.negSucc 164335865922575), (Int.ofNat 16580517927552)], [(Int.ofNat 0), (Int.ofNat 23750398644480), (Int.ofNat 73602766045296), (Int.negSucc 193315123637783), (Int.negSucc 382075880536583), (Int.ofNat 450274955325912), (Int.negSucc 43504362561095), (Int.ofNat 4424757601536)], [(Int.ofNat 0), (Int.negSucc 46671084860039), (Int.negSucc 112714894458899), (Int.ofNat 399607275546792), (Int.ofNat 580433259111048), (Int.negSucc 478204407509615), (Int.negSucc 131787823517171), (Int.ofNat 12338102492784), (Int.ofNat 456538470912)], [(Int.ofNat 0), (Int.ofNat 59188493954520), (Int.ofNat 103381646887548), (Int.negSucc 503243844746471), (Int.negSucc 628589218710959), (Int.negSucc 115272592178327), (Int.ofNat 625301662907340), (Int.negSucc 74871065430719), (Int.ofNat 4501793727648), (Int.ofNat 13265081856)], [(Int.ofNat 0), (Int.negSucc 50554240779959), (Int.negSucc 54130844958515), (Int.ofNat 414144857682216), (Int.ofNat 618938110672128), (Int.ofNat 819590528294712), (Int.negSucc 796734001536443), (Int.negSucc 12740841453599), (Int.ofNat 858256415856), (Int.ofNat 306561333312)], [(Int.ofNat 0), (Int.ofNat 29415812558760), (Int.ofNat 9920362148532), (Int.negSucc 238786034663339), (Int.negSucc 604055661178967), (Int.negSucc 922812009380351), (Int.ofNat 126278906832396), (Int.ofNat 345675599990100), (Int.negSucc 35841713452055), (Int.ofNat 1210655255616)], [(Int.ofNat 0), (Int.negSucc 11501956397879), (Int.ofNat 6514460031852), (Int.ofNat 109391707671588), (Int.ofNat 504155275977924), (Int.ofNat 587806701725736), (Int.ofNat 618928163000496), (Int.negSucc 429432608588507), (Int.ofNat 8567593175340), (Int.negSucc 413499303791)], [(Int.ofNat 0), (Int.ofNat 2890355000040), (Int.negSucc 5545639374011), (Int.negSucc 46773951870167), (Int.negSucc 315248004879767), (Int.negSucc 326942601495263), (Int.negSucc 636928785440711), (Int.ofNat 40687456127976), (Int.ofNat 95329666231272), (Int.negSucc 6042814731647)], [(Int.ofNat 0), (Int.negSucc 421375858919), (Int.ofNat 1927328441220), (Int.ofNat 18371784550464), (Int.ofNat 139980776836320), (Int.ofNat 215319115168704), (Int.ofNat 276879003103224), (Int.ofNat 259400176889760), (Int.negSucc 93153313250135), (Int.ofNat 680890097952)], [(Int.ofNat 0), (Int.ofNat 27061931160), (Int.negSucc 346981944995), (Int.negSucc 5351397577955), (Int.negSucc 42569723276495), (Int.negSucc 124328724833447), (Int.negSucc 75721164635591), (Int.negSucc 191361795797447), (Int.negSucc 11332080789623), (Int.ofNat 10776164241888)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 26539251048), (Int.ofNat 920883483036), (Int.ofNat 8293889990412), (Int.ofNat 46077598330920), (Int.ofNat 34074314705952), (Int.ofNat 49287767409432), (Int.ofNat 49033198498896), (Int.negSucc 5744779915391)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 67762183607), (Int.negSucc 895007651687), (Int.negSucc 9438360132167), (Int.negSucc 17358405012935), (Int.negSucc 4208361601823), (Int.negSucc 20599006789151), (Int.negSucc 2963729782655)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 36753157080), (Int.ofNat 865444814280), (Int.ofNat 4426307890992), (Int.ofNat 1538266699872), (Int.ofNat 2074875095520), (Int.ofNat 2654107741440)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 15837939071), (Int.negSucc 418390106111), (Int.negSucc 709744143455), (Int.ofNat 184295515680), (Int.negSucc 472347676799)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4239140832), (Int.ofNat 70852151520)]]

theorem h1n44_arithmetic_row0 :
    (BiPoly.mul h1p43 h1p16).getD 0 []=h1p44.getD 0 [] := by
  decide +kernel

theorem h1n44_arithmetic_row1 :
    (BiPoly.mul h1p43 h1p16).getD 1 []=h1p44.getD 1 [] := by
  decide +kernel

theorem h1n44_arithmetic_row2 :
    (BiPoly.mul h1p43 h1p16).getD 2 []=h1p44.getD 2 [] := by
  decide +kernel

theorem h1n44_arithmetic_row3 :
    (BiPoly.mul h1p43 h1p16).getD 3 []=h1p44.getD 3 [] := by
  decide +kernel

theorem h1n44_arithmetic_row4 :
    (BiPoly.mul h1p43 h1p16).getD 4 []=h1p44.getD 4 [] := by
  decide +kernel

theorem h1n44_arithmetic_row5 :
    (BiPoly.mul h1p43 h1p16).getD 5 []=h1p44.getD 5 [] := by
  decide +kernel

theorem h1n44_arithmetic_row6 :
    (BiPoly.mul h1p43 h1p16).getD 6 []=h1p44.getD 6 [] := by
  decide +kernel

theorem h1n44_arithmetic_row7 :
    (BiPoly.mul h1p43 h1p16).getD 7 []=h1p44.getD 7 [] := by
  decide +kernel

theorem h1n44_arithmetic_row8 :
    (BiPoly.mul h1p43 h1p16).getD 8 []=h1p44.getD 8 [] := by
  decide +kernel

theorem h1n44_arithmetic_row9 :
    (BiPoly.mul h1p43 h1p16).getD 9 []=h1p44.getD 9 [] := by
  decide +kernel

theorem h1n44_arithmetic_row10 :
    (BiPoly.mul h1p43 h1p16).getD 10 []=h1p44.getD 10 [] := by
  decide +kernel

theorem h1n44_arithmetic_row11 :
    (BiPoly.mul h1p43 h1p16).getD 11 []=h1p44.getD 11 [] := by
  decide +kernel

theorem h1n44_arithmetic_row12 :
    (BiPoly.mul h1p43 h1p16).getD 12 []=h1p44.getD 12 [] := by
  decide +kernel

theorem h1n44_arithmetic_row13 :
    (BiPoly.mul h1p43 h1p16).getD 13 []=h1p44.getD 13 [] := by
  decide +kernel

theorem h1n44_arithmetic_row14 :
    (BiPoly.mul h1p43 h1p16).getD 14 []=h1p44.getD 14 [] := by
  decide +kernel

theorem h1n44_arithmetic_row15 :
    (BiPoly.mul h1p43 h1p16).getD 15 []=h1p44.getD 15 [] := by
  decide +kernel

theorem h1n44_arithmetic : BiPoly.mul h1p43 h1p16=h1p44 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<16 at hk
    have hf : ∀ j : Fin 16, (BiPoly.mul h1p43 h1p16).getD j.val []=h1p44.getD j.val [] :=
      (fun j => Fin.cases h1n44_arithmetic_row0 (fun j => Fin.cases h1n44_arithmetic_row1 (fun j => Fin.cases h1n44_arithmetic_row2 (fun j => Fin.cases h1n44_arithmetic_row3 (fun j => Fin.cases h1n44_arithmetic_row4 (fun j => Fin.cases h1n44_arithmetic_row5 (fun j => Fin.cases h1n44_arithmetic_row6 (fun j => Fin.cases h1n44_arithmetic_row7 (fun j => Fin.cases h1n44_arithmetic_row8 (fun j => Fin.cases h1n44_arithmetic_row9 (fun j => Fin.cases h1n44_arithmetic_row10 (fun j => Fin.cases h1n44_arithmetic_row11 (fun j => Fin.cases h1n44_arithmetic_row12 (fun j => Fin.cases h1n44_arithmetic_row13 (fun j => Fin.cases h1n44_arithmetic_row14 (fun j => Fin.cases h1n44_arithmetic_row15 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n44 : h1e44.toBi mapPolyEnv=h1p44 := by
  change BiPoly.mul (h1e43.toBi mapPolyEnv) (h1e16.toBi mapPolyEnv)=h1p44
  rw [h1n43, h1n16]
  exact h1n44_arithmetic

#print axioms h1n44_arithmetic
end StackSorting.RationalLift
