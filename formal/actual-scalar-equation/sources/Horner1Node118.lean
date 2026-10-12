import BivariateRowEquality
import Horner1Base
import Horner1Node016
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p118 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 258085439999), (Int.negSucc 1173559946399), (Int.ofNat 1381977061200), (Int.ofNat 6402796891200), (Int.negSucc 5949203079599)], [(Int.ofNat 0), (Int.ofNat 1959047715600), (Int.ofNat 7460988298920), (Int.negSucc 13910200879319), (Int.negSucc 40179305360519), (Int.ofNat 45648851645160), (Int.negSucc 4605699424319)], [(Int.ofNat 0), (Int.negSucc 6597332956799), (Int.negSucc 20445212790359), (Int.ofNat 53698645454940), (Int.ofNat 106132189037940), (Int.negSucc 125076376479419), (Int.ofNat 12084545155860), (Int.negSucc 1229099333759)], [(Int.ofNat 0), (Int.ofNat 12964190238900), (Int.ofNat 31309692905250), (Int.negSucc 111002020985219), (Int.negSucc 161231460864179), (Int.ofNat 132834557641560), (Int.ofNat 36607728754770), (Int.negSucc 3427250692439), (Int.negSucc 126816241919)], [(Int.ofNat 0), (Int.negSucc 16441248320699), (Int.negSucc 28717124135429), (Int.ofNat 139789956874020), (Int.ofNat 174608116308600), (Int.ofNat 32020164493980), (Int.negSucc 173694906363149), (Int.ofNat 20797518175200), (Int.negSucc 1250498257679), (Int.negSucc 3684744959)], [(Int.ofNat 0), (Int.ofNat 14042844661100), (Int.ofNat 15036345821810), (Int.negSucc 115040238245059), (Int.negSucc 171927252964479), (Int.negSucc 227664035637419), (Int.ofNat 221315000426790), (Int.ofNat 3539122626000), (Int.negSucc 238404559959), (Int.negSucc 85155925919)], [(Int.ofNat 0), (Int.negSucc 8171059044099), (Int.negSucc 2755656152369), (Int.ofNat 66329454073150), (Int.ofNat 167793239216380), (Int.ofNat 256336669272320), (Int.negSucc 35077474120109), (Int.negSucc 96020999997249), (Int.ofNat 9956031514460), (Int.negSucc 336293126559)], [(Int.ofNat 0), (Int.ofNat 3194987888300), (Int.negSucc 1809572231069), (Int.negSucc 30386585464329), (Int.negSucc 140043132216089), (Int.negSucc 163279639368259), (Int.negSucc 171924489722359), (Int.ofNat 119286835719030), (Int.negSucc 2379886993149), (Int.ofNat 114860917720)], [(Int.ofNat 0), (Int.negSucc 802876388899), (Int.ofNat 1540455381670), (Int.ofNat 12992764408380), (Int.ofNat 87568890244380), (Int.ofNat 90817389304240), (Int.ofNat 176924662622420), (Int.negSucc 11302071146659), (Int.negSucc 26480462842019), (Int.ofNat 1678559647680)], [(Int.ofNat 0), (Int.ofNat 117048849700), (Int.negSucc 535369011449), (Int.negSucc 5103273486239), (Int.negSucc 38883549121199), (Int.negSucc 59810865324639), (Int.negSucc 76910834195339), (Int.negSucc 72055604691599), (Int.ofNat 25875920347260), (Int.negSucc 189136138319)], [(Int.ofNat 0), (Int.negSucc 7517203099), (Int.ofNat 96383873610), (Int.ofNat 1486499327210), (Int.ofNat 11824923132360), (Int.ofNat 34535756898180), (Int.ofNat 21033656843220), (Int.ofNat 53156054388180), (Int.ofNat 3147800219340), (Int.negSucc 2993378956079)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 7372014179), (Int.negSucc 255800967509), (Int.negSucc 2303858330669), (Int.negSucc 12799332869699), (Int.negSucc 9465087418319), (Int.negSucc 13691046502619), (Int.negSucc 13620332916359), (Int.ofNat 1595772198720)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 18822828780), (Int.ofNat 248613236580), (Int.ofNat 2621766703380), (Int.ofNat 4821779170260), (Int.ofNat 1168989333840), (Int.ofNat 5721946330320), (Int.ofNat 823258272960)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 10209210299), (Int.negSucc 240401337299), (Int.negSucc 1229529969719), (Int.negSucc 427296305519), (Int.negSucc 576354193199), (Int.negSucc 737252150399)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4399427520), (Int.ofNat 116219473920), (Int.ofNat 197151150960), (Int.negSucc 51193198799), (Int.ofNat 131207688000)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1177539119), (Int.negSucc 19681153199)]]

theorem h1n118_arithmetic_row0 :
    (BiPoly.mul h1p117 h1p16).getD 0 []=h1p118.getD 0 [] := by
  decide +kernel

theorem h1n118_arithmetic_row1 :
    (BiPoly.mul h1p117 h1p16).getD 1 []=h1p118.getD 1 [] := by
  decide +kernel

theorem h1n118_arithmetic_row2 :
    (BiPoly.mul h1p117 h1p16).getD 2 []=h1p118.getD 2 [] := by
  decide +kernel

theorem h1n118_arithmetic_row3 :
    (BiPoly.mul h1p117 h1p16).getD 3 []=h1p118.getD 3 [] := by
  decide +kernel

theorem h1n118_arithmetic_row4 :
    (BiPoly.mul h1p117 h1p16).getD 4 []=h1p118.getD 4 [] := by
  decide +kernel

theorem h1n118_arithmetic_row5 :
    (BiPoly.mul h1p117 h1p16).getD 5 []=h1p118.getD 5 [] := by
  decide +kernel

theorem h1n118_arithmetic_row6 :
    (BiPoly.mul h1p117 h1p16).getD 6 []=h1p118.getD 6 [] := by
  decide +kernel

theorem h1n118_arithmetic_row7 :
    (BiPoly.mul h1p117 h1p16).getD 7 []=h1p118.getD 7 [] := by
  decide +kernel

theorem h1n118_arithmetic_row8 :
    (BiPoly.mul h1p117 h1p16).getD 8 []=h1p118.getD 8 [] := by
  decide +kernel

theorem h1n118_arithmetic_row9 :
    (BiPoly.mul h1p117 h1p16).getD 9 []=h1p118.getD 9 [] := by
  decide +kernel

theorem h1n118_arithmetic_row10 :
    (BiPoly.mul h1p117 h1p16).getD 10 []=h1p118.getD 10 [] := by
  decide +kernel

theorem h1n118_arithmetic_row11 :
    (BiPoly.mul h1p117 h1p16).getD 11 []=h1p118.getD 11 [] := by
  decide +kernel

theorem h1n118_arithmetic_row12 :
    (BiPoly.mul h1p117 h1p16).getD 12 []=h1p118.getD 12 [] := by
  decide +kernel

theorem h1n118_arithmetic_row13 :
    (BiPoly.mul h1p117 h1p16).getD 13 []=h1p118.getD 13 [] := by
  decide +kernel

theorem h1n118_arithmetic_row14 :
    (BiPoly.mul h1p117 h1p16).getD 14 []=h1p118.getD 14 [] := by
  decide +kernel

theorem h1n118_arithmetic_row15 :
    (BiPoly.mul h1p117 h1p16).getD 15 []=h1p118.getD 15 [] := by
  decide +kernel

theorem h1n118_arithmetic : BiPoly.mul h1p117 h1p16=h1p118 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<16 at hk
    have hf : ∀ j : Fin 16, (BiPoly.mul h1p117 h1p16).getD j.val []=h1p118.getD j.val [] :=
      (fun j => Fin.cases h1n118_arithmetic_row0 (fun j => Fin.cases h1n118_arithmetic_row1 (fun j => Fin.cases h1n118_arithmetic_row2 (fun j => Fin.cases h1n118_arithmetic_row3 (fun j => Fin.cases h1n118_arithmetic_row4 (fun j => Fin.cases h1n118_arithmetic_row5 (fun j => Fin.cases h1n118_arithmetic_row6 (fun j => Fin.cases h1n118_arithmetic_row7 (fun j => Fin.cases h1n118_arithmetic_row8 (fun j => Fin.cases h1n118_arithmetic_row9 (fun j => Fin.cases h1n118_arithmetic_row10 (fun j => Fin.cases h1n118_arithmetic_row11 (fun j => Fin.cases h1n118_arithmetic_row12 (fun j => Fin.cases h1n118_arithmetic_row13 (fun j => Fin.cases h1n118_arithmetic_row14 (fun j => Fin.cases h1n118_arithmetic_row15 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n118 : h1e118.toBi mapPolyEnv=h1p118 := by
  change BiPoly.mul (h1e117.toBi mapPolyEnv) (h1e16.toBi mapPolyEnv)=h1p118
  rw [h1n117, h1n16]
  exact h1n118_arithmetic

#print axioms h1n118_arithmetic
end StackSorting.RationalLift
