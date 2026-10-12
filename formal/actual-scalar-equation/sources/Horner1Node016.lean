import BivariateRowEquality
import Horner1Base
import Horner1Node015
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p16 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 51617088000), (Int.ofNat 234711989280), (Int.negSucc 276395412239), (Int.negSucc 1280559378239), (Int.ofNat 1189840615920)], [(Int.ofNat 0), (Int.negSucc 391809543119), (Int.negSucc 1492197659783), (Int.ofNat 2782040175864), (Int.ofNat 8035861072104), (Int.negSucc 9129770329031), (Int.ofNat 921139884864)], [(Int.ofNat 0), (Int.ofNat 1319466591360), (Int.ofNat 4089042558072), (Int.negSucc 10739729090987), (Int.negSucc 21226437807587), (Int.ofNat 25015275295884), (Int.negSucc 2416909031171), (Int.ofNat 245819866752)], [(Int.ofNat 0), (Int.negSucc 2592838047779), (Int.negSucc 6261938581049), (Int.ofNat 22200404197044), (Int.ofNat 32246292172836), (Int.negSucc 26566911528311), (Int.negSucc 7321545750953), (Int.ofNat 685450138488), (Int.ofNat 25363248384)], [(Int.ofNat 0), (Int.ofNat 3288249664140), (Int.ofNat 5743424827086), (Int.negSucc 27957991374803), (Int.negSucc 34921623261719), (Int.negSucc 6404032898795), (Int.ofNat 34738981272630), (Int.negSucc 4159503635039), (Int.ofNat 250099651536), (Int.ofNat 736948992)], [(Int.ofNat 0), (Int.negSucc 2808568932219), (Int.negSucc 3007269164361), (Int.ofNat 23008047649012), (Int.ofNat 34385450592896), (Int.ofNat 45532807127484), (Int.negSucc 44263000085357), (Int.negSucc 707824525199), (Int.ofNat 47680911992), (Int.ofNat 17031185184)], [(Int.ofNat 0), (Int.ofNat 1634211808820), (Int.ofNat 551131230474), (Int.negSucc 13265890814629), (Int.negSucc 33558647843275), (Int.negSucc 51267333854463), (Int.ofNat 7015494824022), (Int.ofNat 19204199999450), (Int.negSucc 1991206302891), (Int.ofNat 67258625312)], [(Int.ofNat 0), (Int.negSucc 638997577659), (Int.ofNat 361914446214), (Int.ofNat 6077317092866), (Int.ofNat 28008626443218), (Int.ofNat 32655927873652), (Int.ofNat 34384897944472), (Int.negSucc 23857367143805), (Int.ofNat 475977398630), (Int.negSucc 22972183543)], [(Int.ofNat 0), (Int.ofNat 160575277780), (Int.negSucc 308091076333), (Int.negSucc 2598552881675), (Int.negSucc 17513778048875), (Int.negSucc 18163477860847), (Int.negSucc 35384932524483), (Int.ofNat 2260414229332), (Int.ofNat 5296092568404), (Int.negSucc 335711929535)], [(Int.ofNat 0), (Int.negSucc 23409769939), (Int.ofNat 107073802290), (Int.ofNat 1020654697248), (Int.ofNat 7776709824240), (Int.ofNat 11962173064928), (Int.ofNat 15382166839068), (Int.ofNat 14411120938320), (Int.negSucc 5175184069451), (Int.ofNat 37827227664)], [(Int.ofNat 0), (Int.ofNat 1503440620), (Int.negSucc 19276774721), (Int.negSucc 297299865441), (Int.negSucc 2364984626471), (Int.negSucc 6907151379635), (Int.negSucc 4206731368643), (Int.negSucc 10631210877635), (Int.negSucc 629560043867), (Int.ofNat 598675791216)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1474402836), (Int.ofNat 51160193502), (Int.ofNat 460771666134), (Int.ofNat 2559866573940), (Int.ofNat 1893017483664), (Int.ofNat 2738209300524), (Int.ofNat 2724066583272), (Int.negSucc 319154439743)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3764565755), (Int.negSucc 49722647315), (Int.negSucc 524353340675), (Int.negSucc 964355834051), (Int.negSucc 233797866767), (Int.negSucc 1144389266063), (Int.negSucc 164651654591)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2041842060), (Int.ofNat 48080267460), (Int.ofNat 245905993944), (Int.ofNat 85459261104), (Int.ofNat 115270838640), (Int.ofNat 147450430080)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 879885503), (Int.negSucc 23243894783), (Int.negSucc 39430230191), (Int.ofNat 10238639760), (Int.negSucc 26241537599)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 235507824), (Int.ofNat 3936230640)]]

theorem h1n16_arithmetic_row0 :
    (BiPoly.mul h1p4 h1p15).getD 0 []=h1p16.getD 0 [] := by
  decide +kernel

theorem h1n16_arithmetic_row1 :
    (BiPoly.mul h1p4 h1p15).getD 1 []=h1p16.getD 1 [] := by
  decide +kernel

theorem h1n16_arithmetic_row2 :
    (BiPoly.mul h1p4 h1p15).getD 2 []=h1p16.getD 2 [] := by
  decide +kernel

theorem h1n16_arithmetic_row3 :
    (BiPoly.mul h1p4 h1p15).getD 3 []=h1p16.getD 3 [] := by
  decide +kernel

theorem h1n16_arithmetic_row4 :
    (BiPoly.mul h1p4 h1p15).getD 4 []=h1p16.getD 4 [] := by
  decide +kernel

theorem h1n16_arithmetic_row5 :
    (BiPoly.mul h1p4 h1p15).getD 5 []=h1p16.getD 5 [] := by
  decide +kernel

theorem h1n16_arithmetic_row6 :
    (BiPoly.mul h1p4 h1p15).getD 6 []=h1p16.getD 6 [] := by
  decide +kernel

theorem h1n16_arithmetic_row7 :
    (BiPoly.mul h1p4 h1p15).getD 7 []=h1p16.getD 7 [] := by
  decide +kernel

theorem h1n16_arithmetic_row8 :
    (BiPoly.mul h1p4 h1p15).getD 8 []=h1p16.getD 8 [] := by
  decide +kernel

theorem h1n16_arithmetic_row9 :
    (BiPoly.mul h1p4 h1p15).getD 9 []=h1p16.getD 9 [] := by
  decide +kernel

theorem h1n16_arithmetic_row10 :
    (BiPoly.mul h1p4 h1p15).getD 10 []=h1p16.getD 10 [] := by
  decide +kernel

theorem h1n16_arithmetic_row11 :
    (BiPoly.mul h1p4 h1p15).getD 11 []=h1p16.getD 11 [] := by
  decide +kernel

theorem h1n16_arithmetic_row12 :
    (BiPoly.mul h1p4 h1p15).getD 12 []=h1p16.getD 12 [] := by
  decide +kernel

theorem h1n16_arithmetic_row13 :
    (BiPoly.mul h1p4 h1p15).getD 13 []=h1p16.getD 13 [] := by
  decide +kernel

theorem h1n16_arithmetic_row14 :
    (BiPoly.mul h1p4 h1p15).getD 14 []=h1p16.getD 14 [] := by
  decide +kernel

theorem h1n16_arithmetic_row15 :
    (BiPoly.mul h1p4 h1p15).getD 15 []=h1p16.getD 15 [] := by
  decide +kernel

theorem h1n16_arithmetic : BiPoly.mul h1p4 h1p15=h1p16 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<16 at hk
    have hf : ∀ j : Fin 16, (BiPoly.mul h1p4 h1p15).getD j.val []=h1p16.getD j.val [] :=
      (fun j => Fin.cases h1n16_arithmetic_row0 (fun j => Fin.cases h1n16_arithmetic_row1 (fun j => Fin.cases h1n16_arithmetic_row2 (fun j => Fin.cases h1n16_arithmetic_row3 (fun j => Fin.cases h1n16_arithmetic_row4 (fun j => Fin.cases h1n16_arithmetic_row5 (fun j => Fin.cases h1n16_arithmetic_row6 (fun j => Fin.cases h1n16_arithmetic_row7 (fun j => Fin.cases h1n16_arithmetic_row8 (fun j => Fin.cases h1n16_arithmetic_row9 (fun j => Fin.cases h1n16_arithmetic_row10 (fun j => Fin.cases h1n16_arithmetic_row11 (fun j => Fin.cases h1n16_arithmetic_row12 (fun j => Fin.cases h1n16_arithmetic_row13 (fun j => Fin.cases h1n16_arithmetic_row14 (fun j => Fin.cases h1n16_arithmetic_row15 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n16 : h1e16.toBi mapPolyEnv=h1p16 := by
  change BiPoly.mul (h1e4.toBi mapPolyEnv) (h1e15.toBi mapPolyEnv)=h1p16
  rw [h1n4, h1n15]
  exact h1n16_arithmetic

#print axioms h1n16_arithmetic
end StackSorting.RationalLift
