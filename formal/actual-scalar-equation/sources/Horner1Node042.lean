import BivariateRowEquality
import Horner1Base
import Horner1Node041
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p42 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 522623015999), (Int.negSucc 4172975508959), (Int.negSucc 8018394405119), (Int.ofNat 3117557302560), (Int.ofNat 7485599214720)], [(Int.ofNat 0), (Int.ofNat 4025745735840), (Int.ofNat 30723263365968), (Int.ofNat 53096584164912), (Int.negSucc 31776643358351), (Int.negSucc 40492031980751), (Int.ofNat 1847764177344)], [(Int.ofNat 0), (Int.negSucc 13784063757839), (Int.negSucc 101896636109687), (Int.negSucc 167140089999143), (Int.ofNat 100004345726904), (Int.ofNat 85295535091992), (Int.ofNat 14468050224000), (Int.negSucc 1345418481023)], [(Int.ofNat 0), (Int.ofNat 27601804081080), (Int.ofNat 201391020428364), (Int.ofNat 340131318245640), (Int.negSucc 115967889555335), (Int.negSucc 107209905734447), (Int.negSucc 93936093970499), (Int.ofNat 11334374358192), (Int.negSucc 530966506751)], [(Int.ofNat 0), (Int.negSucc 35764659420119), (Int.negSucc 264174844823243), (Int.negSucc 504534524526647), (Int.negSucc 61649960499791), (Int.ofNat 118868922749016), (Int.ofNat 176008012874244), (Int.negSucc 5506623475775), (Int.ofNat 465425808192), (Int.negSucc 48638633471)], [(Int.ofNat 0), (Int.ofNat 31306761563400), (Int.ofNat 241975758980556), (Int.ofNat 566887604084568), (Int.ofNat 383352678304416), (Int.negSucc 93612301700615), (Int.negSucc 131640832607147), (Int.negSucc 64925210856527), (Int.ofNat 7212111728112), (Int.negSucc 186659104319)], [(Int.ofNat 0), (Int.negSucc 18735948696839), (Int.negSucc 158061426942035), (Int.negSucc 479482169936003), (Int.negSucc 600813547934831), (Int.negSucc 55267805104367), (Int.ofNat 14240453663196), (Int.ofNat 122310493086780), (Int.negSucc 7306080730655), (Int.ofNat 364679244480)], [(Int.ofNat 0), (Int.ofNat 7565915266440), (Int.ofNat 73547667415980), (Int.ofNat 297603916701012), (Int.ofNat 559521096308436), (Int.ofNat 262460681414760), (Int.ofNat 49658880421056), (Int.negSucc 60560597849483), (Int.negSucc 21212833826723), (Int.ofNat 1471989551664)], [(Int.ofNat 0), (Int.negSucc 1972689203879), (Int.negSucc 23803434143891), (Int.negSucc 130895659111991), (Int.negSucc 348978843113207), (Int.negSucc 337246089360671), (Int.negSucc 78815782536503), (Int.negSucc 30552949924247), (Int.ofNat 34528389652200), (Int.negSucc 1271421860063)], [(Int.ofNat 0), (Int.ofNat 299976132120), (Int.ofNat 5071053414756), (Int.ofNat 38849826657936), (Int.ofNat 148173317306976), (Int.ofNat 241492187816544), (Int.ofNat 102733628556216), (Int.ofNat 46999733413056), (Int.negSucc 7380130931495), (Int.negSucc 3073827588767)], [(Int.ofNat 0), (Int.negSucc 20218684199), (Int.negSucc 634320973043), (Int.negSucc 7178543328299), (Int.negSucc 41364580594535), (Int.negSucc 106381244700599), (Int.negSucc 87656150479031), (Int.negSucc 28263177684791), (Int.negSucc 12773841280055), (Int.ofNat 3040299822240)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 34874895240), (Int.ofNat 703989691020), (Int.ofNat 6940375147116), (Int.ofNat 28670947666632), (Int.ofNat 43512432456240), (Int.ofNat 17190602121816), (Int.ofNat 8911335917808), (Int.ofNat 421444104768)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 23858237879), (Int.negSucc 568500093719), (Int.negSucc 4360221551735), (Int.negSucc 12003203446343), (Int.negSucc 9126338577695), (Int.negSucc 2690295369695), (Int.negSucc 1148821170047)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 10595053368), (Int.ofNat 298625860296), (Int.ofNat 1657881886032), (Int.ofNat 2718190807200), (Int.ofNat 836269853472), (Int.ofNat 359581617792)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3329823167), (Int.negSucc 84897248255), (Int.negSucc 347812551071), (Int.negSucc 253875376223), (Int.negSucc 31489845119)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 471015648), (Int.ofNat 9756523872), (Int.ofNat 31489845120)]]

theorem h1n42_arithmetic_row0 :
    (BiPoly.mul h1p5 h1p41).getD 0 []=h1p42.getD 0 [] := by
  decide +kernel

theorem h1n42_arithmetic_row1 :
    (BiPoly.mul h1p5 h1p41).getD 1 []=h1p42.getD 1 [] := by
  decide +kernel

theorem h1n42_arithmetic_row2 :
    (BiPoly.mul h1p5 h1p41).getD 2 []=h1p42.getD 2 [] := by
  decide +kernel

theorem h1n42_arithmetic_row3 :
    (BiPoly.mul h1p5 h1p41).getD 3 []=h1p42.getD 3 [] := by
  decide +kernel

theorem h1n42_arithmetic_row4 :
    (BiPoly.mul h1p5 h1p41).getD 4 []=h1p42.getD 4 [] := by
  decide +kernel

theorem h1n42_arithmetic_row5 :
    (BiPoly.mul h1p5 h1p41).getD 5 []=h1p42.getD 5 [] := by
  decide +kernel

theorem h1n42_arithmetic_row6 :
    (BiPoly.mul h1p5 h1p41).getD 6 []=h1p42.getD 6 [] := by
  decide +kernel

theorem h1n42_arithmetic_row7 :
    (BiPoly.mul h1p5 h1p41).getD 7 []=h1p42.getD 7 [] := by
  decide +kernel

theorem h1n42_arithmetic_row8 :
    (BiPoly.mul h1p5 h1p41).getD 8 []=h1p42.getD 8 [] := by
  decide +kernel

theorem h1n42_arithmetic_row9 :
    (BiPoly.mul h1p5 h1p41).getD 9 []=h1p42.getD 9 [] := by
  decide +kernel

theorem h1n42_arithmetic_row10 :
    (BiPoly.mul h1p5 h1p41).getD 10 []=h1p42.getD 10 [] := by
  decide +kernel

theorem h1n42_arithmetic_row11 :
    (BiPoly.mul h1p5 h1p41).getD 11 []=h1p42.getD 11 [] := by
  decide +kernel

theorem h1n42_arithmetic_row12 :
    (BiPoly.mul h1p5 h1p41).getD 12 []=h1p42.getD 12 [] := by
  decide +kernel

theorem h1n42_arithmetic_row13 :
    (BiPoly.mul h1p5 h1p41).getD 13 []=h1p42.getD 13 [] := by
  decide +kernel

theorem h1n42_arithmetic_row14 :
    (BiPoly.mul h1p5 h1p41).getD 14 []=h1p42.getD 14 [] := by
  decide +kernel

theorem h1n42_arithmetic_row15 :
    (BiPoly.mul h1p5 h1p41).getD 15 []=h1p42.getD 15 [] := by
  decide +kernel

theorem h1n42_arithmetic : BiPoly.mul h1p5 h1p41=h1p42 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<16 at hk
    have hf : ∀ j : Fin 16, (BiPoly.mul h1p5 h1p41).getD j.val []=h1p42.getD j.val [] :=
      (fun j => Fin.cases h1n42_arithmetic_row0 (fun j => Fin.cases h1n42_arithmetic_row1 (fun j => Fin.cases h1n42_arithmetic_row2 (fun j => Fin.cases h1n42_arithmetic_row3 (fun j => Fin.cases h1n42_arithmetic_row4 (fun j => Fin.cases h1n42_arithmetic_row5 (fun j => Fin.cases h1n42_arithmetic_row6 (fun j => Fin.cases h1n42_arithmetic_row7 (fun j => Fin.cases h1n42_arithmetic_row8 (fun j => Fin.cases h1n42_arithmetic_row9 (fun j => Fin.cases h1n42_arithmetic_row10 (fun j => Fin.cases h1n42_arithmetic_row11 (fun j => Fin.cases h1n42_arithmetic_row12 (fun j => Fin.cases h1n42_arithmetic_row13 (fun j => Fin.cases h1n42_arithmetic_row14 (fun j => Fin.cases h1n42_arithmetic_row15 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n42 : h1e42.toBi mapPolyEnv=h1p42 := by
  change BiPoly.mul (h1e5.toBi mapPolyEnv) (h1e41.toBi mapPolyEnv)=h1p42
  rw [h1n5, h1n41]
  exact h1n42_arithmetic

#print axioms h1n42_arithmetic
end StackSorting.RationalLift
