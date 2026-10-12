import BivariateRowEquality
import Horner4Base
import Horner4Node011
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p211 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 13381846282173014640), (Int.ofNat 68969934181768138560), (Int.negSucc 49985919522756303839), (Int.negSucc 357825068524897444799), (Int.ofNat 360195215679081846000)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 130700065895668239839), (Int.negSucc 716715660042837060479), (Int.ofNat 308229173972066900160), (Int.ofNat 3502725285504379852800), (Int.negSucc 3258319583840260105439), (Int.ofNat 197275231638846345600)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 620630370171177846480), (Int.ofNat 3328857307428590086560), (Int.negSucc 976956347026775557439), (Int.negSucc 14464226391938249454719), (Int.ofNat 12312078584114613322800), (Int.negSucc 899458313604982403039), (Int.ofNat 26010226242205223040)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1892809385523819172079), (Int.negSucc 9240056912405607840719), (Int.ofNat 2699534609014835288160), (Int.ofNat 31871886595532209378080), (Int.negSucc 22847178004239431496239), (Int.ofNat 264768493900941128880), (Int.ofNat 31268468834347129920), (Int.negSucc 274167985090982399)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4120897390601319080880), (Int.ofNat 17109521372137503538320), (Int.negSucc 6510915029571923212559), (Int.negSucc 37349642828157488700959), (Int.ofNat 14474281621009990730880), (Int.ofNat 6482042117525881557840), (Int.negSucc 429337292780842005359), (Int.ofNat 9996237107594305920), (Int.ofNat 695706877536000)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 6739069900625389942319), (Int.negSucc 22103573746891970379359), (Int.ofNat 10057175765171062258560), (Int.ofNat 14813429456160548119200), (Int.ofNat 21825131396560667282640), (Int.negSucc 16730232334770855899519), (Int.ofNat 405341318698036002240), (Int.ofNat 16571395007114271360), (Int.negSucc 50487872004345599)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 8494832052102813336780), (Int.ofNat 20082483750936418844760), (Int.negSucc 6145099144513512412619), (Int.ofNat 16309675396629440721840), (Int.negSucc 50960064687241085321819), (Int.ofNat 14208597247687244463000), (Int.ofNat 1658580014418633001740), (Int.negSucc 95581490813412339839), (Int.ofNat 831419216283647040)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 8347314251515711302599), (Int.negSucc 12629757116750708523239), (Int.negSucc 6740400828227871747359), (Int.negSucc 22547311588082656834799), (Int.ofNat 34773386159179042571400), (Int.ofNat 6315014247891802896840), (Int.negSucc 3957191273027750304719), (Int.negSucc 13323201761373718079), (Int.ofNat 3222661219865723520)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 6401115203458730693460), (Int.ofNat 5500667937079807188600), (Int.ofNat 17622995835599837165880), (Int.ofNat 7290903707159799695400), (Int.ofNat 4599999230186530101060), (Int.negSucc 21205682241626759746199), (Int.ofNat 2090776675188368595120), (Int.ofNat 345186510282711388200), (Int.negSucc 2988460929712341359)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3804216976134036425999), (Int.negSucc 2170158074845270234799), (Int.negSucc 16952699638485434972159), (Int.ofNat 1990187085253536468480), (Int.negSucc 20826014291084401155839), (Int.ofNat 13358857378536368229600), (Int.ofNat 2350553602924646145360), (Int.negSucc 293329413345232112879), (Int.negSucc 10823157634158341999)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1727365407366625000020), (Int.ofNat 1517115281597042836320), (Int.ofNat 8901775630295792334960), (Int.ofNat 839590655776795624680), (Int.ofNat 11674979500987518851220), (Int.ofNat 1453503514798389260760), (Int.negSucc 3345801997062562288859), (Int.negSucc 209690437465730984999), (Int.ofNat 10017181630755393660)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 586029335453169062039), (Int.negSucc 1270926371596201584359), (Int.negSucc 2457139638447523565159), (Int.negSucc 3967424310516441804839), (Int.negSucc 1812350634300595986239), (Int.negSucc 5759446932898984200479), (Int.ofNat 875029058945927323080), (Int.ofNat 380320904718747335160), (Int.ofNat 9263842516108974960)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 143681527236957417420), (Int.ofNat 752001784496113684200), (Int.ofNat 209739969059890256820), (Int.ofNat 2901229328078278673160), (Int.negSucc 341984828286895845239), (Int.ofNat 2806213212394504839120), (Int.ofNat 761212397190220311300), (Int.negSucc 101793678072521205599), (Int.negSucc 12585199236325866719)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 24193511761572841679), (Int.negSucc 291010052648074068959), (Int.ofNat 13322048399283629280), (Int.negSucc 968372370770381513999), (Int.negSucc 118924448995319252639), (Int.negSucc 479768593042538277839), (Int.negSucc 612339606747476431199), (Int.negSucc 88471253209269334319), (Int.ofNat 506232738712404000)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2576022820717180560), (Int.ofNat 73056427112750921880), (Int.ofNat 43604838674586917700), (Int.ofNat 124812147135839977080), (Int.ofNat 210783220044268225140), (Int.negSucc 31854919805264393279), (Int.ofNat 165702284135173006560), (Int.ofNat 66097753415074857600), (Int.ofNat 4521266371320626160)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 149941359897261119), (Int.negSucc 11435011026549433199), (Int.negSucc 30850862522181920279), (Int.ofNat 18759282548886840600), (Int.negSucc 78730834881053895119), (Int.ofNat 22812154046303389920), (Int.negSucc 15170121993424982399), (Int.negSucc 15798956049473034239), (Int.negSucc 2139341513107714559)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3548228750677440), (Int.ofNat 993105919176294240), (Int.ofNat 8886451931334736380), (Int.negSucc 9848245815145104479), (Int.ofNat 13718604945746946240), (Int.negSucc 2906005462797795839), (Int.negSucc 849366815312809439), (Int.ofNat 1239200306295275520), (Int.ofNat 305789595834839040)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 33954681952408319), (Int.negSucc 1297756068657770879), (Int.ofNat 1555357715998497360), (Int.negSucc 1095378567999703199), (Int.ofNat 85084771537336320), (Int.ofNat 197558273489564160)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 81232109560938240), (Int.negSucc 101823433061005439), (Int.ofNat 31908599863922160)]]

theorem h4n211_arithmetic_row0 :
    (BiPoly.mul h4p210 h4p11).getD 0 []=h4p211.getD 0 [] := by
  decide +kernel

theorem h4n211_arithmetic_row1 :
    (BiPoly.mul h4p210 h4p11).getD 1 []=h4p211.getD 1 [] := by
  decide +kernel

theorem h4n211_arithmetic_row2 :
    (BiPoly.mul h4p210 h4p11).getD 2 []=h4p211.getD 2 [] := by
  decide +kernel

theorem h4n211_arithmetic_row3 :
    (BiPoly.mul h4p210 h4p11).getD 3 []=h4p211.getD 3 [] := by
  decide +kernel

theorem h4n211_arithmetic_row4 :
    (BiPoly.mul h4p210 h4p11).getD 4 []=h4p211.getD 4 [] := by
  decide +kernel

theorem h4n211_arithmetic_row5 :
    (BiPoly.mul h4p210 h4p11).getD 5 []=h4p211.getD 5 [] := by
  decide +kernel

theorem h4n211_arithmetic_row6 :
    (BiPoly.mul h4p210 h4p11).getD 6 []=h4p211.getD 6 [] := by
  decide +kernel

theorem h4n211_arithmetic_row7 :
    (BiPoly.mul h4p210 h4p11).getD 7 []=h4p211.getD 7 [] := by
  decide +kernel

theorem h4n211_arithmetic_row8 :
    (BiPoly.mul h4p210 h4p11).getD 8 []=h4p211.getD 8 [] := by
  decide +kernel

theorem h4n211_arithmetic_row9 :
    (BiPoly.mul h4p210 h4p11).getD 9 []=h4p211.getD 9 [] := by
  decide +kernel

theorem h4n211_arithmetic_row10 :
    (BiPoly.mul h4p210 h4p11).getD 10 []=h4p211.getD 10 [] := by
  decide +kernel

theorem h4n211_arithmetic_row11 :
    (BiPoly.mul h4p210 h4p11).getD 11 []=h4p211.getD 11 [] := by
  decide +kernel

theorem h4n211_arithmetic_row12 :
    (BiPoly.mul h4p210 h4p11).getD 12 []=h4p211.getD 12 [] := by
  decide +kernel

theorem h4n211_arithmetic_row13 :
    (BiPoly.mul h4p210 h4p11).getD 13 []=h4p211.getD 13 [] := by
  decide +kernel

theorem h4n211_arithmetic_row14 :
    (BiPoly.mul h4p210 h4p11).getD 14 []=h4p211.getD 14 [] := by
  decide +kernel

theorem h4n211_arithmetic_row15 :
    (BiPoly.mul h4p210 h4p11).getD 15 []=h4p211.getD 15 [] := by
  decide +kernel

theorem h4n211_arithmetic_row16 :
    (BiPoly.mul h4p210 h4p11).getD 16 []=h4p211.getD 16 [] := by
  decide +kernel

theorem h4n211_arithmetic_row17 :
    (BiPoly.mul h4p210 h4p11).getD 17 []=h4p211.getD 17 [] := by
  decide +kernel

theorem h4n211_arithmetic_row18 :
    (BiPoly.mul h4p210 h4p11).getD 18 []=h4p211.getD 18 [] := by
  decide +kernel

theorem h4n211_arithmetic : BiPoly.mul h4p210 h4p11=h4p211 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h4p210 h4p11).getD j.val []=h4p211.getD j.val [] :=
      (fun j => Fin.cases h4n211_arithmetic_row0 (fun j => Fin.cases h4n211_arithmetic_row1 (fun j => Fin.cases h4n211_arithmetic_row2 (fun j => Fin.cases h4n211_arithmetic_row3 (fun j => Fin.cases h4n211_arithmetic_row4 (fun j => Fin.cases h4n211_arithmetic_row5 (fun j => Fin.cases h4n211_arithmetic_row6 (fun j => Fin.cases h4n211_arithmetic_row7 (fun j => Fin.cases h4n211_arithmetic_row8 (fun j => Fin.cases h4n211_arithmetic_row9 (fun j => Fin.cases h4n211_arithmetic_row10 (fun j => Fin.cases h4n211_arithmetic_row11 (fun j => Fin.cases h4n211_arithmetic_row12 (fun j => Fin.cases h4n211_arithmetic_row13 (fun j => Fin.cases h4n211_arithmetic_row14 (fun j => Fin.cases h4n211_arithmetic_row15 (fun j => Fin.cases h4n211_arithmetic_row16 (fun j => Fin.cases h4n211_arithmetic_row17 (fun j => Fin.cases h4n211_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n211 : h4e211.toBi mapPolyEnv=h4p211 := by
  change BiPoly.mul (h4e210.toBi mapPolyEnv) (h4e11.toBi mapPolyEnv)=h4p211
  rw [h4n210, h4n11]
  exact h4n211_arithmetic

#print axioms h4n211_arithmetic
end StackSorting.RationalLift
