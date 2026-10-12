import BivariateRowEquality
import Horner1Node020
import Horner1Node105
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p106 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 169329857183999), (Int.negSucc 893630599568927), (Int.negSucc 800695528797311), (Int.ofNat 659388656635200), (Int.ofNat 992990787306624), (Int.ofNat 257207344259040)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1871910213788160), (Int.ofNat 9172096528688640), (Int.ofNat 6412377825939168), (Int.negSucc 6841501812941759), (Int.negSucc 7828876012913279), (Int.negSucc 1909535951753279), (Int.negSucc 34353262820447)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 9533085137942399), (Int.negSucc 43955662023751751), (Int.negSucc 25592379066570959), (Int.ofNat 27171055267249608), (Int.ofNat 29316463401315744), (Int.ofNat 10126013787939528), (Int.ofNat 1061387529972912), (Int.negSucc 88239080922695)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 29631510457119360), (Int.ofNat 131212525703258088), (Int.ofNat 73922311465840224), (Int.negSucc 52390547640090359), (Int.negSucc 74782100137974335), (Int.negSucc 38255151275123399), (Int.negSucc 5986068962762591), (Int.ofNat 435307208557464), (Int.negSucc 1831634716031)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 62774025197795279), (Int.negSucc 274641824199925943), (Int.negSucc 180557726388021863), (Int.ofNat 35444250267650928), (Int.ofNat 143896631910501240), (Int.ofNat 94369375069247592), (Int.ofNat 22121979469377768), (Int.ofNat 426523012433280), (Int.negSucc 202477637031911), (Int.ofNat 8722700496576)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 95838833753259840), (Int.ofNat 429686053298027940), (Int.ofNat 374413733411441772), (Int.ofNat 75039566124586764), (Int.negSucc 192560537551950851), (Int.negSucc 161104120792926899), (Int.negSucc 60571241334643739), (Int.negSucc 6259552527114731), (Int.ofNat 973433367106260), (Int.negSucc 50681063381519), (Int.ofNat 1279205402112)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 108694575001501199), (Int.negSucc 521492824347400483), (Int.negSucc 626946036833366799), (Int.negSucc 280380187989574091), (Int.ofNat 130370378311431072), (Int.ofNat 204732207984616140), (Int.ofNat 112037981089297536), (Int.ofNat 21727818155031892), (Int.negSucc 792721318172079), (Int.negSucc 62755926663839), (Int.ofNat 1794117285664), (Int.negSucc 6592389759)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 92988556516200960), (Int.ofNat 500620331898822136), (Int.ofNat 821992993976347036), (Int.ofNat 525540212249557496), (Int.ofNat 75622213429463360), (Int.negSucc 182748693322689891), (Int.negSucc 137256841917571347), (Int.negSucc 47481140348037527), (Int.negSucc 3246309396223031), (Int.ofNat 590474899297132), (Int.negSucc 24408807644847), (Int.ofNat 236210330048)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 60276072344076959), (Int.negSucc 382300939354858927), (Int.negSucc 837330594042675763), (Int.negSucc 719860119871657051), (Int.negSucc 325312565799820123), (Int.ofNat 59183280174138040), (Int.ofNat 113640251581725604), (Int.ofNat 65586277078342436), (Int.ofNat 11715605796601268), (Int.negSucc 568239110247063), (Int.negSucc 10727868778247), (Int.ofNat 577370705472)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 29449771240222080), (Int.ofNat 230942390042310456), (Int.ofNat 663101177003143448), (Int.ofNat 768441286195221360), (Int.ofNat 483410667192069172), (Int.ofNat 125292005320338860), (Int.negSucc 52570817944417199), (Int.negSucc 52887823336306483), (Int.negSucc 20326305629178487), (Int.negSucc 1069601722558583), (Int.ofNat 149117622714508), (Int.negSucc 3010451143711)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 10672683760887839), (Int.negSucc 108688032056135551), (Int.negSucc 407862601387434175), (Int.negSucc 640918216679178447), (Int.negSucc 500687003236065635), (Int.negSucc 254599744529074127), (Int.negSucc 27247394524704559), (Int.ofNat 19064406919582620), (Int.ofNat 19540001839615356), (Int.ofNat 3376439728073636), (Int.negSucc 71178043249495), (Int.negSucc 4991306894023)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2781431795706240), (Int.ofNat 38876012336845384), (Int.ofNat 193414254367972120), (Int.ofNat 412843653924631960), (Int.ofNat 407982633920868128), (Int.ofNat 264801547487166152), (Int.ofNat 92447632507546064), (Int.ofNat 9468324073463644), (Int.negSucc 7224057222730519), (Int.negSucc 4270870456303435), (Int.negSucc 259662616625123), (Int.ofNat 14217238682124)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 492723786710159), (Int.negSucc 10183055664873863), (Int.negSucc 69550959346907967), (Int.negSucc 202330567132560983), (Int.negSucc 264979136596852399), (Int.negSucc 197234693390570695), (Int.negSucc 106743361603762583), (Int.negSucc 25128868501938091), (Int.negSucc 4425397047393899), (Int.ofNat 2425452867674664), (Int.ofNat 409792849278676), (Int.ofNat 11297879758872)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 53109538747200), (Int.ofNat 1843105520175940), (Int.ofNat 18435519277238428), (Int.ofNat 74042786419697804), (Int.ofNat 133226573151974500), (Int.ofNat 117748808343315388), (Int.ofNat 76871550860237436), (Int.ofNat 28995471417299880), (Int.ofNat 7422700896200532), (Int.ofNat 503753466025764), (Int.negSucc 262978246657295), (Int.negSucc 28048436024327)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2628428945999), (Int.negSucc 208125227931571), (Int.negSucc 3444859449264895), (Int.negSucc 19733393745362011), (Int.negSucc 49758405923432855), (Int.negSucc 57428676207284171), (Int.negSucc 40024203654204959), (Int.negSucc 21708965167694567), (Int.negSucc 5826411673294283), (Int.negSucc 1683820997465111), (Int.ofNat 12137289284592), (Int.ofNat 2745371070432)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 11708108467640), (Int.ofNat 422560630621164), (Int.ofNat 3707152893554184), (Int.ofNat 13216680138874624), (Int.ofNat 21645605650858524), (Int.ofNat 16885557500879700), (Int.ofNat 10732111309500804), (Int.ofNat 3771420143654880), (Int.ofNat 1132717760353224), (Int.ofNat 138718557030960), (Int.ofNat 14265523934640)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 129962149199), (Int.negSucc 29997662844419), (Int.negSucc 471573874075643), (Int.negSucc 2391273360468971), (Int.negSucc 5768927374458887), (Int.negSucc 5995952447147891), (Int.negSucc 3700433020181687), (Int.negSucc 1882667965677695), (Int.negSucc 455005514593727), (Int.negSucc 119649755127023), (Int.negSucc 7979943819167)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 921747340800), (Int.ofNat 38436755349528), (Int.ofNat 286980534862956), (Int.ofNat 986570692815420), (Int.ofNat 1615048472047248), (Int.ofNat 1033111286276616), (Int.ofNat 609307294008672), (Int.ofNat 160964777162016), (Int.ofNat 44446245013440), (Int.ofNat 1495578212064)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1680008694479), (Int.negSucc 23569499094083), (Int.negSucc 99103155790823), (Int.negSucc 272866366773935), (Int.negSucc 256147044405983), (Int.negSucc 122633119588319), (Int.negSucc 49779670319423), (Int.negSucc 7531293214655), (Int.negSucc 92521087487)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1255339905120), (Int.ofNat 6431496787224), (Int.ofNat 22236485434416), (Int.ofNat 45093153380976), (Int.ofNat 19357052366016), (Int.ofNat 9163079489664), (Int.ofNat 468450781056)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 407351809727), (Int.negSucc 582955604207), (Int.negSucc 3524992859807), (Int.negSucc 3114433986623), (Int.negSucc 659338299647)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 47686257792), (Int.negSucc 12930500447), (Int.ofNat 283408606080)]]

theorem h1n106_arithmetic_row0 :
    (BiPoly.mul h1p20 h1p105).getD 0 []=h1p106.getD 0 [] := by
  decide +kernel

theorem h1n106_arithmetic_row1 :
    (BiPoly.mul h1p20 h1p105).getD 1 []=h1p106.getD 1 [] := by
  decide +kernel

theorem h1n106_arithmetic_row2 :
    (BiPoly.mul h1p20 h1p105).getD 2 []=h1p106.getD 2 [] := by
  decide +kernel

theorem h1n106_arithmetic_row3 :
    (BiPoly.mul h1p20 h1p105).getD 3 []=h1p106.getD 3 [] := by
  decide +kernel

theorem h1n106_arithmetic_row4 :
    (BiPoly.mul h1p20 h1p105).getD 4 []=h1p106.getD 4 [] := by
  decide +kernel

theorem h1n106_arithmetic_row5 :
    (BiPoly.mul h1p20 h1p105).getD 5 []=h1p106.getD 5 [] := by
  decide +kernel

theorem h1n106_arithmetic_row6 :
    (BiPoly.mul h1p20 h1p105).getD 6 []=h1p106.getD 6 [] := by
  decide +kernel

theorem h1n106_arithmetic_row7 :
    (BiPoly.mul h1p20 h1p105).getD 7 []=h1p106.getD 7 [] := by
  decide +kernel

theorem h1n106_arithmetic_row8 :
    (BiPoly.mul h1p20 h1p105).getD 8 []=h1p106.getD 8 [] := by
  decide +kernel

theorem h1n106_arithmetic_row9 :
    (BiPoly.mul h1p20 h1p105).getD 9 []=h1p106.getD 9 [] := by
  decide +kernel

theorem h1n106_arithmetic_row10 :
    (BiPoly.mul h1p20 h1p105).getD 10 []=h1p106.getD 10 [] := by
  decide +kernel

theorem h1n106_arithmetic_row11 :
    (BiPoly.mul h1p20 h1p105).getD 11 []=h1p106.getD 11 [] := by
  decide +kernel

theorem h1n106_arithmetic_row12 :
    (BiPoly.mul h1p20 h1p105).getD 12 []=h1p106.getD 12 [] := by
  decide +kernel

theorem h1n106_arithmetic_row13 :
    (BiPoly.mul h1p20 h1p105).getD 13 []=h1p106.getD 13 [] := by
  decide +kernel

theorem h1n106_arithmetic_row14 :
    (BiPoly.mul h1p20 h1p105).getD 14 []=h1p106.getD 14 [] := by
  decide +kernel

theorem h1n106_arithmetic_row15 :
    (BiPoly.mul h1p20 h1p105).getD 15 []=h1p106.getD 15 [] := by
  decide +kernel

theorem h1n106_arithmetic_row16 :
    (BiPoly.mul h1p20 h1p105).getD 16 []=h1p106.getD 16 [] := by
  decide +kernel

theorem h1n106_arithmetic_row17 :
    (BiPoly.mul h1p20 h1p105).getD 17 []=h1p106.getD 17 [] := by
  decide +kernel

theorem h1n106_arithmetic_row18 :
    (BiPoly.mul h1p20 h1p105).getD 18 []=h1p106.getD 18 [] := by
  decide +kernel

theorem h1n106_arithmetic_row19 :
    (BiPoly.mul h1p20 h1p105).getD 19 []=h1p106.getD 19 [] := by
  decide +kernel

theorem h1n106_arithmetic_row20 :
    (BiPoly.mul h1p20 h1p105).getD 20 []=h1p106.getD 20 [] := by
  decide +kernel

theorem h1n106_arithmetic_row21 :
    (BiPoly.mul h1p20 h1p105).getD 21 []=h1p106.getD 21 [] := by
  decide +kernel

theorem h1n106_arithmetic : BiPoly.mul h1p20 h1p105=h1p106 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<22 at hk
    have hf : ∀ j : Fin 22, (BiPoly.mul h1p20 h1p105).getD j.val []=h1p106.getD j.val [] :=
      (fun j => Fin.cases h1n106_arithmetic_row0 (fun j => Fin.cases h1n106_arithmetic_row1 (fun j => Fin.cases h1n106_arithmetic_row2 (fun j => Fin.cases h1n106_arithmetic_row3 (fun j => Fin.cases h1n106_arithmetic_row4 (fun j => Fin.cases h1n106_arithmetic_row5 (fun j => Fin.cases h1n106_arithmetic_row6 (fun j => Fin.cases h1n106_arithmetic_row7 (fun j => Fin.cases h1n106_arithmetic_row8 (fun j => Fin.cases h1n106_arithmetic_row9 (fun j => Fin.cases h1n106_arithmetic_row10 (fun j => Fin.cases h1n106_arithmetic_row11 (fun j => Fin.cases h1n106_arithmetic_row12 (fun j => Fin.cases h1n106_arithmetic_row13 (fun j => Fin.cases h1n106_arithmetic_row14 (fun j => Fin.cases h1n106_arithmetic_row15 (fun j => Fin.cases h1n106_arithmetic_row16 (fun j => Fin.cases h1n106_arithmetic_row17 (fun j => Fin.cases h1n106_arithmetic_row18 (fun j => Fin.cases h1n106_arithmetic_row19 (fun j => Fin.cases h1n106_arithmetic_row20 (fun j => Fin.cases h1n106_arithmetic_row21 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n106 : h1e106.toBi mapPolyEnv=h1p106 := by
  change BiPoly.mul (h1e20.toBi mapPolyEnv) (h1e105.toBi mapPolyEnv)=h1p106
  rw [h1n20, h1n105]
  exact h1n106_arithmetic

#print axioms h1n106_arithmetic
end StackSorting.RationalLift
