import BivariateRowEquality
import Horner1Base
import Horner1Node030
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p31 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 61762419647), (Int.negSucc 518957411543), (Int.ofNat 2039469319008), (Int.ofNat 5035770838512), (Int.ofNat 798920057952), (Int.negSucc 3127382583767), (Int.negSucc 1387196114111)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 649057230144), (Int.ofNat 4933329941844), (Int.negSucc 23771209129811), (Int.negSucc 43589860951175), (Int.negSucc 774233359415), (Int.ofNat 21498350752404), (Int.ofNat 6918026720652), (Int.ofNat 179821718496)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3107992794047), (Int.negSucc 21261480037253), (Int.ofNat 122309714263428), (Int.ofNat 171277985024514), (Int.ofNat 2166734332872), (Int.negSucc 54323048572001), (Int.negSucc 24740709623387), (Int.negSucc 5807538492857), (Int.ofNat 476194550832)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 8955817333848), (Int.ofNat 54861731473023), (Int.negSucc 369894479964092), (Int.negSucc 422620364676500), (Int.negSucc 80641112095304), (Int.ofNat 63467874366669), (Int.ofNat 80956309900401), (Int.ofNat 20610291357873), (Int.negSucc 1362697235090), (Int.ofNat 11919399624)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 17261467737683), (Int.negSucc 94186051206908), (Int.ofNat 735283848954636), (Int.ofNat 787502508642387), (Int.ofNat 406322213236038), (Int.negSucc 24882042592034), (Int.negSucc 154105479250583), (Int.negSucc 41322007820822), (Int.negSucc 7290234220085), (Int.ofNat 1098198072876), (Int.negSucc 46902352991)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 23363541744386), (Int.ofNat 112798087794251), (Int.negSucc 1014674210304910), (Int.negSucc 1250424566942795), (Int.negSucc 997006803075725), (Int.negSucc 101342526460118), (Int.ofNat 120631583430221), (Int.ofNat 92086404301274), (Int.ofNat 25059240598390), (Int.negSucc 2987326714221), (Int.ofNat 182553433700), (Int.negSucc 7106417119)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 22624197748357), (Int.negSucc 95463873226904), (Int.ofNat 998903326174644), (Int.ofNat 1720571922293904), (Int.ofNat 1545498144649134), (Int.ofNat 460610010692877), (Int.ofNat 40811345919724), (Int.negSucc 148244280616751), (Int.negSucc 29906897075783), (Int.negSucc 4851224934787), (Int.ofNat 671057357532), (Int.negSucc 15786640319)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 15579193159512), (Int.ofNat 55482806898654), (Int.negSucc 709847508793835), (Int.negSucc 1928419853771372), (Int.negSucc 1767845153798522), (Int.negSucc 1019669209141091), (Int.negSucc 198442282420559), (Int.ofNat 77899376773008), (Int.ofNat 41672046711402), (Int.ofNat 16636337209431), (Int.negSucc 1876241619734), (Int.ofNat 83446333704)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 7318022963727), (Int.negSucc 19035176171433), (Int.ofNat 366595354555306), (Int.ofNat 1649161181798201), (Int.ofNat 1694244387672398), (Int.ofNat 1360282016592100), (Int.ofNat 361238573278114), (Int.ofNat 93467732885266), (Int.negSucc 60800366531151), (Int.negSucc 10927437947068), (Int.negSucc 1883758174879), (Int.ofNat 147444671816)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2038159032604), (Int.ofNat 102001925394), (Int.negSucc 141489963283457), (Int.negSucc 1030561329668611), (Int.negSucc 1424211339732761), (Int.negSucc 1219401145762415), (Int.negSucc 559112819507757), (Int.negSucc 174649212527309), (Int.ofNat 16994113435326), (Int.ofNat 5524542218741), (Int.ofNat 5362956291651), (Int.negSucc 351260183303)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 111428385347), (Int.ofNat 4311114194088), (Int.ofNat 46103500670412), (Int.ofNat 456228353074770), (Int.ofNat 985238740417416), (Int.ofNat 838650667434990), (Int.ofNat 603554205228258), (Int.ofNat 165637138400310), (Int.ofNat 55617989908302), (Int.negSucc 9345866450066), (Int.negSucc 1520351319509), (Int.negSucc 353195641475)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 153774654975), (Int.negSucc 2889686217708), (Int.negSucc 16160749059076), (Int.negSucc 139790248314766), (Int.negSucc 507662313833614), (Int.negSucc 507969723380952), (Int.negSucc 422152955962298), (Int.negSucc 161859959488736), (Int.negSucc 64280998982762), (Int.negSucc 1046795909327), (Int.negSucc 920449563137), (Int.ofNat 588929441976)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 63161691316), (Int.ofNat 1090698998415), (Int.ofNat 6192432562608), (Int.ofNat 30407513066765), (Int.ofNat 178790341180290), (Int.ofNat 271468205280999), (Int.ofNat 206957535101550), (Int.ofNat 133810602278661), (Int.ofNat 36608319418590), (Int.ofNat 12895926388344), (Int.ofNat 15499953072), (Int.ofNat 9187736472)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 11058969869), (Int.negSucc 258073075088), (Int.negSucc 1951251965882), (Int.negSucc 5944030664363), (Int.negSucc 39619039509629), (Int.negSucc 110136707809064), (Int.negSucc 87000871178510), (Int.negSucc 70120143676475), (Int.negSucc 22099703366429), (Int.negSucc 9436578612227), (Int.negSucc 567435809915), (Int.negSucc 193136070815)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 775481850), (Int.ofNat 35738684775), (Int.ofNat 407696520492), (Int.ofNat 1438877096316), (Int.ofNat 5141220007122), (Int.ofNat 28619504402139), (Int.ofNat 34720037479998), (Int.ofNat 23190536524644), (Int.ofNat 13287422937096), (Int.ofNat 3176977072932), (Int.ofNat 947359893960), (Int.ofNat 66544445808)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2212563599), (Int.negSucc 48408594353), (Int.negSucc 307906076654), (Int.negSucc 533109072932), (Int.negSucc 3929139224351), (Int.negSucc 10504560808061), (Int.negSucc 6382456448543), (Int.negSucc 4789741231799), (Int.negSucc 1089959296895), (Int.negSucc 409268362391), (Int.negSucc 8283609503)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2438074890), (Int.ofNat 35342229015), (Int.ofNat 106727725602), (Int.ofNat 189678406968), (Int.ofNat 1759744069344), (Int.ofNat 1850294187072), (Int.ofNat 934570262880), (Int.ofNat 425095599744), (Int.ofNat 67229243136), (Int.ofNat 351949536)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1292998139), (Int.negSucc 14654583017), (Int.negSucc 8597926115), (Int.negSucc 96646489739), (Int.negSucc 376353271727), (Int.negSucc 147509837423), (Int.negSucc 89058209183), (Int.negSucc 3772347551)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 329782104), (Int.ofNat 3247960356), (Int.negSucc 3538933415), (Int.ofNat 28914064560), (Int.ofNat 29484119232), (Int.ofNat 6488846496)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 32437583), (Int.negSucc 297729431), (Int.ofNat 628456320), (Int.negSucc 3068448479)]]

theorem h1n31_arithmetic_row0 :
    (BiPoly.mul h1p2 h1p30).getD 0 []=h1p31.getD 0 [] := by
  decide +kernel

theorem h1n31_arithmetic_row1 :
    (BiPoly.mul h1p2 h1p30).getD 1 []=h1p31.getD 1 [] := by
  decide +kernel

theorem h1n31_arithmetic_row2 :
    (BiPoly.mul h1p2 h1p30).getD 2 []=h1p31.getD 2 [] := by
  decide +kernel

theorem h1n31_arithmetic_row3 :
    (BiPoly.mul h1p2 h1p30).getD 3 []=h1p31.getD 3 [] := by
  decide +kernel

theorem h1n31_arithmetic_row4 :
    (BiPoly.mul h1p2 h1p30).getD 4 []=h1p31.getD 4 [] := by
  decide +kernel

theorem h1n31_arithmetic_row5 :
    (BiPoly.mul h1p2 h1p30).getD 5 []=h1p31.getD 5 [] := by
  decide +kernel

theorem h1n31_arithmetic_row6 :
    (BiPoly.mul h1p2 h1p30).getD 6 []=h1p31.getD 6 [] := by
  decide +kernel

theorem h1n31_arithmetic_row7 :
    (BiPoly.mul h1p2 h1p30).getD 7 []=h1p31.getD 7 [] := by
  decide +kernel

theorem h1n31_arithmetic_row8 :
    (BiPoly.mul h1p2 h1p30).getD 8 []=h1p31.getD 8 [] := by
  decide +kernel

theorem h1n31_arithmetic_row9 :
    (BiPoly.mul h1p2 h1p30).getD 9 []=h1p31.getD 9 [] := by
  decide +kernel

theorem h1n31_arithmetic_row10 :
    (BiPoly.mul h1p2 h1p30).getD 10 []=h1p31.getD 10 [] := by
  decide +kernel

theorem h1n31_arithmetic_row11 :
    (BiPoly.mul h1p2 h1p30).getD 11 []=h1p31.getD 11 [] := by
  decide +kernel

theorem h1n31_arithmetic_row12 :
    (BiPoly.mul h1p2 h1p30).getD 12 []=h1p31.getD 12 [] := by
  decide +kernel

theorem h1n31_arithmetic_row13 :
    (BiPoly.mul h1p2 h1p30).getD 13 []=h1p31.getD 13 [] := by
  decide +kernel

theorem h1n31_arithmetic_row14 :
    (BiPoly.mul h1p2 h1p30).getD 14 []=h1p31.getD 14 [] := by
  decide +kernel

theorem h1n31_arithmetic_row15 :
    (BiPoly.mul h1p2 h1p30).getD 15 []=h1p31.getD 15 [] := by
  decide +kernel

theorem h1n31_arithmetic_row16 :
    (BiPoly.mul h1p2 h1p30).getD 16 []=h1p31.getD 16 [] := by
  decide +kernel

theorem h1n31_arithmetic_row17 :
    (BiPoly.mul h1p2 h1p30).getD 17 []=h1p31.getD 17 [] := by
  decide +kernel

theorem h1n31_arithmetic_row18 :
    (BiPoly.mul h1p2 h1p30).getD 18 []=h1p31.getD 18 [] := by
  decide +kernel

theorem h1n31_arithmetic_row19 :
    (BiPoly.mul h1p2 h1p30).getD 19 []=h1p31.getD 19 [] := by
  decide +kernel

theorem h1n31_arithmetic : BiPoly.mul h1p2 h1p30=h1p31 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<20 at hk
    have hf : ∀ j : Fin 20, (BiPoly.mul h1p2 h1p30).getD j.val []=h1p31.getD j.val [] :=
      (fun j => Fin.cases h1n31_arithmetic_row0 (fun j => Fin.cases h1n31_arithmetic_row1 (fun j => Fin.cases h1n31_arithmetic_row2 (fun j => Fin.cases h1n31_arithmetic_row3 (fun j => Fin.cases h1n31_arithmetic_row4 (fun j => Fin.cases h1n31_arithmetic_row5 (fun j => Fin.cases h1n31_arithmetic_row6 (fun j => Fin.cases h1n31_arithmetic_row7 (fun j => Fin.cases h1n31_arithmetic_row8 (fun j => Fin.cases h1n31_arithmetic_row9 (fun j => Fin.cases h1n31_arithmetic_row10 (fun j => Fin.cases h1n31_arithmetic_row11 (fun j => Fin.cases h1n31_arithmetic_row12 (fun j => Fin.cases h1n31_arithmetic_row13 (fun j => Fin.cases h1n31_arithmetic_row14 (fun j => Fin.cases h1n31_arithmetic_row15 (fun j => Fin.cases h1n31_arithmetic_row16 (fun j => Fin.cases h1n31_arithmetic_row17 (fun j => Fin.cases h1n31_arithmetic_row18 (fun j => Fin.cases h1n31_arithmetic_row19 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n31 : h1e31.toBi mapPolyEnv=h1p31 := by
  change BiPoly.mul (h1e2.toBi mapPolyEnv) (h1e30.toBi mapPolyEnv)=h1p31
  rw [h1n2, h1n30]
  exact h1n31_arithmetic

#print axioms h1n31_arithmetic
end StackSorting.RationalLift
