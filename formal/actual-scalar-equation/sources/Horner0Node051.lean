import BivariateRowEquality
import Horner0Base
import Horner0Node050
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p51 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 123407322402877704000), (Int.ofNat 1056573055400784294240), (Int.ofNat 2172906937284168761280), (Int.negSucc 2075891159424444338879), (Int.negSucc 7122444541944054782399), (Int.ofNat 778405143358459674720), (Int.ofNat 4585217321591807947200)], [(Int.ofNat 0), (Int.negSucc 1553259725074453188959), (Int.negSucc 13161637195281781347311), (Int.negSucc 26615534509051355533967), (Int.ofNat 24813446844541785010560), (Int.ofNat 79072336081552023021888), (Int.negSucc 15928632899287431858863), (Int.negSucc 44360518622702018968655), (Int.ofNat 2387464890353934458400)], [(Int.ofNat 0), (Int.ofNat 9287280611212249185840), (Int.ofNat 77108322926989372781448), (Int.ofNat 152779885533305751512808), (Int.negSucc 133807804231189930639775), (Int.negSucc 408136579300493505842111), (Int.ofNat 97575307056425108760264), (Int.ofNat 184547673408757234161384), (Int.negSucc 2838334161018147901487), (Int.negSucc 520548043110221734847)], [(Int.ofNat 0), (Int.negSucc 35059945119445198486439), (Int.negSucc 282071643968826489006899), (Int.negSucc 548569808309888589883319), (Int.ofNat 411935158882020062849436), (Int.ofNat 1289766535136721079494192), (Int.negSucc 258901771319809664530715), (Int.negSucc 431621805165068075765687), (Int.negSucc 83040338516538220215371), (Int.ofNat 13219903718962938613224), (Int.negSucc 552491575820638451711)], [(Int.ofNat 0), (Int.ofNat 93577318522518758134320), (Int.ofNat 722048827801396894473240), (Int.ofNat 1390773726371133987766416), (Int.negSucc 734356316183782672369367), (Int.negSucc 2775432657919988558906351), (Int.ofNat 144235834033300528245624), (Int.ofNat 623522642721381814840992), (Int.ofNat 457727335581074760100584), (Int.negSucc 58420088097909749355887), (Int.ofNat 3682746773424297808128), (Int.negSucc 117712288619980471295)], [(Int.ofNat 0), (Int.negSucc 187225914229732090386719), (Int.negSucc 1375337155968167901091055), (Int.negSucc 2670156460346617172374955), (Int.ofNat 518136913235626243701732), (Int.ofNat 4252859520640517000711196), (Int.ofNat 1088881080670366359236640), (Int.negSucc 554522958793241525074355), (Int.negSucc 1098715643516176394381531), (Int.ofNat 43866277003382064251220), (Int.ofNat 1703667012924964601880), (Int.ofNat 56884139712951329088), (Int.negSucc 7706663095872508415)], [(Int.ofNat 0), (Int.ofNat 290311917554410246967220), (Int.ofNat 2026493732272084981749846), (Int.ofNat 4069816692648837227428554), (Int.ofNat 953357587299316105354962), (Int.negSucc 4569048881080380946911725), (Int.negSucc 3781839965260317049203641), (Int.ofNat 77620567289143454960022), (Int.ofNat 1343441679471719247142998), (Int.ofNat 312496038715084506785538), (Int.negSucc 47700361355043413520395), (Int.ofNat 2530840884760922066928), (Int.negSucc 46669913322804972287), (Int.ofNat 41405582288378880)], [(Int.ofNat 0), (Int.negSucc 355659636812637594355919), (Int.negSucc 2374091305833495640624235), (Int.negSucc 5091504337697748249570389), (Int.negSucc 3591629954104807704298895), (Int.ofNat 2833141972407359355753570), (Int.ofNat 6463263706040020389338484), (Int.ofNat 1105179927182917174672038), (Int.negSucc 540314195684939953420643), (Int.negSucc 994635829544322886636985), (Int.ofNat 81689941923853054493916), (Int.negSucc 2872592356431541228559), (Int.ofNat 96152675064924849120), (Int.negSucc 1343513138846845823)], [(Int.ofNat 0), (Int.ofNat 347830563299873505663300), (Int.ofNat 2258318487563374714292802), (Int.ofNat 5344227801191490731116158), (Int.ofNat 6142528851153368981041626), (Int.ofNat 687405364695053366170284), (Int.negSucc 6625165532068754214799211), (Int.negSucc 3065124468181576673871317), (Int.negSucc 834165989998433700482237), (Int.ofNat 1192838305669857999068052), (Int.ofNat 91820164197712910453166), (Int.negSucc 16016466846038599800203), (Int.ofNat 652838088762612207120), (Int.negSucc 8592689572294259135)], [(Int.ofNat 0), (Int.negSucc 272648699301664373896199), (Int.negSucc 1772853789739744561395431), (Int.negSucc 4760897628135317475388601), (Int.negSucc 7200589727763705789705683), (Int.negSucc 4401296162580399466507703), (Int.ofNat 3436785161322449009822784), (Int.ofNat 4651495930826196682611678), (Int.ofNat 1746021288319887095592720), (Int.negSucc 278783722070242774117535), (Int.negSucc 445759727064883640049623), (Int.ofNat 32983831414720803912900), (Int.negSucc 761469636188238613175), (Int.ofNat 4943057235837322560)], [(Int.ofNat 0), (Int.ofNat 171105492396716873899080), (Int.ofNat 1161394313654723777004264), (Int.ofNat 3609004409192095212355362), (Int.ofNat 6452626428273555328303404), (Int.ofNat 6436895502344896857957480), (Int.ofNat 1102794744640667452235676), (Int.negSucc 4135764911028146448478409), (Int.negSucc 1960045654946222995600241), (Int.negSucc 938246079222242377769141), (Int.ofNat 497425964688187480844502), (Int.ofNat 19165629755678916444054), (Int.negSucc 3122081390009286066059), (Int.ofNat 84135769529199169248)], [(Int.ofNat 0), (Int.negSucc 85467668923217556642599), (Int.negSucc 637567817483968854584891), (Int.negSucc 2318524357712050181563919), (Int.negSucc 4684718504308354590522605), (Int.negSucc 6138384044938731353596073), (Int.negSucc 4153490776000688051280173), (Int.ofNat 1484552134115560866001908), (Int.ofNat 1723268712341428386284490), (Int.ofNat 1255306388276858539357164), (Int.negSucc 25180445023431019421705), (Int.negSucc 108616969906011005219093), (Int.ofNat 4688008262250119531760), (Int.ofNat 6304881061760676456)], [(Int.ofNat 0), (Int.ofNat 33605056211602814351160), (Int.ofNat 292005420681376157493516), (Int.ofNat 1251166845006001034576484), (Int.ofNat 2861730212027327561242128), (Int.ofNat 4392609341926174130436504), (Int.ofNat 4576884997528294133734590), (Int.ofNat 1279871411407356862235682), (Int.negSucc 1000076810687378396645999), (Int.negSucc 749114858299501326918623), (Int.negSucc 429241408145139298772081), (Int.ofNat 93147084958577982212964), (Int.ofNat 4745067548934048055914), (Int.negSucc 321274071518227672523)], [(Int.ofNat 0), (Int.negSucc 10218543112359628098959), (Int.negSucc 110072551409991117566687), (Int.negSucc 559946840437351973339135), (Int.negSucc 1496586432647025172581851), (Int.negSucc 2521026889707371461481099), (Int.negSucc 3287313040327860193830413), (Int.negSucc 2393960992112206512361067), (Int.negSucc 30178631171372296670699), (Int.ofNat 216141048218309426998452), (Int.ofNat 397202787570979299492786), (Int.ofNat 27082149876372877865886), (Int.negSucc 12735067910167622708315), (Int.ofNat 47087702109687731616)], [(Int.ofNat 0), (Int.ofNat 2338542681761010387780), (Int.ofNat 33401333534235100575222), (Int.ofNat 204366384616628511898758), (Int.ofNat 665324571321272178132546), (Int.ofNat 1221852032167749388614798), (Int.ofNat 1757662160689883429745276), (Int.ofNat 1939839648411453440572188), (Int.ofNat 725915679759292333322304), (Int.ofNat 57449850949114421652480), (Int.negSucc 115183141271377471084601), (Int.negSucc 90930959999958714663455), (Int.ofNat 4525502102165231373936), (Int.ofNat 575608857031247229072)], [(Int.ofNat 0), (Int.negSucc 386015723963420820959), (Int.negSucc 7912365782301887092787), (Int.negSucc 59528265380376019656437), (Int.negSucc 244635908367636216692387), (Int.negSucc 515685112135126132293221), (Int.negSucc 753852448612535041424633), (Int.negSucc 1023088671460052203641989), (Int.negSucc 761891616993948773605073), (Int.negSucc 179177871776504971662125), (Int.negSucc 47560165755453050693615), (Int.ofNat 50139335699382090302028), (Int.ofNat 7241852945034624455172), (Int.negSucc 336552227011030503815)], [(Int.ofNat 0), (Int.ofNat 42822628632925035540), (Int.ofNat 1402854243390598678458), (Int.ofNat 13455116682635656799982), (Int.ofNat 71599628626804258154706), (Int.ofNat 187525240185955732126248), (Int.ofNat 279060017595765656890806), (Int.ofNat 388842586234396862606748), (Int.ofNat 442985412907239837035706), (Int.ofNat 191888190558966969418824), (Int.ofNat 63958685760467767298232), (Int.ofNat 2251144612234799158392), (Int.negSucc 7111565602692047790407), (Int.negSucc 326436342087668577263)], [(Int.ofNat 0), (Int.negSucc 2796022565129714279), (Int.negSucc 174747915884891498327), (Int.negSucc 2270847982700664834473), (Int.negSucc 15964135790586373004051), (Int.negSucc 55896519942951082238483), (Int.negSucc 93307932573037869306029), (Int.negSucc 116105470768764180273149), (Int.negSucc 165568309317153683475443), (Int.negSucc 122899206065098258084427), (Int.negSucc 41521234624064819991251), (Int.negSucc 15013536675723752171327), (Int.ofNat 1075990388781471590952), (Int.ofNat 361100827902302977392)], [(Int.ofNat 0), (Int.ofNat 77741528184262800), (Int.ofNat 13655632606008181956), (Int.ofNat 269857968336229013046), (Int.ofNat 2572893478741990791168), (Int.ofNat 12773063723144969813400), (Int.ofNat 27263981520728345752074), (Int.ofNat 30949359920854982245080), (Int.ofNat 41612230471459853737584), (Int.ofNat 49011307820677379947824), (Int.ofNat 21996201039250273825896), (Int.ofNat 8542329511232527452936), (Int.ofNat 1495196955498977004816), (Int.negSucc 37371453392812471487)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 506067915265317359), (Int.negSucc 20278982430838185803), (Int.negSucc 278230054087009866761), (Int.negSucc 2077436742537202040753), (Int.negSucc 6330626767597211683559), (Int.negSucc 8004729242886905575979), (Int.negSucc 7614450531496033464419), (Int.negSucc 11978696988307023008903), (Int.negSucc 8682504635812740712847), (Int.negSucc 3070662189854642906831), (Int.negSucc 992756994406995550895), (Int.negSucc 84452902849583568287)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 733345784009102160), (Int.ofNat 17693137724640803388), (Int.ofNat 217837694560706370180), (Int.ofNat 1049518389791027691288), (Int.ofNat 1820758540833154024488), (Int.ofNat 1311570010182585759336), (Int.ofNat 1666452232613619190656), (Int.ofNat 2173686380014259080512), (Int.ofNat 900144593058483844704), (Int.ofNat 298226918276815273920), (Int.ofNat 43669013038231935744)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 479669699231365391), (Int.negSucc 12225839284197316691), (Int.negSucc 109943594228546511227), (Int.negSucc 302831669821300806671), (Int.negSucc 261020255522803773335), (Int.negSucc 112683626553369617711), (Int.negSucc 290740768839477758015), (Int.negSucc 197208418570749379583), (Int.negSucc 57125856849735735071), (Int.negSucc 8383563950750697023)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 207725523351446880), (Int.ofNat 5818412693140146648), (Int.ofNat 31008264197834382984), (Int.ofNat 43697597657185778256), (Int.ofNat 6485483332449952128), (Int.ofNat 10442573944321366368), (Int.ofNat 25034162984979180768), (Int.ofNat 7776249730750997568), (Int.ofNat 562012869469731840)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 63071412998615999), (Int.negSucc 1505226542655630383), (Int.negSucc 4201324181643356207), (Int.negSucc 1706494668595210079), (Int.ofNat 1864214494528349088), (Int.negSucc 1271852757909802943), (Int.negSucc 562012869469731839)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 8665499079704448), (Int.ofNat 156733368276827232), (Int.ofNat 188031301828412832), (Int.negSucc 181546876812847679)]]

theorem h0n51_arithmetic_row0 :
    (BiPoly.mul h0p4 h0p50).getD 0 []=h0p51.getD 0 [] := by
  decide +kernel

theorem h0n51_arithmetic_row1 :
    (BiPoly.mul h0p4 h0p50).getD 1 []=h0p51.getD 1 [] := by
  decide +kernel

theorem h0n51_arithmetic_row2 :
    (BiPoly.mul h0p4 h0p50).getD 2 []=h0p51.getD 2 [] := by
  decide +kernel

theorem h0n51_arithmetic_row3 :
    (BiPoly.mul h0p4 h0p50).getD 3 []=h0p51.getD 3 [] := by
  decide +kernel

theorem h0n51_arithmetic_row4 :
    (BiPoly.mul h0p4 h0p50).getD 4 []=h0p51.getD 4 [] := by
  decide +kernel

theorem h0n51_arithmetic_row5 :
    (BiPoly.mul h0p4 h0p50).getD 5 []=h0p51.getD 5 [] := by
  decide +kernel

theorem h0n51_arithmetic_row6 :
    (BiPoly.mul h0p4 h0p50).getD 6 []=h0p51.getD 6 [] := by
  decide +kernel

theorem h0n51_arithmetic_row7 :
    (BiPoly.mul h0p4 h0p50).getD 7 []=h0p51.getD 7 [] := by
  decide +kernel

theorem h0n51_arithmetic_row8 :
    (BiPoly.mul h0p4 h0p50).getD 8 []=h0p51.getD 8 [] := by
  decide +kernel

theorem h0n51_arithmetic_row9 :
    (BiPoly.mul h0p4 h0p50).getD 9 []=h0p51.getD 9 [] := by
  decide +kernel

theorem h0n51_arithmetic_row10 :
    (BiPoly.mul h0p4 h0p50).getD 10 []=h0p51.getD 10 [] := by
  decide +kernel

theorem h0n51_arithmetic_row11 :
    (BiPoly.mul h0p4 h0p50).getD 11 []=h0p51.getD 11 [] := by
  decide +kernel

theorem h0n51_arithmetic_row12 :
    (BiPoly.mul h0p4 h0p50).getD 12 []=h0p51.getD 12 [] := by
  decide +kernel

theorem h0n51_arithmetic_row13 :
    (BiPoly.mul h0p4 h0p50).getD 13 []=h0p51.getD 13 [] := by
  decide +kernel

theorem h0n51_arithmetic_row14 :
    (BiPoly.mul h0p4 h0p50).getD 14 []=h0p51.getD 14 [] := by
  decide +kernel

theorem h0n51_arithmetic_row15 :
    (BiPoly.mul h0p4 h0p50).getD 15 []=h0p51.getD 15 [] := by
  decide +kernel

theorem h0n51_arithmetic_row16 :
    (BiPoly.mul h0p4 h0p50).getD 16 []=h0p51.getD 16 [] := by
  decide +kernel

theorem h0n51_arithmetic_row17 :
    (BiPoly.mul h0p4 h0p50).getD 17 []=h0p51.getD 17 [] := by
  decide +kernel

theorem h0n51_arithmetic_row18 :
    (BiPoly.mul h0p4 h0p50).getD 18 []=h0p51.getD 18 [] := by
  decide +kernel

theorem h0n51_arithmetic_row19 :
    (BiPoly.mul h0p4 h0p50).getD 19 []=h0p51.getD 19 [] := by
  decide +kernel

theorem h0n51_arithmetic_row20 :
    (BiPoly.mul h0p4 h0p50).getD 20 []=h0p51.getD 20 [] := by
  decide +kernel

theorem h0n51_arithmetic_row21 :
    (BiPoly.mul h0p4 h0p50).getD 21 []=h0p51.getD 21 [] := by
  decide +kernel

theorem h0n51_arithmetic_row22 :
    (BiPoly.mul h0p4 h0p50).getD 22 []=h0p51.getD 22 [] := by
  decide +kernel

theorem h0n51_arithmetic_row23 :
    (BiPoly.mul h0p4 h0p50).getD 23 []=h0p51.getD 23 [] := by
  decide +kernel

theorem h0n51_arithmetic_row24 :
    (BiPoly.mul h0p4 h0p50).getD 24 []=h0p51.getD 24 [] := by
  decide +kernel

theorem h0n51_arithmetic : BiPoly.mul h0p4 h0p50=h0p51 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<25 at hk
    have hf : ∀ j : Fin 25, (BiPoly.mul h0p4 h0p50).getD j.val []=h0p51.getD j.val [] :=
      (fun j => Fin.cases h0n51_arithmetic_row0 (fun j => Fin.cases h0n51_arithmetic_row1 (fun j => Fin.cases h0n51_arithmetic_row2 (fun j => Fin.cases h0n51_arithmetic_row3 (fun j => Fin.cases h0n51_arithmetic_row4 (fun j => Fin.cases h0n51_arithmetic_row5 (fun j => Fin.cases h0n51_arithmetic_row6 (fun j => Fin.cases h0n51_arithmetic_row7 (fun j => Fin.cases h0n51_arithmetic_row8 (fun j => Fin.cases h0n51_arithmetic_row9 (fun j => Fin.cases h0n51_arithmetic_row10 (fun j => Fin.cases h0n51_arithmetic_row11 (fun j => Fin.cases h0n51_arithmetic_row12 (fun j => Fin.cases h0n51_arithmetic_row13 (fun j => Fin.cases h0n51_arithmetic_row14 (fun j => Fin.cases h0n51_arithmetic_row15 (fun j => Fin.cases h0n51_arithmetic_row16 (fun j => Fin.cases h0n51_arithmetic_row17 (fun j => Fin.cases h0n51_arithmetic_row18 (fun j => Fin.cases h0n51_arithmetic_row19 (fun j => Fin.cases h0n51_arithmetic_row20 (fun j => Fin.cases h0n51_arithmetic_row21 (fun j => Fin.cases h0n51_arithmetic_row22 (fun j => Fin.cases h0n51_arithmetic_row23 (fun j => Fin.cases h0n51_arithmetic_row24 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n51 : h0e51.toBi mapPolyEnv=h0p51 := by
  change BiPoly.mul (h0e4.toBi mapPolyEnv) (h0e50.toBi mapPolyEnv)=h0p51
  rw [h0n4, h0n50]
  exact h0n51_arithmetic

#print axioms h0n51_arithmetic
end StackSorting.RationalLift
