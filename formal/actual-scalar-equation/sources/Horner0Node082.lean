import BivariateRowEquality
import Horner0Base
import Horner0Node057
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p82 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 438781590765787392000), (Int.ofNat 3125955660254747003520), (Int.ofNat 515654987497496210880), (Int.negSucc 27291900688550354350079), (Int.negSucc 5748009286451788794239), (Int.ofNat 82541197717756464447360), (Int.negSucc 52475264902661802062399)], [(Int.ofNat 0), (Int.negSucc 5473439885560693078079), (Int.negSucc 37239797202575852988575), (Int.ofNat 1379973974642723408544), (Int.ofNat 326363899043925392263488), (Int.ofNat 24544209963482903931264), (Int.negSucc 934565892211534635545759), (Int.ofNat 668500015916606958837792), (Int.negSucc 54994901490488387174399)], [(Int.ofNat 0), (Int.ofNat 32424505009394739900480), (Int.ofNat 206785401814919476267776), (Int.negSucc 60925862612207694133583), (Int.negSucc 1802285730415060745248655), (Int.ofNat 99642916050652972958112), (Int.ofNat 4688959588231965027852384), (Int.negSucc 3482738253725879683021967), (Int.ofNat 402896052663566872457520), (Int.negSucc 21893306512647465379583)], [(Int.ofNat 0), (Int.negSucc 121229467578703963046159), (Int.negSucc 707712714255721765949927), (Int.ofNat 430797072660731640359712), (Int.ofNat 6047265148772832144160056), (Int.negSucc 992687245315668006292655), (Int.negSucc 13553528039150204695553207), (Int.ofNat 9305445318959723007550464), (Int.negSucc 662756718643381406863511), (Int.ofNat 45816331219025810253984), (Int.negSucc 4030974676784003530751)], [(Int.ofNat 0), (Int.ofNat 320323931390486307175200), (Int.ofNat 1663482359378572931281680), (Int.negSucc 1632012776019841966417871), (Int.negSucc 13709149459310617061107679), (Int.ofNat 3020268216870478491152688), (Int.ofNat 24520221807569393615778096), (Int.negSucc 11430663691191582466771919), (Int.negSucc 2718458729936150715017567), (Int.ofNat 413546929723700555033232), (Int.negSucc 16062479653219926632063), (Int.negSucc 323754481380519558143)], [(Int.ofNat 0), (Int.negSucc 634110531512686932332879), (Int.negSucc 2832522985589918682961367), (Int.ofNat 4016970385787172030520032), (Int.ofNat 22219344501681786652354464), (Int.negSucc 3750911992952863600042367), (Int.negSucc 28018228248383394238459703), (Int.negSucc 3972006122663450339852831), (Int.ofNat 14301811241356738794017616), (Int.negSucc 1706415312129110600313167), (Int.ofNat 110117561978003710327488), (Int.negSucc 4080176416103519372543), (Int.negSucc 7345780267740659711)], [(Int.ofNat 0), (Int.ofNat 972161473781649571341480), (Int.ofNat 3590895898598782799517804), (Int.negSucc 6957874829759210713187675), (Int.negSucc 26860512648059342824487507), (Int.negSucc 2244338629667717161886027), (Int.ofNat 18771016530375961263720612), (Int.ofNat 36581876265872852321622300), (Int.negSucc 26054670790997454857673419), (Int.ofNat 602113004238106820200212), (Int.ofNat 81386158226318634658752), (Int.negSucc 788774382293085876095), (Int.negSucc 245213143620655696127), (Int.ofNat 45169726132776960)], [(Int.ofNat 0), (Int.negSucc 1176539640169108936330079), (Int.negSucc 3427768120722152106287303), (Int.ofNat 8852162505844374797536116), (Int.ofNat 25567285797154078034393448), (Int.ofNat 16795722516459631864853436), (Int.negSucc 4502692178514055868401943), (Int.negSucc 57424342621599815983995923), (Int.ofNat 14723560213099761704279616), (Int.ofNat 8422506515937887877175380), (Int.negSucc 1075888828875238378836263), (Int.ofNat 56961877708044517981824), (Int.negSucc 1370570392440121737599), (Int.negSucc 595106884183039487)], [(Int.ofNat 0), (Int.ofNat 1135512233373923984018520), (Int.ofNat 2459907413976300991216092), (Int.negSucc 8503161393678392594129867), (Int.negSucc 21050527712696930046575843), (Int.negSucc 32314133189409540177781943), (Int.negSucc 5238656216959839542434007), (Int.ofNat 41108083662762424896308676), (Int.ofNat 24009683418699038985210012), (Int.negSucc 19624120709536978355675879), (Int.ofNat 1164792771110431202012532), (Int.negSucc 17940820885798716938159), (Int.ofNat 589972031494805945088), (Int.negSucc 36500645459874002687)], [(Int.ofNat 0), (Int.negSucc 877340704193739941137199), (Int.negSucc 1307786746264745037063407), (Int.ofNat 6320261034403312718902572), (Int.ofNat 16920489321137640513511368), (Int.ofNat 38128708931802585309360720), (Int.ofNat 12035879908389424193638032), (Int.negSucc 4418785144943832790244339), (Int.negSucc 52723123178696150948871191), (Int.ofNat 14140508006522196273664152), (Int.ofNat 2723777503002103347822456), (Int.negSucc 329894713236891210177167), (Int.ofNat 13086671427629165665440), (Int.negSucc 209430861617669836031)], [(Int.ofNat 0), (Int.ofNat 542003355236673865697040), (Int.ofNat 500465835208423265844384), (Int.negSucc 3766067823519262578542795), (Int.negSucc 13802527132636734686971583), (Int.negSucc 32081611525939574242049807), (Int.negSucc 20301577221010941229977287), (Int.negSucc 17172212604637679301761171), (Int.ofNat 38840627736902195572455396), (Int.ofNat 10310282037481735534841028), (Int.negSucc 7530303971399087924305163), (Int.ofNat 392662274240237517924300), (Int.negSucc 2555657702265942313631), (Int.negSucc 103136049956192962175)], [(Int.ofNat 0), (Int.negSucc 266133901111691906706479), (Int.negSucc 134729890297981145684999), (Int.ofNat 1916469134053424390159352), (Int.ofNat 10491754211260886548888380), (Int.ofNat 21109625014194267232545972), (Int.ofNat 25933782147310338076503180), (Int.ofNat 16849590521232517396154928), (Int.negSucc 2748945161969696607229259), (Int.negSucc 26766158493943550054236823), (Int.ofNat 5065700868541027688093748), (Int.ofNat 616276060479509165459316), (Int.negSucc 55910861669216882757167), (Int.ofNat 1315988028850540938912)], [(Int.ofNat 0), (Int.ofNat 102711365631141751410480), (Int.ofNat 30714956631213596697240), (Int.negSucc 908768938046554931377103), (Int.negSucc 6760938454781548682002967), (Int.negSucc 12095025016831158907805327), (Int.negSucc 23244923198865309063514163), (Int.negSucc 11777856409121009341316147), (Int.negSucc 16382562117285959070803207), (Int.ofNat 17706628984603192039719576), (Int.ofNat 3623973264303637575737052), (Int.negSucc 1547604736738931365399367), (Int.ofNat 38629241568542049445548), (Int.ofNat 1081641532929104555856)], [(Int.ofNat 0), (Int.negSucc 30609708117057978967439), (Int.negSucc 12545570665241143649639), (Int.ofNat 420031278288548702504784), (Int.ofNat 3537526138481606009176512), (Int.ofNat 6695139519096928902681120), (Int.ofNat 14666408091261000961835292), (Int.ofNat 10456205690016830155705704), (Int.ofNat 13111496106606363357197424), (Int.ofNat 480797142390951769816056), (Int.negSucc 7687083655530335864844971), (Int.ofNat 690331696279384291732188), (Int.ofNat 101064301946111745898272), (Int.negSucc 4090468349833244579807)], [(Int.ofNat 0), (Int.ofNat 6855279654803054985000), (Int.ofNat 7334761711118021033724), (Int.negSucc 179122484022633111577211), (Int.negSucc 1492346034633559518529739), (Int.negSucc 3613071673827264029647211), (Int.negSucc 6771364225368304533211799), (Int.negSucc 8984028134589080313311783), (Int.negSucc 5539207568465873732060375), (Int.negSucc 7617606400156329285754967), (Int.ofNat 3784666240097927109138564), (Int.ofNat 896208698588210180416152), (Int.negSucc 140819260933712010314591), (Int.negSucc 1633626709151930576639)], [(Int.ofNat 0), (Int.negSucc 1105887415556971755359), (Int.negSucc 3147325308762775281575), (Int.ofNat 63835578201284807167836), (Int.ofNat 511379844700215350989584), (Int.ofNat 1740449289238937329402404), (Int.ofNat 2528787411818571220501356), (Int.ofNat 5407597959590824087056228), (Int.ofNat 2606906472952466809876500), (Int.ofNat 4803136713028591940354292), (Int.ofNat 898575292147370464817784), (Int.negSucc 1121365085676618181486247), (Int.negSucc 4262987210670806016311), (Int.ofNat 7172336334966858165024)], [(Int.ofNat 0), (Int.ofNat 119783741109183368280), (Int.ofNat 882588870639451791612), (Int.negSucc 17560061287474754340467), (Int.negSucc 143321246747681267351627), (Int.negSucc 684058118402030919023087), (Int.negSucc 925525724719332594518243), (Int.negSucc 2119723753080209928771815), (Int.negSucc 1848367158667211047533299), (Int.negSucc 1414751436609793402870151), (Int.negSucc 1808261458816031465801327), (Int.ofNat 275732881062917471137872), (Int.ofNat 105505100281198824778800), (Int.negSucc 1505073968222120089343)], [(Int.ofNat 0), (Int.negSucc 7637533931753653679), (Int.negSucc 157838252653701464111), (Int.ofNat 3510860427319701097764), (Int.ofNat 32629619395986903497304), (Int.ofNat 207459937359474754760856), (Int.ofNat 364369054419971755583076), (Int.ofNat 546314718499509220417044), (Int.ofNat 1009418240396097516211488), (Int.ofNat 337492931513148720210456), (Int.ofNat 814683589788467311158456), (Int.ofNat 239638933918356047623728), (Int.negSucc 57788549210832582154607), (Int.negSucc 4774565626700319029951)], [(Int.ofNat 0), (Int.ofNat 208108090831718880), (Int.ofNat 16608363339761990136), (Int.negSucc 477223476439399301195), (Int.negSucc 5846345070099340895855), (Int.negSucc 46713550232597815709063), (Int.negSucc 130149624023432363791619), (Int.negSucc 110545328226790219246343), (Int.negSucc 325249708593390006122495), (Int.negSucc 178374107840753672137151), (Int.negSucc 156397147949806282440143), (Int.negSucc 196267680296832526827695), (Int.negSucc 9010128429951939441791), (Int.ofNat 3033622110592845259776)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 791653812831313055), (Int.ofNat 39411399976936255224), (Int.ofNat 771776773673946025140), (Int.ofNat 7493059158521298847884), (Int.ofNat 34898024285052124306680), (Int.ofNat 29375727252722000502984), (Int.ofNat 55712106896482823878584), (Int.ofNat 85536318386834840630016), (Int.ofNat 13313906491747253550048), (Int.ofNat 56442633792791826569184), (Int.ofNat 19326844649231971320096), (Int.ofNat 393243450062722819200)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1497606268201115039), (Int.negSucc 66369303077399166455), (Int.negSucc 804761530752675668615), (Int.negSucc 6314694075825325244783), (Int.negSucc 9542160233828747575631), (Int.negSucc 3860433416851002572399), (Int.negSucc 21255165013586152270751), (Int.negSucc 4950217602907345449791), (Int.negSucc 5788139396126877146303), (Int.negSucc 7298638303783951162367), (Int.negSucc 917357675979920663807)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2775940570431428256), (Int.ofNat 51577326137314802952), (Int.ofNat 700523325581692578408), (Int.ofNat 2199202782401176633008), (Int.ofNat 213835218674923580688), (Int.ofNat 2154075017917518516096), (Int.ofNat 2383367982550351224192), (Int.negSucc 317120748560107455743), (Int.ofNat 1118125218191398263360), (Int.ofNat 307433358469575141120)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1474125479050597055), (Int.negSucc 39634037257657761071), (Int.negSucc 286221320722961857007), (Int.negSucc 163296831719084304383), (Int.ofNat 84022949457342897408), (Int.negSucc 449738599704225474239), (Int.ofNat 97453225956075717312), (Int.negSucc 55169244523584322559), (Int.negSucc 33720772168183910399)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 615355489192821120), (Int.ofNat 16840646652313066464), (Int.ofNat 36933016125691186848), (Int.negSucc 34227880953814593791), (Int.ofNat 32181588887927150016), (Int.negSucc 5834696783543274239)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 155978983434680063), (Int.negSucc 2509242662113530047), (Int.ofNat 1633921891315629120)]]

theorem h0n82_arithmetic_row0 :
    (BiPoly.mul h0p66 h0p57).getD 0 []=h0p82.getD 0 [] := by
  decide +kernel

theorem h0n82_arithmetic_row1 :
    (BiPoly.mul h0p66 h0p57).getD 1 []=h0p82.getD 1 [] := by
  decide +kernel

theorem h0n82_arithmetic_row2 :
    (BiPoly.mul h0p66 h0p57).getD 2 []=h0p82.getD 2 [] := by
  decide +kernel

theorem h0n82_arithmetic_row3 :
    (BiPoly.mul h0p66 h0p57).getD 3 []=h0p82.getD 3 [] := by
  decide +kernel

theorem h0n82_arithmetic_row4 :
    (BiPoly.mul h0p66 h0p57).getD 4 []=h0p82.getD 4 [] := by
  decide +kernel

theorem h0n82_arithmetic_row5 :
    (BiPoly.mul h0p66 h0p57).getD 5 []=h0p82.getD 5 [] := by
  decide +kernel

theorem h0n82_arithmetic_row6 :
    (BiPoly.mul h0p66 h0p57).getD 6 []=h0p82.getD 6 [] := by
  decide +kernel

theorem h0n82_arithmetic_row7 :
    (BiPoly.mul h0p66 h0p57).getD 7 []=h0p82.getD 7 [] := by
  decide +kernel

theorem h0n82_arithmetic_row8 :
    (BiPoly.mul h0p66 h0p57).getD 8 []=h0p82.getD 8 [] := by
  decide +kernel

theorem h0n82_arithmetic_row9 :
    (BiPoly.mul h0p66 h0p57).getD 9 []=h0p82.getD 9 [] := by
  decide +kernel

theorem h0n82_arithmetic_row10 :
    (BiPoly.mul h0p66 h0p57).getD 10 []=h0p82.getD 10 [] := by
  decide +kernel

theorem h0n82_arithmetic_row11 :
    (BiPoly.mul h0p66 h0p57).getD 11 []=h0p82.getD 11 [] := by
  decide +kernel

theorem h0n82_arithmetic_row12 :
    (BiPoly.mul h0p66 h0p57).getD 12 []=h0p82.getD 12 [] := by
  decide +kernel

theorem h0n82_arithmetic_row13 :
    (BiPoly.mul h0p66 h0p57).getD 13 []=h0p82.getD 13 [] := by
  decide +kernel

theorem h0n82_arithmetic_row14 :
    (BiPoly.mul h0p66 h0p57).getD 14 []=h0p82.getD 14 [] := by
  decide +kernel

theorem h0n82_arithmetic_row15 :
    (BiPoly.mul h0p66 h0p57).getD 15 []=h0p82.getD 15 [] := by
  decide +kernel

theorem h0n82_arithmetic_row16 :
    (BiPoly.mul h0p66 h0p57).getD 16 []=h0p82.getD 16 [] := by
  decide +kernel

theorem h0n82_arithmetic_row17 :
    (BiPoly.mul h0p66 h0p57).getD 17 []=h0p82.getD 17 [] := by
  decide +kernel

theorem h0n82_arithmetic_row18 :
    (BiPoly.mul h0p66 h0p57).getD 18 []=h0p82.getD 18 [] := by
  decide +kernel

theorem h0n82_arithmetic_row19 :
    (BiPoly.mul h0p66 h0p57).getD 19 []=h0p82.getD 19 [] := by
  decide +kernel

theorem h0n82_arithmetic_row20 :
    (BiPoly.mul h0p66 h0p57).getD 20 []=h0p82.getD 20 [] := by
  decide +kernel

theorem h0n82_arithmetic_row21 :
    (BiPoly.mul h0p66 h0p57).getD 21 []=h0p82.getD 21 [] := by
  decide +kernel

theorem h0n82_arithmetic_row22 :
    (BiPoly.mul h0p66 h0p57).getD 22 []=h0p82.getD 22 [] := by
  decide +kernel

theorem h0n82_arithmetic_row23 :
    (BiPoly.mul h0p66 h0p57).getD 23 []=h0p82.getD 23 [] := by
  decide +kernel

theorem h0n82_arithmetic_row24 :
    (BiPoly.mul h0p66 h0p57).getD 24 []=h0p82.getD 24 [] := by
  decide +kernel

theorem h0n82_arithmetic : BiPoly.mul h0p66 h0p57=h0p82 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<25 at hk
    have hf : ∀ j : Fin 25, (BiPoly.mul h0p66 h0p57).getD j.val []=h0p82.getD j.val [] :=
      (fun j => Fin.cases h0n82_arithmetic_row0 (fun j => Fin.cases h0n82_arithmetic_row1 (fun j => Fin.cases h0n82_arithmetic_row2 (fun j => Fin.cases h0n82_arithmetic_row3 (fun j => Fin.cases h0n82_arithmetic_row4 (fun j => Fin.cases h0n82_arithmetic_row5 (fun j => Fin.cases h0n82_arithmetic_row6 (fun j => Fin.cases h0n82_arithmetic_row7 (fun j => Fin.cases h0n82_arithmetic_row8 (fun j => Fin.cases h0n82_arithmetic_row9 (fun j => Fin.cases h0n82_arithmetic_row10 (fun j => Fin.cases h0n82_arithmetic_row11 (fun j => Fin.cases h0n82_arithmetic_row12 (fun j => Fin.cases h0n82_arithmetic_row13 (fun j => Fin.cases h0n82_arithmetic_row14 (fun j => Fin.cases h0n82_arithmetic_row15 (fun j => Fin.cases h0n82_arithmetic_row16 (fun j => Fin.cases h0n82_arithmetic_row17 (fun j => Fin.cases h0n82_arithmetic_row18 (fun j => Fin.cases h0n82_arithmetic_row19 (fun j => Fin.cases h0n82_arithmetic_row20 (fun j => Fin.cases h0n82_arithmetic_row21 (fun j => Fin.cases h0n82_arithmetic_row22 (fun j => Fin.cases h0n82_arithmetic_row23 (fun j => Fin.cases h0n82_arithmetic_row24 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n82 : h0e82.toBi mapPolyEnv=h0p82 := by
  change BiPoly.mul (h0e66.toBi mapPolyEnv) (h0e57.toBi mapPolyEnv)=h0p82
  rw [h0n66, h0n57]
  exact h0n82_arithmetic

#print axioms h0n82_arithmetic
end StackSorting.RationalLift
