import BivariateRowEquality
import Horner0Base
import Horner0Node080
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p81 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 246814644805755407999), (Int.negSucc 2113146110801568588479), (Int.negSucc 4345813874568337522559), (Int.ofNat 4151782318848888677760), (Int.ofNat 14244889083888109564800), (Int.negSucc 1556810286716919349439), (Int.negSucc 9170434643183615894399)], [(Int.ofNat 0), (Int.ofNat 3106519450148906377920), (Int.ofNat 26323274390563562694624), (Int.ofNat 53231069018102711067936), (Int.negSucc 49626893689083570021119), (Int.negSucc 158144672163104046043775), (Int.ofNat 31857265798574863717728), (Int.ofNat 88721037245404037937312), (Int.negSucc 4774929780707868916799)], [(Int.ofNat 0), (Int.negSucc 18574561222424498371679), (Int.negSucc 154216645853978745562895), (Int.negSucc 305559771066611503025615), (Int.ofNat 267615608462379861279552), (Int.ofNat 816273158600987011684224), (Int.negSucc 195150614112850217520527), (Int.negSucc 369095346817514468322767), (Int.ofNat 5676668322036295802976), (Int.ofNat 1041096086220443469696)], [(Int.ofNat 0), (Int.ofNat 70119890238890396972880), (Int.ofNat 564143287937652978013800), (Int.ofNat 1097139616619777179766640), (Int.negSucc 823870317764040125698871), (Int.negSucc 2579533070273442158988383), (Int.ofNat 517803542639619329061432), (Int.ofNat 863243610330136151531376), (Int.ofNat 166080677033076440430744), (Int.negSucc 26439807437925877226447), (Int.ofNat 1104983151641276903424)], [(Int.ofNat 0), (Int.negSucc 187154637045037516268639), (Int.negSucc 1444097655602793788946479), (Int.negSucc 2781547452742267975532831), (Int.ofNat 1468712632367565344738736), (Int.ofNat 5550865315839977117812704), (Int.negSucc 288471668066601056491247), (Int.negSucc 1247045285442763629681983), (Int.negSucc 915454671162149520201167), (Int.ofNat 116840176195819498711776), (Int.negSucc 7365493546848595616255), (Int.ofNat 235424577239960942592)], [(Int.ofNat 0), (Int.ofNat 374451828459464180773440), (Int.ofNat 2750674311936335802182112), (Int.ofNat 5340312920693234344749912), (Int.negSucc 1036273826471252487403463), (Int.negSucc 8505719041281034001422391), (Int.negSucc 2177762161340732718473279), (Int.ofNat 1109045917586483050148712), (Int.ofNat 2197431287032352788763064), (Int.negSucc 87732554006764128502439), (Int.negSucc 3407334025849929203759), (Int.negSucc 113768279425902658175), (Int.ofNat 15413326191745016832)], [(Int.ofNat 0), (Int.negSucc 580623835108820493934439), (Int.negSucc 4052987464544169963499691), (Int.negSucc 8139633385297674454857107), (Int.negSucc 1906715174598632210709923), (Int.ofNat 9138097762160761893823452), (Int.ofNat 7563679930520634098407284), (Int.negSucc 155241134578286909920043), (Int.negSucc 2686883358943438494285995), (Int.negSucc 624992077430169013571075), (Int.ofNat 95400722710086827040792), (Int.negSucc 5061681769521844133855), (Int.ofNat 93339826645609944576), (Int.negSucc 82811164576757759)], [(Int.ofNat 0), (Int.ofNat 711319273625275188711840), (Int.ofNat 4748182611666991281248472), (Int.ofNat 10183008675395496499140780), (Int.ofNat 7183259908209615408597792), (Int.negSucc 5666283944814718711507139), (Int.negSucc 12926527412080040778676967), (Int.negSucc 2210359854365834349344075), (Int.ofNat 1080628391369879906841288), (Int.ofNat 1989271659088645773273972), (Int.negSucc 163379883847706108987831), (Int.ofNat 5745184712863082457120), (Int.negSucc 192305350129849698239), (Int.ofNat 2687026277693691648)], [(Int.ofNat 0), (Int.negSucc 695661126599747011326599), (Int.negSucc 4516636975126749428585603), (Int.negSucc 10688455602382981462232315), (Int.negSucc 12285057702306737962083251), (Int.negSucc 1374810729390106732340567), (Int.ofNat 13250331064137508429598424), (Int.ofNat 6130248936363153347742636), (Int.ofNat 1668331979996867400964476), (Int.negSucc 2385676611339715998136103), (Int.negSucc 183640328395425820906331), (Int.ofNat 32032933692077199600408), (Int.negSucc 1305676177525224414239), (Int.ofNat 17185379144588518272)], [(Int.ofNat 0), (Int.ofNat 545297398603328747792400), (Int.ofNat 3545707579479489122790864), (Int.ofNat 9521795256270634950777204), (Int.ofNat 14401179455527411579411368), (Int.ofNat 8802592325160798933015408), (Int.negSucc 6873570322644898019645567), (Int.negSucc 9302991861652393365223355), (Int.negSucc 3492042576639774191185439), (Int.ofNat 557567444140485548235072), (Int.ofNat 891519454129767280099248), (Int.negSucc 65967662829441607825799), (Int.ofNat 1522939272376477226352), (Int.negSucc 9886114471674645119)], [(Int.ofNat 0), (Int.negSucc 342210984793433747798159), (Int.negSucc 2322788627309447554008527), (Int.negSucc 7218008818384190424710723), (Int.negSucc 12905252856547110656606807), (Int.negSucc 12873791004689793715914959), (Int.negSucc 2205589489281334904471351), (Int.ofNat 8271529822056292896956820), (Int.ofNat 3920091309892445991200484), (Int.ofNat 1876492158444484755538284), (Int.negSucc 994851929376374961689003), (Int.negSucc 38331259511357832888107), (Int.ofNat 6244162780018572132120), (Int.negSucc 168271539058398338495)], [(Int.ofNat 0), (Int.ofNat 170935337846435113285200), (Int.ofNat 1275135634967937709169784), (Int.ofNat 4637048715424100363127840), (Int.ofNat 9369437008616709181045212), (Int.ofNat 12276768089877462707192148), (Int.ofNat 8306981552001376102560348), (Int.negSucc 2969104268231121732003815), (Int.negSucc 3446537424682856772568979), (Int.negSucc 2510612776553717078714327), (Int.ofNat 50360890046862038843412), (Int.ofNat 217233939812022010438188), (Int.negSucc 9376016524500239063519), (Int.negSucc 12609762123521352911)], [(Int.ofNat 0), (Int.negSucc 67210112423205628702319), (Int.negSucc 584010841362752314987031), (Int.negSucc 2502333690012002069152967), (Int.negSucc 5723460424054655122484255), (Int.negSucc 8785218683852348260873007), (Int.negSucc 9153769995056588267469179), (Int.negSucc 2559742822814713724471363), (Int.ofNat 2000153621374756793292000), (Int.ofNat 1498229716599002653837248), (Int.ofNat 858482816290278597544164), (Int.negSucc 186294169917155964425927), (Int.negSucc 9490135097868096111827), (Int.ofNat 642548143036455345048)], [(Int.ofNat 0), (Int.ofNat 20437086224719256197920), (Int.ofNat 220145102819982235133376), (Int.ofNat 1119893680874703946678272), (Int.ofNat 2993172865294050345163704), (Int.ofNat 5042053779414742922962200), (Int.ofNat 6574626080655720387660828), (Int.ofNat 4787921984224413024722136), (Int.ofNat 60357262342744593341400), (Int.negSucc 432282096436618853996903), (Int.negSucc 794405575141958598985571), (Int.negSucc 54164299752745755731771), (Int.ofNat 25470135820335245416632), (Int.negSucc 94175404219375463231)], [(Int.ofNat 0), (Int.negSucc 4677085363522020775559), (Int.negSucc 66802667068470201150443), (Int.negSucc 408732769233257023797515), (Int.negSucc 1330649142642544356265091), (Int.negSucc 2443704064335498777229595), (Int.negSucc 3515324321379766859490551), (Int.negSucc 3879679296822906881144375), (Int.negSucc 1451831359518584666644607), (Int.negSucc 114899701898228843304959), (Int.ofNat 230366282542754942169204), (Int.ofNat 181861919999917429326912), (Int.negSucc 9051004204330462747871), (Int.negSucc 1151217714062494458143)], [(Int.ofNat 0), (Int.ofNat 772031447926841641920), (Int.ofNat 15824731564603774185576), (Int.ofNat 119056530760752039312876), (Int.ofNat 489271816735272433384776), (Int.ofNat 1031370224270252264586444), (Int.ofNat 1507704897225070082849268), (Int.ofNat 2046177342920104407283980), (Int.ofNat 1523783233987897547210148), (Int.ofNat 358355743553009943324252), (Int.ofNat 95120331510906101387232), (Int.negSucc 100278671398764180604055), (Int.negSucc 14483705890069248910343), (Int.ofNat 673104454022061007632)], [(Int.ofNat 0), (Int.negSucc 85645257265850071079), (Int.negSucc 2805708486781197356915), (Int.negSucc 26910233365271313599963), (Int.negSucc 143199257253608516309411), (Int.negSucc 375050480371911464252495), (Int.negSucc 558120035191531313781611), (Int.negSucc 777685172468793725213495), (Int.negSucc 885970825814479674071411), (Int.negSucc 383776381117933938837647), (Int.negSucc 127917371520935534596463), (Int.negSucc 4502289224469598316783), (Int.ofNat 14223131205384095580816), (Int.ofNat 652872684175337154528)], [(Int.ofNat 0), (Int.ofNat 5592045130259428560), (Int.ofNat 349495831769782996656), (Int.ofNat 4541695965401329668948), (Int.ofNat 31928271581172746008104), (Int.ofNat 111793039885902164476968), (Int.ofNat 186615865146075738612060), (Int.ofNat 232210941537528360546300), (Int.ofNat 331136618634307366950888), (Int.ofNat 245798412130196516168856), (Int.ofNat 83042469248129639982504), (Int.ofNat 30027073351447504342656), (Int.negSucc 2151980777562943181903), (Int.negSucc 722201655804605954783)], [(Int.ofNat 0), (Int.negSucc 155483056368525599), (Int.negSucc 27311265212016363911), (Int.negSucc 539715936672458026091), (Int.negSucc 5145786957483981582335), (Int.negSucc 25546127446289939626799), (Int.negSucc 54527963041456691504147), (Int.negSucc 61898719841709964490159), (Int.negSucc 83224460942919707475167), (Int.negSucc 98022615641354759895647), (Int.negSucc 43992402078500547651791), (Int.negSucc 17084659022465054905871), (Int.negSucc 2990393910997954009631), (Int.ofNat 74742906785624942976)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1012135830530634720), (Int.ofNat 40557964861676371608), (Int.ofNat 556460108174019733524), (Int.ofNat 4154873485074404081508), (Int.ofNat 12661253535194423367120), (Int.ofNat 16009458485773811151960), (Int.ofNat 15228901062992066928840), (Int.ofNat 23957393976614046017808), (Int.ofNat 17365009271625481425696), (Int.ofNat 6141324379709285813664), (Int.ofNat 1985513988813991101792), (Int.ofNat 168905805699167136576)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1466691568018204319), (Int.negSucc 35386275449281606775), (Int.negSucc 435675389121412740359), (Int.negSucc 2099036779582055382575), (Int.negSucc 3641517081666308048975), (Int.negSucc 2623140020365171518671), (Int.negSucc 3332904465227238381311), (Int.negSucc 4347372760028518161023), (Int.negSucc 1800289186116967689407), (Int.negSucc 596453836553630547839), (Int.negSucc 87338026076463871487)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 959339398462730784), (Int.ofNat 24451678568394633384), (Int.ofNat 219887188457093022456), (Int.ofNat 605663339642601613344), (Int.ofNat 522040511045607546672), (Int.ofNat 225367253106739235424), (Int.ofNat 581481537678955516032), (Int.ofNat 394416837141498759168), (Int.ofNat 114251713699471470144), (Int.ofNat 16767127901501394048)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 415451046702893759), (Int.negSucc 11636825386280293295), (Int.negSucc 62016528395668765967), (Int.negSucc 87395195314371556511), (Int.negSucc 12970966664899904255), (Int.negSucc 20885147888642732735), (Int.negSucc 50068325969958361535), (Int.negSucc 15552499461501995135), (Int.negSucc 1124025738939463679)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 126142825997232000), (Int.ofNat 3010453085311260768), (Int.ofNat 8402648363286712416), (Int.ofNat 3412989337190420160), (Int.negSucc 3728428989056698175), (Int.ofNat 2543705515819605888), (Int.ofNat 1124025738939463680)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 17330998159408895), (Int.negSucc 313466736553654463), (Int.negSucc 376062603656825663), (Int.ofNat 363093753625695360)]]

theorem h0n81_arithmetic_row0 :
    (BiPoly.mul h0p4 h0p80).getD 0 []=h0p81.getD 0 [] := by
  decide +kernel

theorem h0n81_arithmetic_row1 :
    (BiPoly.mul h0p4 h0p80).getD 1 []=h0p81.getD 1 [] := by
  decide +kernel

theorem h0n81_arithmetic_row2 :
    (BiPoly.mul h0p4 h0p80).getD 2 []=h0p81.getD 2 [] := by
  decide +kernel

theorem h0n81_arithmetic_row3 :
    (BiPoly.mul h0p4 h0p80).getD 3 []=h0p81.getD 3 [] := by
  decide +kernel

theorem h0n81_arithmetic_row4 :
    (BiPoly.mul h0p4 h0p80).getD 4 []=h0p81.getD 4 [] := by
  decide +kernel

theorem h0n81_arithmetic_row5 :
    (BiPoly.mul h0p4 h0p80).getD 5 []=h0p81.getD 5 [] := by
  decide +kernel

theorem h0n81_arithmetic_row6 :
    (BiPoly.mul h0p4 h0p80).getD 6 []=h0p81.getD 6 [] := by
  decide +kernel

theorem h0n81_arithmetic_row7 :
    (BiPoly.mul h0p4 h0p80).getD 7 []=h0p81.getD 7 [] := by
  decide +kernel

theorem h0n81_arithmetic_row8 :
    (BiPoly.mul h0p4 h0p80).getD 8 []=h0p81.getD 8 [] := by
  decide +kernel

theorem h0n81_arithmetic_row9 :
    (BiPoly.mul h0p4 h0p80).getD 9 []=h0p81.getD 9 [] := by
  decide +kernel

theorem h0n81_arithmetic_row10 :
    (BiPoly.mul h0p4 h0p80).getD 10 []=h0p81.getD 10 [] := by
  decide +kernel

theorem h0n81_arithmetic_row11 :
    (BiPoly.mul h0p4 h0p80).getD 11 []=h0p81.getD 11 [] := by
  decide +kernel

theorem h0n81_arithmetic_row12 :
    (BiPoly.mul h0p4 h0p80).getD 12 []=h0p81.getD 12 [] := by
  decide +kernel

theorem h0n81_arithmetic_row13 :
    (BiPoly.mul h0p4 h0p80).getD 13 []=h0p81.getD 13 [] := by
  decide +kernel

theorem h0n81_arithmetic_row14 :
    (BiPoly.mul h0p4 h0p80).getD 14 []=h0p81.getD 14 [] := by
  decide +kernel

theorem h0n81_arithmetic_row15 :
    (BiPoly.mul h0p4 h0p80).getD 15 []=h0p81.getD 15 [] := by
  decide +kernel

theorem h0n81_arithmetic_row16 :
    (BiPoly.mul h0p4 h0p80).getD 16 []=h0p81.getD 16 [] := by
  decide +kernel

theorem h0n81_arithmetic_row17 :
    (BiPoly.mul h0p4 h0p80).getD 17 []=h0p81.getD 17 [] := by
  decide +kernel

theorem h0n81_arithmetic_row18 :
    (BiPoly.mul h0p4 h0p80).getD 18 []=h0p81.getD 18 [] := by
  decide +kernel

theorem h0n81_arithmetic_row19 :
    (BiPoly.mul h0p4 h0p80).getD 19 []=h0p81.getD 19 [] := by
  decide +kernel

theorem h0n81_arithmetic_row20 :
    (BiPoly.mul h0p4 h0p80).getD 20 []=h0p81.getD 20 [] := by
  decide +kernel

theorem h0n81_arithmetic_row21 :
    (BiPoly.mul h0p4 h0p80).getD 21 []=h0p81.getD 21 [] := by
  decide +kernel

theorem h0n81_arithmetic_row22 :
    (BiPoly.mul h0p4 h0p80).getD 22 []=h0p81.getD 22 [] := by
  decide +kernel

theorem h0n81_arithmetic_row23 :
    (BiPoly.mul h0p4 h0p80).getD 23 []=h0p81.getD 23 [] := by
  decide +kernel

theorem h0n81_arithmetic_row24 :
    (BiPoly.mul h0p4 h0p80).getD 24 []=h0p81.getD 24 [] := by
  decide +kernel

theorem h0n81_arithmetic : BiPoly.mul h0p4 h0p80=h0p81 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<25 at hk
    have hf : ∀ j : Fin 25, (BiPoly.mul h0p4 h0p80).getD j.val []=h0p81.getD j.val [] :=
      (fun j => Fin.cases h0n81_arithmetic_row0 (fun j => Fin.cases h0n81_arithmetic_row1 (fun j => Fin.cases h0n81_arithmetic_row2 (fun j => Fin.cases h0n81_arithmetic_row3 (fun j => Fin.cases h0n81_arithmetic_row4 (fun j => Fin.cases h0n81_arithmetic_row5 (fun j => Fin.cases h0n81_arithmetic_row6 (fun j => Fin.cases h0n81_arithmetic_row7 (fun j => Fin.cases h0n81_arithmetic_row8 (fun j => Fin.cases h0n81_arithmetic_row9 (fun j => Fin.cases h0n81_arithmetic_row10 (fun j => Fin.cases h0n81_arithmetic_row11 (fun j => Fin.cases h0n81_arithmetic_row12 (fun j => Fin.cases h0n81_arithmetic_row13 (fun j => Fin.cases h0n81_arithmetic_row14 (fun j => Fin.cases h0n81_arithmetic_row15 (fun j => Fin.cases h0n81_arithmetic_row16 (fun j => Fin.cases h0n81_arithmetic_row17 (fun j => Fin.cases h0n81_arithmetic_row18 (fun j => Fin.cases h0n81_arithmetic_row19 (fun j => Fin.cases h0n81_arithmetic_row20 (fun j => Fin.cases h0n81_arithmetic_row21 (fun j => Fin.cases h0n81_arithmetic_row22 (fun j => Fin.cases h0n81_arithmetic_row23 (fun j => Fin.cases h0n81_arithmetic_row24 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n81 : h0e81.toBi mapPolyEnv=h0p81 := by
  change BiPoly.mul (h0e4.toBi mapPolyEnv) (h0e80.toBi mapPolyEnv)=h0p81
  rw [h0n4, h0n80]
  exact h0n81_arithmetic

#print axioms h0n81_arithmetic
end StackSorting.RationalLift
