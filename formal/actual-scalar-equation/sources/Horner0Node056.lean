import BivariateRowEquality
import Horner0Base
import Horner0Node055
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p56 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 246814644805755407999), (Int.negSucc 1619516821190057772479), (Int.negSucc 1106780232188221977599), (Int.ofNat 6365342783225332632960), (Int.ofNat 1514203517437444298880), (Int.negSucc 4585217321591807947199)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3106519450148906377920), (Int.ofNat 20110235490265749938784), (Int.ofNat 13010598037571211190368), (Int.negSucc 75648089764225992401855), (Int.negSucc 6848492634652061240063), (Int.ofNat 45554251067878986197856), (Int.negSucc 2387464890353934458399)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 18574561222424498371679), (Int.negSucc 117067523409129748819535), (Int.negSucc 71424724248352005386543), (Int.ofNat 410465056959083872052640), (Int.negSucc 4656955317180732421055), (Int.negSucc 185836703478488752678415), (Int.ofNat 2578060139463037034064), (Int.ofNat 520548043110221734848)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 70119890238890396972880), (Int.ofNat 423903507459872184068040), (Int.ofNat 249332601700032811630560), (Int.negSucc 1322535521164105748959991), (Int.ofNat 65537972054769338931600), (Int.ofNat 386727598530080651198232), (Int.ofNat 89788413269974849134912), (Int.negSucc 13496149506873257839079), (Int.ofNat 552491575820638451712)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 187154637045037516268639), (Int.negSucc 1069788381512718756409199), (Int.negSucc 641970689716830462714431), (Int.ofNat 2752654011801226270167600), (Int.ofNat 45557292237524577477504), (Int.negSucc 379586252541650211446255), (Int.negSucc 487872780359463206789471), (Int.ofNat 60290889556776893377776), (Int.negSucc 3741602917734288043775), (Int.ofNat 117712288619980471296)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 374451828459464180773440), (Int.ofNat 2001770655017407440635232), (Int.ofNat 1336771610658419463479448), (Int.negSucc 3709817047788091414362359), (Int.negSucc 1086084945704851172697671), (Int.negSucc 5592269931030373077935), (Int.ofNat 1120230457448543796304584), (Int.negSucc 43029627864734803846103), (Int.negSucc 1673298277294520810231), (Int.negSucc 60737471260887583295), (Int.ofNat 7706663095872508416)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 580623835108820493934439), (Int.negSucc 2891739794326528975630811), (Int.negSucc 2356153796644616503595483), (Int.ofNat 2805592418690600796481044), (Int.ofNat 3526912924779560300861364), (Int.ofNat 509854080961513496684556), (Int.negSucc 1174949296501313903289155), (Int.negSucc 336984765940810687707683), (Int.ofNat 48977454451452361844292), (Int.negSucc 2554186192817896647791), (Int.ofNat 46690616113949161728), (Int.negSucc 41405582288378879)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 711319273625275188711840), (Int.ofNat 3325544064416440903824792), (Int.ofNat 3531920546562614691491196), (Int.ofNat 119418815084386025615400), (Int.negSucc 5905121574983490762737939), (Int.negSucc 1116284262113059253201087), (Int.ofNat 22208669860284157058100), (Int.ofNat 1036211051649311592725088), (Int.negSucc 83150444209977412176203), (Int.ofNat 2921004572248715364576), (Int.negSucc 96824431634348272031), (Int.ofNat 1343513138846845824)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 695661126599747011326599), (Int.negSucc 3125314721927255405932403), (Int.negSucc 4437826158528470650367507), (Int.negSucc 3409405385249796661348235), (Int.ofNat 5444000041109486590355904), (Int.ofNat 2362330981918535248886616), (Int.ofNat 1405586972526082849969404), (Int.negSucc 1142841965055298298974331), (Int.negSucc 99992681229119400187439), (Int.ofNat 16345034062812979468548), (Int.negSucc 657134433548759336687), (Int.ofNat 8592689572294259136)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 545297398603328747792400), (Int.ofNat 2455112782272831627206064), (Int.ofNat 4611569691724971696365076), (Int.ofNat 5178040072077468186681216), (Int.negSucc 1553487818994137440347023), (Int.negSucc 3766594684656623138951519), (Int.negSucc 1769802492339147087320315), (Int.ofNat 47562408038519983455192), (Int.ofNat 462442628063445581324688), (Int.negSucc 33365801997123882550127), (Int.ofNat 763941164806157274456), (Int.negSucc 4943057235837322559)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 342210984793433747798159), (Int.negSucc 1638366657722580058412207), (Int.negSucc 3941275502939030307886307), (Int.negSucc 5022701850669050040834191), (Int.negSucc 2828387303351693634246575), (Int.ofNat 3451185117422052364021800), (Int.ofNat 1369159587212188168913220), (Int.ofNat 1181772135468069653374044), (Int.negSucc 487052112491654551209803), (Int.negSucc 20747704393065859269395), (Int.ofNat 3164149274773885650684), (Int.negSucc 84135769529199169247)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 170935337846435113285200), (Int.ofNat 933264959275067482599384), (Int.ofNat 2770518796873965397929072), (Int.ofNat 3828399414868778385187068), (Int.ofNat 4619969260139905936818012), (Int.negSucc 932956968278435771075675), (Int.negSucc 1103190331674250189852463), (Int.negSucc 1240156761334356392864051), (Int.negSucc 30299253885004292986223), (Int.ofNat 110959397816870624815860), (Int.negSucc 4684855821719239193531), (Int.negSucc 6304881061760676455)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 67210112423205628702319), (Int.negSucc 449590616516341057582391), (Int.negSucc 1603152456979319953988183), (Int.negSucc 2517155510096015214507887), (Int.negSucc 3750907663660317831857231), (Int.negSucc 1651954667735952603754715), (Int.ofNat 744166512657191483038068), (Int.ofNat 511820596060373827215864), (Int.ofNat 474588524478254999405520), (Int.negSucc 90694232666231401266875), (Int.negSucc 4905704584693161892175), (Int.ofNat 321274071518227672524)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 20437086224719256197920), (Int.ofNat 179270930370543722737536), (Int.ofNat 761351820133616501203200), (Int.ofNat 1470469225026817342757304), (Int.ofNat 2101115329361108237447592), (Int.ofNat 2372395421933503912765644), (Int.ofNat 43131140357405199190848), (Int.negSucc 25905018372065805040295), (Int.negSucc 380472059692487243916311), (Int.negSucc 33461455756984111152947), (Int.ofNat 12758611761222466574124), (Int.negSucc 47087702109687731615)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 4677085363522020775559), (Int.negSucc 57448496341426159599323), (Int.negSucc 293835776550404704598867), (Int.negSucc 742977589541734947067355), (Int.negSucc 957748885252028883094883), (Int.negSucc 1599826550875709093300783), (Int.negSucc 680026195071488694542807), (Int.negSucc 91778969375607277558991), (Int.ofNat 68658236852985711813024), (Int.ofNat 93049808836783518543156), (Int.negSucc 4237697673649607759399), (Int.negSucc 575608857031247229071)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 772031447926841641920), (Int.ofNat 14280668668750090901736), (Int.ofNat 90495193423251857509404), (Int.ofNat 308281429888768718365968), (Int.ofNat 414807364492714827854508), (Int.ofNat 678090168239640427140252), (Int.ofNat 689997006440823553003476), (Int.ofNat 143789221106250441203196), (Int.ofNat 70777301340509060917860), (Int.negSucc 46434271170112020448487), (Int.negSucc 7410129058540139707079), (Int.ofNat 336552227011030503816)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 85645257265850071079), (Int.negSucc 2634417972249497214755), (Int.negSucc 21641397420772319170451), (Int.negSucc 99916462412063877968507), (Int.negSucc 175217555547783708315479), (Int.negSucc 207684924095963897150651), (Int.negSucc 362315324276865930912191), (Int.negSucc 161340177260747812247027), (Int.negSucc 61096026596438314343591), (Int.negSucc 5725318328058905909279), (Int.ofNat 6948347431648213501776), (Int.ofNat 326436342087668577264)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5592045130259428560), (Int.ofNat 338311741509264139536), (Int.ofNat 3865072482382801389876), (Int.ofNat 24198126616407143228352), (Int.ofNat 63396786653087878020264), (Int.ofNat 59822291839899982571532), (Int.ofNat 112566357857728395403236), (Int.ofNat 106003902918850576144416), (Int.ofNat 33790606292495363880024), (Int.ofNat 15461256663138912222456), (Int.negSucc 895439974830320102255), (Int.negSucc 361100827902302977391)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 155483056368525599), (Int.negSucc 27000299099279312711), (Int.negSucc 485715338473899400667), (Int.negSucc 4174356280536182780999), (Int.negSucc 17197414885217574064799), (Int.negSucc 20133133271021543374547), (Int.negSucc 21632453299666877741063), (Int.negSucc 39959554343585951993039), (Int.negSucc 18103506954182855909567), (Int.negSucc 7785388170134835832655), (Int.negSucc 1513882682195383240559), (Int.ofNat 37371453392812471488)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1012135830530634720), (Int.ofNat 38533693200615102168), (Int.ofNat 479392721772789529188), (Int.ofNat 3196088041528825023132), (Int.ofNat 6269077452136773320856), (Int.ofNat 3471303581500264510248), (Int.ofNat 8286293899991537908344), (Int.ofNat 7384806176630970201120), (Int.ofNat 2595396918363541023456), (Int.ofNat 950530542982203766752), (Int.ofNat 84452902849583568288)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1466691568018204319), (Int.negSucc 32452892313245198135), (Int.negSucc 370769604494922344087), (Int.negSucc 1357497570592210694399), (Int.negSucc 926521940481886660175), (Int.negSucc 770096139401398198319), (Int.negSucc 1792712186424441984671), (Int.negSucc 761948387179634191679), (Int.negSucc 276392411757699306047), (Int.negSucc 43669013038231935743)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 959339398462730784), (Int.ofNat 22532999771469171816), (Int.ofNat 174821188914154678824), (Int.ofNat 256020961814292255696), (Int.ofNat 9998587417023035280), (Int.ofNat 205370078272693164864), (Int.ofNat 170741381133569186304), (Int.ofNat 52934074874360386560), (Int.ofNat 8383563950750697024)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 415451046702893759), (Int.negSucc 10805923292874505775), (Int.negSucc 40404681809919754415), (Int.negSucc 6585831694532047679), (Int.ofNat 200696724164191104), (Int.negSucc 21286541336971114943), (Int.negSucc 7495243296016131647), (Int.negSucc 562012869469731839)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 126142825997232000), (Int.ofNat 2758167433316796768), (Int.ofNat 2886313496653118880), (Int.negSucc 2359637656115817599), (Int.ofNat 990846323174937024), (Int.ofNat 562012869469731840)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 17330998159408895), (Int.negSucc 278804740234836671), (Int.ofNat 181546876812847680)]]

theorem h0n56_arithmetic_row0 :
    (BiPoly.mul h0p37 h0p55).getD 0 []=h0p56.getD 0 [] := by
  decide +kernel

theorem h0n56_arithmetic_row1 :
    (BiPoly.mul h0p37 h0p55).getD 1 []=h0p56.getD 1 [] := by
  decide +kernel

theorem h0n56_arithmetic_row2 :
    (BiPoly.mul h0p37 h0p55).getD 2 []=h0p56.getD 2 [] := by
  decide +kernel

theorem h0n56_arithmetic_row3 :
    (BiPoly.mul h0p37 h0p55).getD 3 []=h0p56.getD 3 [] := by
  decide +kernel

theorem h0n56_arithmetic_row4 :
    (BiPoly.mul h0p37 h0p55).getD 4 []=h0p56.getD 4 [] := by
  decide +kernel

theorem h0n56_arithmetic_row5 :
    (BiPoly.mul h0p37 h0p55).getD 5 []=h0p56.getD 5 [] := by
  decide +kernel

theorem h0n56_arithmetic_row6 :
    (BiPoly.mul h0p37 h0p55).getD 6 []=h0p56.getD 6 [] := by
  decide +kernel

theorem h0n56_arithmetic_row7 :
    (BiPoly.mul h0p37 h0p55).getD 7 []=h0p56.getD 7 [] := by
  decide +kernel

theorem h0n56_arithmetic_row8 :
    (BiPoly.mul h0p37 h0p55).getD 8 []=h0p56.getD 8 [] := by
  decide +kernel

theorem h0n56_arithmetic_row9 :
    (BiPoly.mul h0p37 h0p55).getD 9 []=h0p56.getD 9 [] := by
  decide +kernel

theorem h0n56_arithmetic_row10 :
    (BiPoly.mul h0p37 h0p55).getD 10 []=h0p56.getD 10 [] := by
  decide +kernel

theorem h0n56_arithmetic_row11 :
    (BiPoly.mul h0p37 h0p55).getD 11 []=h0p56.getD 11 [] := by
  decide +kernel

theorem h0n56_arithmetic_row12 :
    (BiPoly.mul h0p37 h0p55).getD 12 []=h0p56.getD 12 [] := by
  decide +kernel

theorem h0n56_arithmetic_row13 :
    (BiPoly.mul h0p37 h0p55).getD 13 []=h0p56.getD 13 [] := by
  decide +kernel

theorem h0n56_arithmetic_row14 :
    (BiPoly.mul h0p37 h0p55).getD 14 []=h0p56.getD 14 [] := by
  decide +kernel

theorem h0n56_arithmetic_row15 :
    (BiPoly.mul h0p37 h0p55).getD 15 []=h0p56.getD 15 [] := by
  decide +kernel

theorem h0n56_arithmetic_row16 :
    (BiPoly.mul h0p37 h0p55).getD 16 []=h0p56.getD 16 [] := by
  decide +kernel

theorem h0n56_arithmetic_row17 :
    (BiPoly.mul h0p37 h0p55).getD 17 []=h0p56.getD 17 [] := by
  decide +kernel

theorem h0n56_arithmetic_row18 :
    (BiPoly.mul h0p37 h0p55).getD 18 []=h0p56.getD 18 [] := by
  decide +kernel

theorem h0n56_arithmetic_row19 :
    (BiPoly.mul h0p37 h0p55).getD 19 []=h0p56.getD 19 [] := by
  decide +kernel

theorem h0n56_arithmetic_row20 :
    (BiPoly.mul h0p37 h0p55).getD 20 []=h0p56.getD 20 [] := by
  decide +kernel

theorem h0n56_arithmetic_row21 :
    (BiPoly.mul h0p37 h0p55).getD 21 []=h0p56.getD 21 [] := by
  decide +kernel

theorem h0n56_arithmetic_row22 :
    (BiPoly.mul h0p37 h0p55).getD 22 []=h0p56.getD 22 [] := by
  decide +kernel

theorem h0n56_arithmetic_row23 :
    (BiPoly.mul h0p37 h0p55).getD 23 []=h0p56.getD 23 [] := by
  decide +kernel

theorem h0n56_arithmetic_row24 :
    (BiPoly.mul h0p37 h0p55).getD 24 []=h0p56.getD 24 [] := by
  decide +kernel

theorem h0n56_arithmetic : BiPoly.mul h0p37 h0p55=h0p56 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<25 at hk
    have hf : ∀ j : Fin 25, (BiPoly.mul h0p37 h0p55).getD j.val []=h0p56.getD j.val [] :=
      (fun j => Fin.cases h0n56_arithmetic_row0 (fun j => Fin.cases h0n56_arithmetic_row1 (fun j => Fin.cases h0n56_arithmetic_row2 (fun j => Fin.cases h0n56_arithmetic_row3 (fun j => Fin.cases h0n56_arithmetic_row4 (fun j => Fin.cases h0n56_arithmetic_row5 (fun j => Fin.cases h0n56_arithmetic_row6 (fun j => Fin.cases h0n56_arithmetic_row7 (fun j => Fin.cases h0n56_arithmetic_row8 (fun j => Fin.cases h0n56_arithmetic_row9 (fun j => Fin.cases h0n56_arithmetic_row10 (fun j => Fin.cases h0n56_arithmetic_row11 (fun j => Fin.cases h0n56_arithmetic_row12 (fun j => Fin.cases h0n56_arithmetic_row13 (fun j => Fin.cases h0n56_arithmetic_row14 (fun j => Fin.cases h0n56_arithmetic_row15 (fun j => Fin.cases h0n56_arithmetic_row16 (fun j => Fin.cases h0n56_arithmetic_row17 (fun j => Fin.cases h0n56_arithmetic_row18 (fun j => Fin.cases h0n56_arithmetic_row19 (fun j => Fin.cases h0n56_arithmetic_row20 (fun j => Fin.cases h0n56_arithmetic_row21 (fun j => Fin.cases h0n56_arithmetic_row22 (fun j => Fin.cases h0n56_arithmetic_row23 (fun j => Fin.cases h0n56_arithmetic_row24 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n56 : h0e56.toBi mapPolyEnv=h0p56 := by
  change BiPoly.mul (h0e37.toBi mapPolyEnv) (h0e55.toBi mapPolyEnv)=h0p56
  rw [h0n37, h0n55]
  exact h0n56_arithmetic

#print axioms h0n56_arithmetic
end StackSorting.RationalLift
