import BivariateRowEquality
import Horner4Base
import Horner4Node133
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p159 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1316344772297362175999), (Int.negSucc 9377866980764241010559), (Int.negSucc 1546964962492488632639), (Int.ofNat 81875702065651063050240), (Int.ofNat 17244027859355366382720), (Int.negSucc 247623593153269393342079), (Int.ofNat 157425794707985406187200)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 16420319656682079234240), (Int.ofNat 111719391607727558965728), (Int.negSucc 4139921923928170225631), (Int.negSucc 979091697131776176790463), (Int.negSucc 73632629890448711793791), (Int.ofNat 2803697676634603906637280), (Int.negSucc 2005500047749820876513375), (Int.ofNat 164984704471465161523200)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 97273515028184219701439), (Int.negSucc 620356205444758428803327), (Int.ofNat 182777587836623082400752), (Int.ofNat 5406857191245182235745968), (Int.negSucc 298928748151958918874335), (Int.negSucc 14066878764695895083557151), (Int.ofNat 10448214761177639049065904), (Int.negSucc 1208688157990700617372559), (Int.ofNat 65679919537942396138752)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 363688402736111889138480), (Int.ofNat 2123138142767165297849784), (Int.negSucc 1292391217982194921079135), (Int.negSucc 18141795446318496432480167), (Int.ofNat 2978061735947004018877968), (Int.ofNat 40660584117450614086659624), (Int.negSucc 27916335956879169022651391), (Int.ofNat 1988270155930144220590536), (Int.negSucc 137448993657077430761951), (Int.ofNat 12092924030352010592256)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 960971794171458921525599), (Int.negSucc 4990447078135718793845039), (Int.ofNat 4896038328059525899253616), (Int.ofNat 41127448377931851183323040), (Int.negSucc 9060804650611435473458063), (Int.negSucc 73560665422708180847334287), (Int.ofNat 34291991073574747400315760), (Int.ofNat 8155376189808452145052704), (Int.negSucc 1240640789171101665099695), (Int.ofNat 48187438959659779896192), (Int.ofNat 971263444141558674432)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1902331594538060796998640), (Int.ofNat 8497568956769756048884104), (Int.negSucc 12050911157361516091560095), (Int.negSucc 66658033505045359957063391), (Int.ofNat 11252735978858590800127104), (Int.ofNat 84054684745150182715379112), (Int.ofNat 11916018367990351019558496), (Int.negSucc 42905433724070216382052847), (Int.ofNat 5119245936387331800939504), (Int.negSucc 330352685934011130982463), (Int.ofNat 12240529248310558117632), (Int.ofNat 22037340803221979136)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2916484421344948714024439), (Int.negSucc 10772687695796348398553411), (Int.ofNat 20873624489277632139563028), (Int.ofNat 80581537944178028473462524), (Int.ofNat 6733015889003151485658084), (Int.negSucc 56313049591127883791161835), (Int.negSucc 109745628797618556964866899), (Int.ofNat 78164012372992364573020260), (Int.negSucc 1806339012714320460600635), (Int.negSucc 244158474678955903976255), (Int.ofNat 2366323146879257628288), (Int.ofNat 735639430861967088384), (Int.negSucc 135509178398330879)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3529618920507326808990240), (Int.ofNat 10283304362166456318861912), (Int.negSucc 26556487517533124392608347), (Int.negSucc 76701857391462234103180343), (Int.negSucc 50387167549378895594560307), (Int.ofNat 13508076535542167605205832), (Int.ofNat 172273027864799447951987772), (Int.negSucc 44170680639299285112838847), (Int.negSucc 25267519547813663631526139), (Int.ofNat 3227666486625715136508792), (Int.negSucc 170885633124133553945471), (Int.ofNat 4111711177320365212800), (Int.ofNat 1785320652549118464)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3406536700121771952055559), (Int.negSucc 7379722241928902973648275), (Int.ofNat 25509484181035177782389604), (Int.ofNat 63151583138090790139727532), (Int.ofNat 96942399568228620533345832), (Int.ofNat 15715968650879518627302024), (Int.negSucc 123324250988287274688926027), (Int.negSucc 72029050256097116955630035), (Int.ofNat 58872362128610935067027640), (Int.negSucc 3494378313331293606037595), (Int.ofNat 53822462657396150814480), (Int.negSucc 1769916094484417835263), (Int.ofNat 109501936379622008064)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2632022112581219823411600), (Int.ofNat 3923360238794235111190224), (Int.negSucc 18960783103209938156707715), (Int.negSucc 50761467963412921540534103), (Int.negSucc 114386126795407755928082159), (Int.negSucc 36107639725168272580914095), (Int.ofNat 13256355434831498370733020), (Int.ofNat 158169369536088452846613576), (Int.negSucc 42421524019566588820992455), (Int.negSucc 8171332509006310043467367), (Int.ofNat 989684139710673630531504), (Int.negSucc 39260014282887496996319), (Int.ofNat 628292584853009508096)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1626010065710021597091119), (Int.negSucc 1501397505625269797533151), (Int.ofNat 11298203470557787735628388), (Int.ofNat 41407581397910204060914752), (Int.ofNat 96244834577818722726149424), (Int.ofNat 60904731663032823689931864), (Int.ofNat 51516637813913037905283516), (Int.negSucc 116521883210706586717366187), (Int.negSucc 30930846112445206604523083), (Int.ofNat 22590911914197263772915492), (Int.negSucc 1177986822720712553772899), (Int.ofNat 7666973106797826940896), (Int.ofNat 309408149868578886528)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 798401703335075720119440), (Int.ofNat 404189670893943437055000), (Int.negSucc 5749407402160273170478055), (Int.negSucc 31475262633782659646665139), (Int.negSucc 63328875042582801697637915), (Int.negSucc 77801346441931014229509539), (Int.negSucc 50548771563697552188464783), (Int.ofNat 8246835485909089821687780), (Int.ofNat 80298475481830650162710472), (Int.negSucc 15197102605623083064281243), (Int.negSucc 1848828181438527496377947), (Int.ofNat 167732585007650648271504), (Int.negSucc 3947964086551622816735)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 308134096893425254231439), (Int.negSucc 92144869893640790091719), (Int.ofNat 2726306814139664794131312), (Int.ofNat 20282815364344646046008904), (Int.ofNat 36285075050493476723415984), (Int.ofNat 69734769596595927190542492), (Int.ofNat 35333569227363028023948444), (Int.ofNat 49147686351857877212409624), (Int.negSucc 53119886953809576119158727), (Int.negSucc 10871919792910912727211155), (Int.ofNat 4642814210216794096198104), (Int.negSucc 115887724705626148336643), (Int.negSucc 3244924598787313667567)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 91829124351173936902320), (Int.ofNat 37636711995723430948920), (Int.negSucc 1260093834865646107514351), (Int.negSucc 10612578415444818027529535), (Int.negSucc 20085418557290786708043359), (Int.negSucc 43999224273783002885505875), (Int.negSucc 31368617070050490467117111), (Int.negSucc 39334488319819090071592271), (Int.negSucc 1442391427172855309448167), (Int.ofNat 23061250966591007594534916), (Int.negSucc 2070995088838152875196563), (Int.negSucc 303192905838335237694815), (Int.ofNat 12271405049499733739424)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 20565838964409164954999), (Int.negSucc 22004285133354063101171), (Int.ofNat 537367452067899334731636), (Int.ofNat 4477038103900678555589220), (Int.ofNat 10839215021481792088941636), (Int.ofNat 20314092676104913599635400), (Int.ofNat 26952084403767240939935352), (Int.ofNat 16617622705397621196181128), (Int.ofNat 22852819200468987857264904), (Int.negSucc 11353998720293781327415691), (Int.negSucc 2688626095764630541248455), (Int.ofNat 422457782801136030943776), (Int.ofNat 4900880127455791729920)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3317662246670915266080), (Int.ofNat 9441975926288325844728), (Int.negSucc 191506734603854421503507), (Int.negSucc 1534139534100646052968751), (Int.negSucc 5221347867716811988207211), (Int.negSucc 7586362235455713661504067), (Int.negSucc 16222793878772472261168683), (Int.negSucc 7820719418857400429629499), (Int.negSucc 14409410139085775821062875), (Int.negSucc 2695725876442111394453351), (Int.ofNat 3364095257029854544458744), (Int.ofNat 12788961632012418048936), (Int.negSucc 21517009004900574495071)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 359351223327550104839), (Int.negSucc 2647766611918355374835), (Int.ofNat 52680183862424263021404), (Int.ofNat 429963740243043802054884), (Int.ofNat 2052174355206092757069264), (Int.ofNat 2776577174157997783554732), (Int.ofNat 6359171259240629786315448), (Int.ofNat 5545101476001633142599900), (Int.ofNat 4244254309829380208610456), (Int.ofNat 5424784376448094397403984), (Int.negSucc 827198643188752413413615), (Int.negSucc 316515300843596474336399), (Int.ofNat 4515221904666360268032)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 22912601795260961040), (Int.ofNat 473514757961104392336), (Int.negSucc 10532581281959103293291), (Int.negSucc 97888858187960710491911), (Int.negSucc 622379812078424264282567), (Int.negSucc 1093107163259915266749227), (Int.negSucc 1638944155498527661251131), (Int.negSucc 3028254721188292548634463), (Int.negSucc 1012478794539446160631367), (Int.negSucc 2444050769365401933475367), (Int.negSucc 718916801755068142871183), (Int.ofNat 173365647632497746463824), (Int.ofNat 14323696880100957089856)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 624324272495156639), (Int.negSucc 49825090019285970407), (Int.ofNat 1431670429318197903588), (Int.ofNat 17539035210298022687568), (Int.ofNat 140140650697793447127192), (Int.ofNat 390448872070297091374860), (Int.ofNat 331635984680370657739032), (Int.ofNat 975749125780170018367488), (Int.ofNat 535122323522261016411456), (Int.ofNat 469191443849418847320432), (Int.ofNat 588803040890497580483088), (Int.ofNat 27030385289855818325376), (Int.negSucc 9100866331778535779327)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2374961438493939168), (Int.negSucc 118234199930808765671), (Int.negSucc 2315330321021838075419), (Int.negSucc 22479177475563896543651), (Int.negSucc 104694072855156372920039), (Int.negSucc 88127181758166001508951), (Int.negSucc 167136320689448471635751), (Int.negSucc 256608955160504521890047), (Int.negSucc 39941719475241760650143), (Int.negSucc 169327901378375479707551), (Int.negSucc 57980533947695913960287), (Int.negSucc 1179730350188168457599)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4492818804603345120), (Int.ofNat 199107909232197499368), (Int.ofNat 2414284592258027005848), (Int.ofNat 18944082227475975734352), (Int.ofNat 28626480701486242726896), (Int.ofNat 11581300250553007717200), (Int.ofNat 63765495040758456812256), (Int.ofNat 14850652808722036349376), (Int.ofNat 17364418188380631438912), (Int.ofNat 21895914911351853487104), (Int.ofNat 2752073027939761991424)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 8327821711294284767), (Int.negSucc 154731978411944408855), (Int.negSucc 2101569976745077735223), (Int.negSucc 6597608347203529899023), (Int.negSucc 641505656024770742063), (Int.negSucc 6462225053752555548287), (Int.negSucc 7150103947651053672575), (Int.ofNat 951362245680322367232), (Int.negSucc 3354375654574194790079), (Int.negSucc 922300075408725423359)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4422376437151791168), (Int.ofNat 118902111772973283216), (Int.ofNat 858663962168885571024), (Int.ofNat 489890495157252913152), (Int.negSucc 252068848372028692223), (Int.ofNat 1349215799112676422720), (Int.negSucc 292359677868227151935), (Int.ofNat 165507733570752967680), (Int.ofNat 101162316504551731200)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1846066467578463359), (Int.negSucc 50521939956939199391), (Int.negSucc 110799048377073560543), (Int.ofNat 102683642861443781376), (Int.negSucc 96544766663781450047), (Int.ofNat 17504090350629822720)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 467936950304040192), (Int.ofNat 7527727986340590144), (Int.negSucc 4901765673946887359)]]

theorem h4n159_arithmetic_row0 :
    (BiPoly.mul h4p158 h4p133).getD 0 []=h4p159.getD 0 [] := by
  decide +kernel

theorem h4n159_arithmetic_row1 :
    (BiPoly.mul h4p158 h4p133).getD 1 []=h4p159.getD 1 [] := by
  decide +kernel

theorem h4n159_arithmetic_row2 :
    (BiPoly.mul h4p158 h4p133).getD 2 []=h4p159.getD 2 [] := by
  decide +kernel

theorem h4n159_arithmetic_row3 :
    (BiPoly.mul h4p158 h4p133).getD 3 []=h4p159.getD 3 [] := by
  decide +kernel

theorem h4n159_arithmetic_row4 :
    (BiPoly.mul h4p158 h4p133).getD 4 []=h4p159.getD 4 [] := by
  decide +kernel

theorem h4n159_arithmetic_row5 :
    (BiPoly.mul h4p158 h4p133).getD 5 []=h4p159.getD 5 [] := by
  decide +kernel

theorem h4n159_arithmetic_row6 :
    (BiPoly.mul h4p158 h4p133).getD 6 []=h4p159.getD 6 [] := by
  decide +kernel

theorem h4n159_arithmetic_row7 :
    (BiPoly.mul h4p158 h4p133).getD 7 []=h4p159.getD 7 [] := by
  decide +kernel

theorem h4n159_arithmetic_row8 :
    (BiPoly.mul h4p158 h4p133).getD 8 []=h4p159.getD 8 [] := by
  decide +kernel

theorem h4n159_arithmetic_row9 :
    (BiPoly.mul h4p158 h4p133).getD 9 []=h4p159.getD 9 [] := by
  decide +kernel

theorem h4n159_arithmetic_row10 :
    (BiPoly.mul h4p158 h4p133).getD 10 []=h4p159.getD 10 [] := by
  decide +kernel

theorem h4n159_arithmetic_row11 :
    (BiPoly.mul h4p158 h4p133).getD 11 []=h4p159.getD 11 [] := by
  decide +kernel

theorem h4n159_arithmetic_row12 :
    (BiPoly.mul h4p158 h4p133).getD 12 []=h4p159.getD 12 [] := by
  decide +kernel

theorem h4n159_arithmetic_row13 :
    (BiPoly.mul h4p158 h4p133).getD 13 []=h4p159.getD 13 [] := by
  decide +kernel

theorem h4n159_arithmetic_row14 :
    (BiPoly.mul h4p158 h4p133).getD 14 []=h4p159.getD 14 [] := by
  decide +kernel

theorem h4n159_arithmetic_row15 :
    (BiPoly.mul h4p158 h4p133).getD 15 []=h4p159.getD 15 [] := by
  decide +kernel

theorem h4n159_arithmetic_row16 :
    (BiPoly.mul h4p158 h4p133).getD 16 []=h4p159.getD 16 [] := by
  decide +kernel

theorem h4n159_arithmetic_row17 :
    (BiPoly.mul h4p158 h4p133).getD 17 []=h4p159.getD 17 [] := by
  decide +kernel

theorem h4n159_arithmetic_row18 :
    (BiPoly.mul h4p158 h4p133).getD 18 []=h4p159.getD 18 [] := by
  decide +kernel

theorem h4n159_arithmetic_row19 :
    (BiPoly.mul h4p158 h4p133).getD 19 []=h4p159.getD 19 [] := by
  decide +kernel

theorem h4n159_arithmetic_row20 :
    (BiPoly.mul h4p158 h4p133).getD 20 []=h4p159.getD 20 [] := by
  decide +kernel

theorem h4n159_arithmetic_row21 :
    (BiPoly.mul h4p158 h4p133).getD 21 []=h4p159.getD 21 [] := by
  decide +kernel

theorem h4n159_arithmetic_row22 :
    (BiPoly.mul h4p158 h4p133).getD 22 []=h4p159.getD 22 [] := by
  decide +kernel

theorem h4n159_arithmetic_row23 :
    (BiPoly.mul h4p158 h4p133).getD 23 []=h4p159.getD 23 [] := by
  decide +kernel

theorem h4n159_arithmetic_row24 :
    (BiPoly.mul h4p158 h4p133).getD 24 []=h4p159.getD 24 [] := by
  decide +kernel

theorem h4n159_arithmetic : BiPoly.mul h4p158 h4p133=h4p159 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<25 at hk
    have hf : ∀ j : Fin 25, (BiPoly.mul h4p158 h4p133).getD j.val []=h4p159.getD j.val [] :=
      (fun j => Fin.cases h4n159_arithmetic_row0 (fun j => Fin.cases h4n159_arithmetic_row1 (fun j => Fin.cases h4n159_arithmetic_row2 (fun j => Fin.cases h4n159_arithmetic_row3 (fun j => Fin.cases h4n159_arithmetic_row4 (fun j => Fin.cases h4n159_arithmetic_row5 (fun j => Fin.cases h4n159_arithmetic_row6 (fun j => Fin.cases h4n159_arithmetic_row7 (fun j => Fin.cases h4n159_arithmetic_row8 (fun j => Fin.cases h4n159_arithmetic_row9 (fun j => Fin.cases h4n159_arithmetic_row10 (fun j => Fin.cases h4n159_arithmetic_row11 (fun j => Fin.cases h4n159_arithmetic_row12 (fun j => Fin.cases h4n159_arithmetic_row13 (fun j => Fin.cases h4n159_arithmetic_row14 (fun j => Fin.cases h4n159_arithmetic_row15 (fun j => Fin.cases h4n159_arithmetic_row16 (fun j => Fin.cases h4n159_arithmetic_row17 (fun j => Fin.cases h4n159_arithmetic_row18 (fun j => Fin.cases h4n159_arithmetic_row19 (fun j => Fin.cases h4n159_arithmetic_row20 (fun j => Fin.cases h4n159_arithmetic_row21 (fun j => Fin.cases h4n159_arithmetic_row22 (fun j => Fin.cases h4n159_arithmetic_row23 (fun j => Fin.cases h4n159_arithmetic_row24 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n159 : h4e159.toBi mapPolyEnv=h4p159 := by
  change BiPoly.mul (h4e158.toBi mapPolyEnv) (h4e133.toBi mapPolyEnv)=h4p159
  rw [h4n158, h4n133]
  exact h4n159_arithmetic

#print axioms h4n159_arithmetic
end StackSorting.RationalLift
