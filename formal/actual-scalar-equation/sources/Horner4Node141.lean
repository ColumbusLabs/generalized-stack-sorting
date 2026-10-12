import BivariateRowEquality
import Horner4Base
import Horner4Node140
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p141 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2961775737669064895999), (Int.negSucc 25357753329618823061759), (Int.negSucc 52149766494820050270719), (Int.ofNat 49821387826186664133120), (Int.ofNat 170938669006657314777600), (Int.negSucc 18681723440603032193279), (Int.negSucc 110045215718203390732799)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 37278233401786876535040), (Int.ofNat 315879292686762752335488), (Int.ofNat 638772828217232532815232), (Int.negSucc 595522724269002840253439), (Int.negSucc 1897736065957248552525311), (Int.ofNat 382287189582898364612736), (Int.ofNat 1064652446944848455247744), (Int.negSucc 57299157368494427001599)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 222894734669093980460159), (Int.negSucc 1850599750247744946754751), (Int.negSucc 3666717252799338036307391), (Int.ofNat 3211387301548558335354624), (Int.ofNat 9795277903211844140210688), (Int.negSucc 2341807369354202610246335), (Int.negSucc 4429144161810173619873215), (Int.ofNat 68120019864435549635712), (Int.ofNat 12493153034645321636352)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 841438682866684763674560), (Int.ofNat 6769719455251835736165600), (Int.ofNat 13165675399437326157199680), (Int.negSucc 9886443813168481508386463), (Int.negSucc 30954396843281305907860607), (Int.ofNat 6213642511675431948737184), (Int.ofNat 10358923323961633818376512), (Int.ofNat 1992968124396917285168928), (Int.negSucc 317277689255110526717375), (Int.ofNat 13259797819695322841088)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2245855644540450195223679), (Int.negSucc 17329171867233525467357759), (Int.negSucc 33378569432907215706393983), (Int.ofNat 17624551588410784136864832), (Int.ofNat 66610383790079725413752448), (Int.negSucc 3461660016799212677894975), (Int.negSucc 14964543425313163556183807), (Int.negSucc 10985456053945794242414015), (Int.ofNat 1402082114349833984541312), (Int.negSucc 88385922562183147395071), (Int.ofNat 2825094926879531311104)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4493421941513570169281280), (Int.ofNat 33008091743236029626185344), (Int.ofNat 64083755048318812136998944), (Int.negSucc 12435285917655029848841567), (Int.negSucc 102068628495372408017068703), (Int.negSucc 26133145936088792621679359), (Int.ofNat 13308551011037796601784544), (Int.ofNat 26369175444388233465156768), (Int.negSucc 1052790648081169542029279), (Int.negSucc 40888008310199150445119), (Int.negSucc 1365219353110831898111), (Int.ofNat 184959914300940201984)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 6967486021305845927213279), (Int.negSucc 48635849574530039561996303), (Int.negSucc 97675600623572093458285295), (Int.negSucc 22880582095183586528519087), (Int.ofNat 109657173145929142725881424), (Int.ofNat 90764159166247609180887408), (Int.negSucc 1862893614939442919040527), (Int.negSucc 32242600307321261931431951), (Int.negSucc 7499904929162028162852911), (Int.ofNat 1144808672521041924489504), (Int.negSucc 60740181234262129606271), (Int.ofNat 1120077919747319334912), (Int.negSucc 993733974921093119)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 8535831283503302264542080), (Int.ofNat 56978191340003895374981664), (Int.ofNat 122196104104745957989689360), (Int.ofNat 86199118898515384903173504), (Int.negSucc 67995407337776624538085679), (Int.negSucc 155118328944960489344123615), (Int.negSucc 26524318252390012192128911), (Int.ofNat 12967540696438558882095456), (Int.ofNat 23871259909063749279287664), (Int.negSucc 1960558606172473307853983), (Int.ofNat 68942216554356989485440), (Int.negSucc 2307664201558196378879), (Int.ofNat 32244315332324299776)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 8347933519196964135919199), (Int.negSucc 54199643701520993143027247), (Int.negSucc 128261467228595777546787791), (Int.negSucc 147420692427680855544999023), (Int.negSucc 16497728752681280788086815), (Int.ofNat 159003972769650101155181088), (Int.ofNat 73562987236357840172911632), (Int.ofNat 20019983759962408811573712), (Int.negSucc 28628119336076591977633247), (Int.negSucc 2203683940745109850875983), (Int.ofNat 384395204304926395204896), (Int.negSucc 15668114130302692970879), (Int.ofNat 206224549735062219264)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 6543568783239944973508800), (Int.ofNat 42548490953753869473490368), (Int.ofNat 114261543075247619409326448), (Int.ofNat 172814153466328938952936416), (Int.ofNat 105631107901929587196184896), (Int.negSucc 82482843871738776235746815), (Int.negSucc 111635902339828720382680271), (Int.negSucc 41904510919677290294225279), (Int.ofNat 6690809329685826578820864), (Int.ofNat 10698233449557207361190976), (Int.negSucc 791611953953299293909599), (Int.ofNat 18275271268517726716224), (Int.negSucc 118633373660095741439)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 4106531817521204973577919), (Int.negSucc 27873463527713370648102335), (Int.negSucc 86616105820610285096528687), (Int.negSucc 154863034278565327879281695), (Int.negSucc 154485492056277524590979519), (Int.negSucc 26467073871376018853656223), (Int.ofNat 99258357864675514763481840), (Int.ofNat 47041095718709351894405808), (Int.ofNat 22517905901333817066459408), (Int.negSucc 11938223152516499540268047), (Int.negSucc 459975114136293994657295), (Int.ofNat 74929953360222865585440), (Int.negSucc 2019258468700780061951)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2051224054157221359422400), (Int.ofNat 15301627619615252510037408), (Int.ofNat 55644584585089204357534080), (Int.ofNat 112433244103400510172542544), (Int.ofNat 147321217078529552486305776), (Int.ofNat 99683778624016513230724176), (Int.negSucc 35629251218773460784045791), (Int.negSucc 41358449096194281270827759), (Int.negSucc 30127353318644604944571935), (Int.ofNat 604330680562344466120944), (Int.ofNat 2606807277744264125258256), (Int.negSucc 112512198294002868762239), (Int.negSucc 151317145482256234943)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 806521349078467544427839), (Int.negSucc 7008130096353027779844383), (Int.negSucc 30028004280144024829835615), (Int.negSucc 68681525088655861469811071), (Int.negSucc 105422624206228179130476095), (Int.negSucc 109845239940679059209630159), (Int.negSucc 30716913873776564693656367), (Int.ofNat 24001843456497081519504000), (Int.ofNat 17978756599188031846046976), (Int.ofNat 10301793795483343170529968), (Int.negSucc 2235530039005871573111135), (Int.negSucc 113881621174417153341935), (Int.ofNat 7710577716437464140576)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 245245034696631074375040), (Int.ofNat 2641741233839786821600512), (Int.ofNat 13438724170496447360139264), (Int.ofNat 35918074383528604141964448), (Int.ofNat 60504645352976915075546400), (Int.ofNat 78895512967868644651929936), (Int.ofNat 57455063810692956296665632), (Int.ofNat 724287148112935120096800), (Int.negSucc 5187385157239426247962847), (Int.negSucc 9532866901703503187826863), (Int.negSucc 649971597032949068781263), (Int.ofNat 305641629844022944999584), (Int.negSucc 1130104850632505558783)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 56125024362264249306719), (Int.negSucc 801632004821642413805327), (Int.negSucc 4904793230799084285570191), (Int.negSucc 15967789711710532275181103), (Int.negSucc 29324448772025985326755151), (Int.negSucc 42183891856557202313886623), (Int.negSucc 46556151561874882573732511), (Int.negSucc 17421976314223015999735295), (Int.negSucc 1378796422778746119659519), (Int.ofNat 2764395390513059306030448), (Int.ofNat 2182343039999009151922944), (Int.negSucc 108612050451965552974463), (Int.negSucc 13814612568749933497727)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 9264377375122099703040), (Int.ofNat 189896778775245290226912), (Int.ofNat 1428678369129024471754512), (Int.ofNat 5871261800823269200617312), (Int.ofNat 12376442691243027175037328), (Int.ofNat 18092458766700840994191216), (Int.ofNat 24554128115041252887407760), (Int.ofNat 18285398807854770566521776), (Int.ofNat 4300268922636119319891024), (Int.ofNat 1141443978130873216646784), (Int.negSucc 1203344056785170167248671), (Int.negSucc 173804470680830986924127), (Int.ofNat 8077253448264732091584)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1027743087190200852959), (Int.negSucc 33668501841374368282991), (Int.negSucc 322922800383255763199567), (Int.negSucc 1718391087043302195712943), (Int.negSucc 4500605764462937571029951), (Int.negSucc 6697440422298375765379343), (Int.negSucc 9332222069625524702561951), (Int.negSucc 10631649909773756088856943), (Int.negSucc 4605316573415207266051775), (Int.negSucc 1535008458251226415157567), (Int.negSucc 54027470693635179801407), (Int.ofNat 170677574464609146969792), (Int.ofNat 7834472210104045854336)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 67104541563113142720), (Int.ofNat 4193949981237395959872), (Int.ofNat 54500351584815956027376), (Int.ofNat 383139258974072952097248), (Int.ofNat 1341516478630825973723616), (Int.ofNat 2239390381752908863344720), (Int.ofNat 2786531298450340326555600), (Int.ofNat 3973639423611688403410656), (Int.ofNat 2949580945562358194026272), (Int.ofNat 996509630977555679790048), (Int.ofNat 360324880217370052111872), (Int.negSucc 25823769330755318182847), (Int.negSucc 8666419869655271457407)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1865796676422307199), (Int.negSucc 327735182544196366943), (Int.negSucc 6476591240069496313103), (Int.negSucc 61749443489807778988031), (Int.negSucc 306553529355479275521599), (Int.negSucc 654335556497480298049775), (Int.negSucc 742784638100519573881919), (Int.negSucc 998693531315036489702015), (Int.negSucc 1176271387696257118747775), (Int.negSucc 527908824942006571821503), (Int.negSucc 205015908269580658870463), (Int.negSucc 35884726931975448115583), (Int.ofNat 896914881427499315712)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 12145629966367616640), (Int.ofNat 486695578340116459296), (Int.ofNat 6677521298088236802288), (Int.ofNat 49858481820892848978096), (Int.ofNat 151935042422333080405440), (Int.ofNat 192113501829285733823520), (Int.ofNat 182746812755904803146080), (Int.ofNat 287488727719368552213696), (Int.ofNat 208380111259505777108352), (Int.ofNat 73695892556511429763968), (Int.ofNat 23826167865767893221504), (Int.ofNat 2026869668390005638912)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 17600298816218451839), (Int.negSucc 424635305391379281311), (Int.negSucc 5228104669456952884319), (Int.negSucc 25188441354984664590911), (Int.negSucc 43698204979995696587711), (Int.negSucc 31477680244382058224063), (Int.negSucc 39994853582726860575743), (Int.negSucc 52168473120342217932287), (Int.negSucc 21603470233403612272895), (Int.negSucc 7157446038643566574079), (Int.negSucc 1048056312917566457855)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 11512072781552769408), (Int.ofNat 293420142820735600608), (Int.ofNat 2638646261485116269472), (Int.ofNat 7267960075711219360128), (Int.ofNat 6264486132547290560064), (Int.ofNat 2704407037280870825088), (Int.ofNat 6977778452147466192384), (Int.ofNat 4733002045697985110016), (Int.ofNat 1371020564393657641728), (Int.ofNat 201205534818016728576)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 4985412560434725119), (Int.negSucc 139641904635363519551), (Int.negSucc 744198340748025191615), (Int.negSucc 1048742343772458678143), (Int.negSucc 155651599978798851071), (Int.negSucc 250621774663712792831), (Int.negSucc 600819911639500338431), (Int.negSucc 186629993538023941631), (Int.negSucc 13488308867273564159)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1513713911966784000), (Int.ofNat 36125437023735129216), (Int.ofNat 100831780359440548992), (Int.ofNat 40955872046285041920), (Int.negSucc 44741147868680378111), (Int.ofNat 30524466189835270656), (Int.ofNat 13488308867273564160)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 207971977912906751), (Int.negSucc 3761600838643853567), (Int.negSucc 4512751243881907967), (Int.ofNat 4357125043508344320)]]

theorem h4n141_arithmetic_row0 :
    (BiPoly.mul h4p5 h4p140).getD 0 []=h4p141.getD 0 [] := by
  decide +kernel

theorem h4n141_arithmetic_row1 :
    (BiPoly.mul h4p5 h4p140).getD 1 []=h4p141.getD 1 [] := by
  decide +kernel

theorem h4n141_arithmetic_row2 :
    (BiPoly.mul h4p5 h4p140).getD 2 []=h4p141.getD 2 [] := by
  decide +kernel

theorem h4n141_arithmetic_row3 :
    (BiPoly.mul h4p5 h4p140).getD 3 []=h4p141.getD 3 [] := by
  decide +kernel

theorem h4n141_arithmetic_row4 :
    (BiPoly.mul h4p5 h4p140).getD 4 []=h4p141.getD 4 [] := by
  decide +kernel

theorem h4n141_arithmetic_row5 :
    (BiPoly.mul h4p5 h4p140).getD 5 []=h4p141.getD 5 [] := by
  decide +kernel

theorem h4n141_arithmetic_row6 :
    (BiPoly.mul h4p5 h4p140).getD 6 []=h4p141.getD 6 [] := by
  decide +kernel

theorem h4n141_arithmetic_row7 :
    (BiPoly.mul h4p5 h4p140).getD 7 []=h4p141.getD 7 [] := by
  decide +kernel

theorem h4n141_arithmetic_row8 :
    (BiPoly.mul h4p5 h4p140).getD 8 []=h4p141.getD 8 [] := by
  decide +kernel

theorem h4n141_arithmetic_row9 :
    (BiPoly.mul h4p5 h4p140).getD 9 []=h4p141.getD 9 [] := by
  decide +kernel

theorem h4n141_arithmetic_row10 :
    (BiPoly.mul h4p5 h4p140).getD 10 []=h4p141.getD 10 [] := by
  decide +kernel

theorem h4n141_arithmetic_row11 :
    (BiPoly.mul h4p5 h4p140).getD 11 []=h4p141.getD 11 [] := by
  decide +kernel

theorem h4n141_arithmetic_row12 :
    (BiPoly.mul h4p5 h4p140).getD 12 []=h4p141.getD 12 [] := by
  decide +kernel

theorem h4n141_arithmetic_row13 :
    (BiPoly.mul h4p5 h4p140).getD 13 []=h4p141.getD 13 [] := by
  decide +kernel

theorem h4n141_arithmetic_row14 :
    (BiPoly.mul h4p5 h4p140).getD 14 []=h4p141.getD 14 [] := by
  decide +kernel

theorem h4n141_arithmetic_row15 :
    (BiPoly.mul h4p5 h4p140).getD 15 []=h4p141.getD 15 [] := by
  decide +kernel

theorem h4n141_arithmetic_row16 :
    (BiPoly.mul h4p5 h4p140).getD 16 []=h4p141.getD 16 [] := by
  decide +kernel

theorem h4n141_arithmetic_row17 :
    (BiPoly.mul h4p5 h4p140).getD 17 []=h4p141.getD 17 [] := by
  decide +kernel

theorem h4n141_arithmetic_row18 :
    (BiPoly.mul h4p5 h4p140).getD 18 []=h4p141.getD 18 [] := by
  decide +kernel

theorem h4n141_arithmetic_row19 :
    (BiPoly.mul h4p5 h4p140).getD 19 []=h4p141.getD 19 [] := by
  decide +kernel

theorem h4n141_arithmetic_row20 :
    (BiPoly.mul h4p5 h4p140).getD 20 []=h4p141.getD 20 [] := by
  decide +kernel

theorem h4n141_arithmetic_row21 :
    (BiPoly.mul h4p5 h4p140).getD 21 []=h4p141.getD 21 [] := by
  decide +kernel

theorem h4n141_arithmetic_row22 :
    (BiPoly.mul h4p5 h4p140).getD 22 []=h4p141.getD 22 [] := by
  decide +kernel

theorem h4n141_arithmetic_row23 :
    (BiPoly.mul h4p5 h4p140).getD 23 []=h4p141.getD 23 [] := by
  decide +kernel

theorem h4n141_arithmetic_row24 :
    (BiPoly.mul h4p5 h4p140).getD 24 []=h4p141.getD 24 [] := by
  decide +kernel

theorem h4n141_arithmetic : BiPoly.mul h4p5 h4p140=h4p141 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<25 at hk
    have hf : ∀ j : Fin 25, (BiPoly.mul h4p5 h4p140).getD j.val []=h4p141.getD j.val [] :=
      (fun j => Fin.cases h4n141_arithmetic_row0 (fun j => Fin.cases h4n141_arithmetic_row1 (fun j => Fin.cases h4n141_arithmetic_row2 (fun j => Fin.cases h4n141_arithmetic_row3 (fun j => Fin.cases h4n141_arithmetic_row4 (fun j => Fin.cases h4n141_arithmetic_row5 (fun j => Fin.cases h4n141_arithmetic_row6 (fun j => Fin.cases h4n141_arithmetic_row7 (fun j => Fin.cases h4n141_arithmetic_row8 (fun j => Fin.cases h4n141_arithmetic_row9 (fun j => Fin.cases h4n141_arithmetic_row10 (fun j => Fin.cases h4n141_arithmetic_row11 (fun j => Fin.cases h4n141_arithmetic_row12 (fun j => Fin.cases h4n141_arithmetic_row13 (fun j => Fin.cases h4n141_arithmetic_row14 (fun j => Fin.cases h4n141_arithmetic_row15 (fun j => Fin.cases h4n141_arithmetic_row16 (fun j => Fin.cases h4n141_arithmetic_row17 (fun j => Fin.cases h4n141_arithmetic_row18 (fun j => Fin.cases h4n141_arithmetic_row19 (fun j => Fin.cases h4n141_arithmetic_row20 (fun j => Fin.cases h4n141_arithmetic_row21 (fun j => Fin.cases h4n141_arithmetic_row22 (fun j => Fin.cases h4n141_arithmetic_row23 (fun j => Fin.cases h4n141_arithmetic_row24 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n141 : h4e141.toBi mapPolyEnv=h4p141 := by
  change BiPoly.mul (h4e5.toBi mapPolyEnv) (h4e140.toBi mapPolyEnv)=h4p141
  rw [h4n5, h4n140]
  exact h4n141_arithmetic

#print axioms h4n141_arithmetic
end StackSorting.RationalLift
