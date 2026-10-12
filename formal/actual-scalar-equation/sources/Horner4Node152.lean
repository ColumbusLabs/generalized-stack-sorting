import BivariateRowEquality
import Horner4Base
import Horner4Node151
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p152 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2961775737669064896000), (Int.ofNat 25357753329618823061760), (Int.ofNat 52149766494820050270720), (Int.negSucc 49821387826186664133119), (Int.negSucc 170938669006657314777599), (Int.ofNat 18681723440603032193280), (Int.ofNat 110045215718203390732800)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 37278233401786876535039), (Int.negSucc 315879292686762752335487), (Int.negSucc 638772828217232532815231), (Int.ofNat 595522724269002840253440), (Int.ofNat 1897736065957248552525312), (Int.negSucc 382287189582898364612735), (Int.negSucc 1064652446944848455247743), (Int.ofNat 57299157368494427001600)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 222894734669093980460160), (Int.ofNat 1850599750247744946754752), (Int.ofNat 3666717252799338036307392), (Int.negSucc 3211387301548558335354623), (Int.negSucc 9795277903211844140210687), (Int.ofNat 2341807369354202610246336), (Int.ofNat 4429144161810173619873216), (Int.negSucc 68120019864435549635711), (Int.negSucc 12493153034645321636351)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 841438682866684763674559), (Int.negSucc 6769719455251835736165599), (Int.negSucc 13165675399437326157199679), (Int.ofNat 9886443813168481508386464), (Int.ofNat 30954396843281305907860608), (Int.negSucc 6213642511675431948737183), (Int.negSucc 10358923323961633818376511), (Int.negSucc 1992968124396917285168927), (Int.ofNat 317277689255110526717376), (Int.negSucc 13259797819695322841087)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2245855644540450195223680), (Int.ofNat 17329171867233525467357760), (Int.ofNat 33378569432907215706393984), (Int.negSucc 17624551588410784136864831), (Int.negSucc 66610383790079725413752447), (Int.ofNat 3461660016799212677894976), (Int.ofNat 14964543425313163556183808), (Int.ofNat 10985456053945794242414016), (Int.negSucc 1402082114349833984541311), (Int.ofNat 88385922562183147395072), (Int.negSucc 2825094926879531311103)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 4493421941513570169281279), (Int.negSucc 33008091743236029626185343), (Int.negSucc 64083755048318812136998943), (Int.ofNat 12435285917655029848841568), (Int.ofNat 102068628495372408017068704), (Int.ofNat 26133145936088792621679360), (Int.negSucc 13308551011037796601784543), (Int.negSucc 26369175444388233465156767), (Int.ofNat 1052790648081169542029280), (Int.ofNat 40888008310199150445120), (Int.ofNat 1365219353110831898112), (Int.negSucc 184959914300940201983)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 6967486021305845927213280), (Int.ofNat 48635849574530039561996304), (Int.ofNat 97675600623572093458285296), (Int.ofNat 22880582095183586528519088), (Int.negSucc 109657173145929142725881423), (Int.negSucc 90764159166247609180887407), (Int.ofNat 1862893614939442919040528), (Int.ofNat 32242600307321261931431952), (Int.ofNat 7499904929162028162852912), (Int.negSucc 1144808672521041924489503), (Int.ofNat 60740181234262129606272), (Int.negSucc 1120077919747319334911), (Int.ofNat 993733974921093120)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 8535831283503302264542079), (Int.negSucc 56978191340003895374981663), (Int.negSucc 122196104104745957989689359), (Int.negSucc 86199118898515384903173503), (Int.ofNat 67995407337776624538085680), (Int.ofNat 155118328944960489344123616), (Int.ofNat 26524318252390012192128912), (Int.negSucc 12967540696438558882095455), (Int.negSucc 23871259909063749279287663), (Int.ofNat 1960558606172473307853984), (Int.negSucc 68942216554356989485439), (Int.ofNat 2307664201558196378880), (Int.negSucc 32244315332324299775)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 8347933519196964135919200), (Int.ofNat 54199643701520993143027248), (Int.ofNat 128261467228595777546787792), (Int.ofNat 147420692427680855544999024), (Int.ofNat 16497728752681280788086816), (Int.negSucc 159003972769650101155181087), (Int.negSucc 73562987236357840172911631), (Int.negSucc 20019983759962408811573711), (Int.ofNat 28628119336076591977633248), (Int.ofNat 2203683940745109850875984), (Int.negSucc 384395204304926395204895), (Int.ofNat 15668114130302692970880), (Int.negSucc 206224549735062219263)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 6543568783239944973508799), (Int.negSucc 42548490953753869473490367), (Int.negSucc 114261543075247619409326447), (Int.negSucc 172814153466328938952936415), (Int.negSucc 105631107901929587196184895), (Int.ofNat 82482843871738776235746816), (Int.ofNat 111635902339828720382680272), (Int.ofNat 41904510919677290294225280), (Int.negSucc 6690809329685826578820863), (Int.negSucc 10698233449557207361190975), (Int.ofNat 791611953953299293909600), (Int.negSucc 18275271268517726716223), (Int.ofNat 118633373660095741440)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4106531817521204973577920), (Int.ofNat 27873463527713370648102336), (Int.ofNat 86616105820610285096528688), (Int.ofNat 154863034278565327879281696), (Int.ofNat 154485492056277524590979520), (Int.ofNat 26467073871376018853656224), (Int.negSucc 99258357864675514763481839), (Int.negSucc 47041095718709351894405807), (Int.negSucc 22517905901333817066459407), (Int.ofNat 11938223152516499540268048), (Int.ofNat 459975114136293994657296), (Int.negSucc 74929953360222865585439), (Int.ofNat 2019258468700780061952)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2051224054157221359422399), (Int.negSucc 15301627619615252510037407), (Int.negSucc 55644584585089204357534079), (Int.negSucc 112433244103400510172542543), (Int.negSucc 147321217078529552486305775), (Int.negSucc 99683778624016513230724175), (Int.ofNat 35629251218773460784045792), (Int.ofNat 41358449096194281270827760), (Int.ofNat 30127353318644604944571936), (Int.negSucc 604330680562344466120943), (Int.negSucc 2606807277744264125258255), (Int.ofNat 112512198294002868762240), (Int.ofNat 151317145482256234944)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 806521349078467544427840), (Int.ofNat 7008130096353027779844384), (Int.ofNat 30028004280144024829835616), (Int.ofNat 68681525088655861469811072), (Int.ofNat 105422624206228179130476096), (Int.ofNat 109845239940679059209630160), (Int.ofNat 30716913873776564693656368), (Int.negSucc 24001843456497081519503999), (Int.negSucc 17978756599188031846046975), (Int.negSucc 10301793795483343170529967), (Int.ofNat 2235530039005871573111136), (Int.ofNat 113881621174417153341936), (Int.negSucc 7710577716437464140575)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 245245034696631074375039), (Int.negSucc 2641741233839786821600511), (Int.negSucc 13438724170496447360139263), (Int.negSucc 35918074383528604141964447), (Int.negSucc 60504645352976915075546399), (Int.negSucc 78895512967868644651929935), (Int.negSucc 57455063810692956296665631), (Int.negSucc 724287148112935120096799), (Int.ofNat 5187385157239426247962848), (Int.ofNat 9532866901703503187826864), (Int.ofNat 649971597032949068781264), (Int.negSucc 305641629844022944999583), (Int.ofNat 1130104850632505558784)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 56125024362264249306720), (Int.ofNat 801632004821642413805328), (Int.ofNat 4904793230799084285570192), (Int.ofNat 15967789711710532275181104), (Int.ofNat 29324448772025985326755152), (Int.ofNat 42183891856557202313886624), (Int.ofNat 46556151561874882573732512), (Int.ofNat 17421976314223015999735296), (Int.ofNat 1378796422778746119659520), (Int.negSucc 2764395390513059306030447), (Int.negSucc 2182343039999009151922943), (Int.ofNat 108612050451965552974464), (Int.ofNat 13814612568749933497728)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 9264377375122099703039), (Int.negSucc 189896778775245290226911), (Int.negSucc 1428678369129024471754511), (Int.negSucc 5871261800823269200617311), (Int.negSucc 12376442691243027175037327), (Int.negSucc 18092458766700840994191215), (Int.negSucc 24554128115041252887407759), (Int.negSucc 18285398807854770566521775), (Int.negSucc 4300268922636119319891023), (Int.negSucc 1141443978130873216646783), (Int.ofNat 1203344056785170167248672), (Int.ofNat 173804470680830986924128), (Int.negSucc 8077253448264732091583)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1027743087190200852960), (Int.ofNat 33668501841374368282992), (Int.ofNat 322922800383255763199568), (Int.ofNat 1718391087043302195712944), (Int.ofNat 4500605764462937571029952), (Int.ofNat 6697440422298375765379344), (Int.ofNat 9332222069625524702561952), (Int.ofNat 10631649909773756088856944), (Int.ofNat 4605316573415207266051776), (Int.ofNat 1535008458251226415157568), (Int.ofNat 54027470693635179801408), (Int.negSucc 170677574464609146969791), (Int.negSucc 7834472210104045854335)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 67104541563113142719), (Int.negSucc 4193949981237395959871), (Int.negSucc 54500351584815956027375), (Int.negSucc 383139258974072952097247), (Int.negSucc 1341516478630825973723615), (Int.negSucc 2239390381752908863344719), (Int.negSucc 2786531298450340326555599), (Int.negSucc 3973639423611688403410655), (Int.negSucc 2949580945562358194026271), (Int.negSucc 996509630977555679790047), (Int.negSucc 360324880217370052111871), (Int.ofNat 25823769330755318182848), (Int.ofNat 8666419869655271457408)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1865796676422307200), (Int.ofNat 327735182544196366944), (Int.ofNat 6476591240069496313104), (Int.ofNat 61749443489807778988032), (Int.ofNat 306553529355479275521600), (Int.ofNat 654335556497480298049776), (Int.ofNat 742784638100519573881920), (Int.ofNat 998693531315036489702016), (Int.ofNat 1176271387696257118747776), (Int.ofNat 527908824942006571821504), (Int.ofNat 205015908269580658870464), (Int.ofNat 35884726931975448115584), (Int.negSucc 896914881427499315711)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 12145629966367616639), (Int.negSucc 486695578340116459295), (Int.negSucc 6677521298088236802287), (Int.negSucc 49858481820892848978095), (Int.negSucc 151935042422333080405439), (Int.negSucc 192113501829285733823519), (Int.negSucc 182746812755904803146079), (Int.negSucc 287488727719368552213695), (Int.negSucc 208380111259505777108351), (Int.negSucc 73695892556511429763967), (Int.negSucc 23826167865767893221503), (Int.negSucc 2026869668390005638911)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 17600298816218451840), (Int.ofNat 424635305391379281312), (Int.ofNat 5228104669456952884320), (Int.ofNat 25188441354984664590912), (Int.ofNat 43698204979995696587712), (Int.ofNat 31477680244382058224064), (Int.ofNat 39994853582726860575744), (Int.ofNat 52168473120342217932288), (Int.ofNat 21603470233403612272896), (Int.ofNat 7157446038643566574080), (Int.ofNat 1048056312917566457856)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 11512072781552769407), (Int.negSucc 293420142820735600607), (Int.negSucc 2638646261485116269471), (Int.negSucc 7267960075711219360127), (Int.negSucc 6264486132547290560063), (Int.negSucc 2704407037280870825087), (Int.negSucc 6977778452147466192383), (Int.negSucc 4733002045697985110015), (Int.negSucc 1371020564393657641727), (Int.negSucc 201205534818016728575)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4985412560434725120), (Int.ofNat 139641904635363519552), (Int.ofNat 744198340748025191616), (Int.ofNat 1048742343772458678144), (Int.ofNat 155651599978798851072), (Int.ofNat 250621774663712792832), (Int.ofNat 600819911639500338432), (Int.ofNat 186629993538023941632), (Int.ofNat 13488308867273564160)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1513713911966783999), (Int.negSucc 36125437023735129215), (Int.negSucc 100831780359440548991), (Int.negSucc 40955872046285041919), (Int.ofNat 44741147868680378112), (Int.negSucc 30524466189835270655), (Int.negSucc 13488308867273564159)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 207971977912906752), (Int.ofNat 3761600838643853568), (Int.ofNat 4512751243881907968), (Int.negSucc 4357125043508344319)]]

theorem h4n152_arithmetic_row0 :
    (BiPoly.mul h4p5 h4p151).getD 0 []=h4p152.getD 0 [] := by
  decide +kernel

theorem h4n152_arithmetic_row1 :
    (BiPoly.mul h4p5 h4p151).getD 1 []=h4p152.getD 1 [] := by
  decide +kernel

theorem h4n152_arithmetic_row2 :
    (BiPoly.mul h4p5 h4p151).getD 2 []=h4p152.getD 2 [] := by
  decide +kernel

theorem h4n152_arithmetic_row3 :
    (BiPoly.mul h4p5 h4p151).getD 3 []=h4p152.getD 3 [] := by
  decide +kernel

theorem h4n152_arithmetic_row4 :
    (BiPoly.mul h4p5 h4p151).getD 4 []=h4p152.getD 4 [] := by
  decide +kernel

theorem h4n152_arithmetic_row5 :
    (BiPoly.mul h4p5 h4p151).getD 5 []=h4p152.getD 5 [] := by
  decide +kernel

theorem h4n152_arithmetic_row6 :
    (BiPoly.mul h4p5 h4p151).getD 6 []=h4p152.getD 6 [] := by
  decide +kernel

theorem h4n152_arithmetic_row7 :
    (BiPoly.mul h4p5 h4p151).getD 7 []=h4p152.getD 7 [] := by
  decide +kernel

theorem h4n152_arithmetic_row8 :
    (BiPoly.mul h4p5 h4p151).getD 8 []=h4p152.getD 8 [] := by
  decide +kernel

theorem h4n152_arithmetic_row9 :
    (BiPoly.mul h4p5 h4p151).getD 9 []=h4p152.getD 9 [] := by
  decide +kernel

theorem h4n152_arithmetic_row10 :
    (BiPoly.mul h4p5 h4p151).getD 10 []=h4p152.getD 10 [] := by
  decide +kernel

theorem h4n152_arithmetic_row11 :
    (BiPoly.mul h4p5 h4p151).getD 11 []=h4p152.getD 11 [] := by
  decide +kernel

theorem h4n152_arithmetic_row12 :
    (BiPoly.mul h4p5 h4p151).getD 12 []=h4p152.getD 12 [] := by
  decide +kernel

theorem h4n152_arithmetic_row13 :
    (BiPoly.mul h4p5 h4p151).getD 13 []=h4p152.getD 13 [] := by
  decide +kernel

theorem h4n152_arithmetic_row14 :
    (BiPoly.mul h4p5 h4p151).getD 14 []=h4p152.getD 14 [] := by
  decide +kernel

theorem h4n152_arithmetic_row15 :
    (BiPoly.mul h4p5 h4p151).getD 15 []=h4p152.getD 15 [] := by
  decide +kernel

theorem h4n152_arithmetic_row16 :
    (BiPoly.mul h4p5 h4p151).getD 16 []=h4p152.getD 16 [] := by
  decide +kernel

theorem h4n152_arithmetic_row17 :
    (BiPoly.mul h4p5 h4p151).getD 17 []=h4p152.getD 17 [] := by
  decide +kernel

theorem h4n152_arithmetic_row18 :
    (BiPoly.mul h4p5 h4p151).getD 18 []=h4p152.getD 18 [] := by
  decide +kernel

theorem h4n152_arithmetic_row19 :
    (BiPoly.mul h4p5 h4p151).getD 19 []=h4p152.getD 19 [] := by
  decide +kernel

theorem h4n152_arithmetic_row20 :
    (BiPoly.mul h4p5 h4p151).getD 20 []=h4p152.getD 20 [] := by
  decide +kernel

theorem h4n152_arithmetic_row21 :
    (BiPoly.mul h4p5 h4p151).getD 21 []=h4p152.getD 21 [] := by
  decide +kernel

theorem h4n152_arithmetic_row22 :
    (BiPoly.mul h4p5 h4p151).getD 22 []=h4p152.getD 22 [] := by
  decide +kernel

theorem h4n152_arithmetic_row23 :
    (BiPoly.mul h4p5 h4p151).getD 23 []=h4p152.getD 23 [] := by
  decide +kernel

theorem h4n152_arithmetic_row24 :
    (BiPoly.mul h4p5 h4p151).getD 24 []=h4p152.getD 24 [] := by
  decide +kernel

theorem h4n152_arithmetic : BiPoly.mul h4p5 h4p151=h4p152 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<25 at hk
    have hf : ∀ j : Fin 25, (BiPoly.mul h4p5 h4p151).getD j.val []=h4p152.getD j.val [] :=
      (fun j => Fin.cases h4n152_arithmetic_row0 (fun j => Fin.cases h4n152_arithmetic_row1 (fun j => Fin.cases h4n152_arithmetic_row2 (fun j => Fin.cases h4n152_arithmetic_row3 (fun j => Fin.cases h4n152_arithmetic_row4 (fun j => Fin.cases h4n152_arithmetic_row5 (fun j => Fin.cases h4n152_arithmetic_row6 (fun j => Fin.cases h4n152_arithmetic_row7 (fun j => Fin.cases h4n152_arithmetic_row8 (fun j => Fin.cases h4n152_arithmetic_row9 (fun j => Fin.cases h4n152_arithmetic_row10 (fun j => Fin.cases h4n152_arithmetic_row11 (fun j => Fin.cases h4n152_arithmetic_row12 (fun j => Fin.cases h4n152_arithmetic_row13 (fun j => Fin.cases h4n152_arithmetic_row14 (fun j => Fin.cases h4n152_arithmetic_row15 (fun j => Fin.cases h4n152_arithmetic_row16 (fun j => Fin.cases h4n152_arithmetic_row17 (fun j => Fin.cases h4n152_arithmetic_row18 (fun j => Fin.cases h4n152_arithmetic_row19 (fun j => Fin.cases h4n152_arithmetic_row20 (fun j => Fin.cases h4n152_arithmetic_row21 (fun j => Fin.cases h4n152_arithmetic_row22 (fun j => Fin.cases h4n152_arithmetic_row23 (fun j => Fin.cases h4n152_arithmetic_row24 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n152 : h4e152.toBi mapPolyEnv=h4p152 := by
  change BiPoly.mul (h4e5.toBi mapPolyEnv) (h4e151.toBi mapPolyEnv)=h4p152
  rw [h4n5, h4n151]
  exact h4n152_arithmetic

#print axioms h4n152_arithmetic
end StackSorting.RationalLift
