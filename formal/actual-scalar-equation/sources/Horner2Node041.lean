import BivariateRowEquality
import Horner2Base
import Horner2Node040
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p41 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 9100764875354111999), (Int.negSucc 52807210075864834559), (Int.negSucc 115076329208419478399), (Int.negSucc 403747820932533609599), (Int.negSucc 449671291061383560959), (Int.ofNat 2182007541539425731840), (Int.ofNat 1960669289955762437760), (Int.negSucc 2017072996567231524479), (Int.negSucc 1678441390846809523199)], [(Int.ofNat 0), (Int.ofNat 103818795771837818880), (Int.ofNat 590969505035079207936), (Int.ofNat 1460091469736010552192), (Int.ofNat 5566508919618439166208), (Int.ofNat 7267873036563493781760), (Int.negSucc 24959104317018102044159), (Int.negSucc 21134564451115380040319), (Int.ofNat 19407644272276826086656), (Int.ofNat 13742518171147516021248), (Int.negSucc 583961574134299944959)], [(Int.ofNat 0), (Int.negSucc 549045716052380774399), (Int.negSucc 3181404437628454079999), (Int.negSucc 8832294637930821637727), (Int.negSucc 35606085528415736471903), (Int.negSucc 50070743372556297883295), (Int.ofNat 132984134799476986305504), (Int.ofNat 105229414844906060598624), (Int.negSucc 79914052396770806137247), (Int.negSucc 53247631938709721772383), (Int.negSucc 933117536630087248607), (Int.ofNat 291195816907509930240)], [(Int.ofNat 0), (Int.ofNat 1786329365225497044480), (Int.ofNat 10997487085278783710592), (Int.ofNat 33431864132161131721056), (Int.ofNat 141885854690930502227136), (Int.ofNat 203553233138324522523744), (Int.negSucc 426370921098467374191167), (Int.negSucc 324510380388453321811871), (Int.ofNat 163858407441586632583488), (Int.ofNat 131849927581015451148192), (Int.ofNat 26045108477937526332096), (Int.negSucc 3824138496480899189183), (Int.ofNat 151915735569914933760)], [(Int.ofNat 0), (Int.negSucc 4001318833184061131519), (Int.negSucc 27364873609086830553887), (Int.negSucc 88315686511814372273519), (Int.negSucc 397230140069911136815727), (Int.negSucc 558321521151703320208847), (Int.ofNat 880705467391780940839728), (Int.ofNat 711404197295173412406576), (Int.negSucc 93183598876830247522703), (Int.negSucc 237048772788302826672431), (Int.negSucc 109442603836463258395151), (Int.ofNat 11560903043651109167808), (Int.negSucc 620621908508674717823), (Int.ofNat 16889905709082700800)], [(Int.ofNat 0), (Int.ofNat 6543366739965241989120), (Int.ofNat 51818660553092075545856), (Int.ofNat 173374146941299380676368), (Int.ofNat 830668344301607670967760), (Int.ofNat 1118022653759076131100512), (Int.negSucc 1126407110029465745777423), (Int.negSucc 1213004128774161821428031), (Int.negSucc 374584086726096463458255), (Int.ofNat 300336664010743573520928), (Int.ofNat 227868719468674563809168), (Int.ofNat 1033169330745578263600), (Int.negSucc 1272751897427382095231), (Int.ofNat 28784912037935778560), (Int.negSucc 87994499346687999)], [(Int.ofNat 0), (Int.negSucc 8083223709083933417279), (Int.negSucc 76768127545938023679647), (Int.negSucc 264507483868273642933103), (Int.negSucc 1340175596617075047006799), (Int.negSucc 1740601532708057316906479), (Int.ofNat 606246518127644308666432), (Int.ofNat 1661230998516872159125984), (Int.ofNat 1147108015052575679932144), (Int.negSucc 152247525416467922460559), (Int.negSucc 265910933371029766323039), (Int.negSucc 73491607753504089172975), (Int.ofNat 8249972211313152148064), (Int.negSucc 304177823451175263743), (Int.ofNat 3127563564986009600)], [(Int.ofNat 0), (Int.ofNat 7699367198551520958720), (Int.ofNat 90109470642615650667936), (Int.ofNat 324788621404425897943856), (Int.ofNat 1696732535905325101228960), (Int.ofNat 2234514666127469549414128), (Int.ofNat 753086326945811864618128), (Int.negSucc 1695821170914410783310031), (Int.negSucc 1682589568174830973693279), (Int.negSucc 347676583054097867571983), (Int.ofNat 142014150802233911949104), (Int.ofNat 166905793702340452029056), (Int.negSucc 6767738830634544468511), (Int.negSucc 127973281292249289215), (Int.ofNat 8524308865065507840)], [(Int.ofNat 0), (Int.negSucc 5720793791847365140799), (Int.negSucc 84171344517462766548703), (Int.negSucc 329232919564085752672959), (Int.negSucc 1702579030191598025347695), (Int.negSucc 2474721402080688112834623), (Int.negSucc 2200868942215992008124463), (Int.ofNat 917659072910153321497920), (Int.ofNat 1556469891381172572025152), (Int.ofNat 966392559467305636669968), (Int.ofNat 89429256098422388510912), (Int.negSucc 153140704839963064924079), (Int.negSucc 22846548950518572370015), (Int.ofNat 1959126207088054810944), (Int.negSucc 34991264133971233279)], [(Int.ofNat 0), (Int.ofNat 3331966557000050519040), (Int.ofNat 62543604156305703177728), (Int.ofNat 279007349955271866005376), (Int.ofNat 1366698812045352059825296), (Int.ofNat 2391469590509929095502464), (Int.ofNat 2860133934209288917125568), (Int.ofNat 522677660783476955239040), (Int.negSucc 889100366159583826128095), (Int.negSucc 1153888947504412529703759), (Int.negSucc 317079695357284582538671), (Int.ofNat 4143844754736831417472), (Int.ofNat 55692550025569908996448), (Int.negSucc 1401875406930325027631), (Int.negSucc 61013632081393719679)], [(Int.ofNat 0), (Int.negSucc 1519290785664895094399), (Int.negSucc 36827158866284057828159), (Int.negSucc 197306926370136755528991), (Int.negSucc 889964760803560286161327), (Int.negSucc 1969225237062851138221567), (Int.negSucc 2589569059817496181243679), (Int.negSucc 1746063049264897437721407), (Int.ofNat 49818988012201661672288), (Int.ofNat 719736131482960983433584), (Int.ofNat 429055394418246053028064), (Int.ofNat 133204812312853724244640), (Int.negSucc 38665495762073213487135), (Int.negSucc 4241741389257883761407), (Int.ofNat 169860423647375381760)], [(Int.ofNat 0), (Int.ofNat 538016814304360320000), (Int.ofNat 17062648685746535445568), (Int.ofNat 114874304541205909936832), (Int.ofNat 480757162431819832045856), (Int.ofNat 1333538623033882987440432), (Int.ofNat 1869681923107380032431392), (Int.ofNat 2016857725560653376556544), (Int.ofNat 643747384202916094259776), (Int.negSucc 88345256905797055538159), (Int.negSucc 336525610039484595709455), (Int.negSucc 148087088040390678037935), (Int.negSucc 16617164247847237702911), (Int.ofNat 7506438665120941965424), (Int.ofNat 93605522978656572480)], [(Int.ofNat 0), (Int.negSucc 145474747731173531519), (Int.negSucc 6151887630952103292255), (Int.negSucc 53974793848459669171823), (Int.negSucc 221633626090163278004239), (Int.negSucc 723793319177592676430223), (Int.negSucc 1150507801726699027634287), (Int.negSucc 1494981301526109919899599), (Int.negSucc 935240449656426381513711), (Int.negSucc 293383946488036650766271), (Int.ofNat 101682590994888211934736), (Int.ofNat 84649814866912465316704), (Int.ofNat 43712311987635073819008), (Int.negSucc 2096389277792508270815), (Int.negSucc 402510870624980675519)], [(Int.ofNat 0), (Int.ofNat 29119470188985093120), (Int.ofNat 1697451529375318879872), (Int.ofNat 20010004289017358666384), (Int.ofNat 88915974641226652434736), (Int.ofNat 312486319721773113436960), (Int.ofNat 606585689817952469897744), (Int.ofNat 817841922041210522155488), (Int.ofNat 785478778725480536065872), (Int.ofNat 368673157083939646283088), (Int.ofNat 84352025373257886132096), (Int.negSucc 19918532536476194813471), (Int.negSucc 25978052080973428144991), (Int.negSucc 4473580485696834304223), (Int.ofNat 139482345164190347520)], [(Int.ofNat 0), (Int.negSucc 4079852365549830719), (Int.negSucc 349445233032453135519), (Int.negSucc 5712808630150027514415), (Int.negSucc 30750835246652755148783), (Int.negSucc 108720514127580509907951), (Int.negSucc 263644368256272208337439), (Int.negSucc 361879461084750407913247), (Int.negSucc 446250528332522771877071), (Int.negSucc 281362511634242344946495), (Int.negSucc 126811706003561360006495), (Int.negSucc 18156319390901835087263), (Int.ofNat 2060312881421344638816), (Int.ofNat 4248121303687941316224), (Int.ofNat 282070448074430017920)], [(Int.ofNat 0), (Int.ofNat 358104031659982080), (Int.ofNat 51564600245211184544), (Int.ofNat 1221972123696053270064), (Int.ofNat 8790960239798422191264), (Int.ofNat 31436041369184825590288), (Int.ofNat 90447481767529429338480), (Int.ofNat 137464957020789742054032), (Int.ofNat 181277668813993469306784), (Int.ofNat 156363074671716956168352), (Int.ofNat 85514801198060288805408), (Int.ofNat 27406080304994185259040), (Int.ofNat 5941962378150596783424), (Int.negSucc 699468394720232890943), (Int.negSucc 236887677764027447039)], [(Int.ofNat 0), (Int.negSucc 14844234440692799), (Int.negSucc 5096726169787686815), (Int.negSucc 189291975832948566239), (Int.negSucc 1957764745788440350607), (Int.negSucc 7764120256462134744095), (Int.negSucc 23920789821982080646895), (Int.negSucc 44511379944163786130399), (Int.negSucc 55737534945853455961535), (Int.negSucc 63045575353049112786527), (Int.negSucc 39408285802190676992927), (Int.negSucc 18374649459511342269887), (Int.negSucc 4774836478768180412543), (Int.negSucc 843378670755577300607), (Int.negSucc 5637797253160277759)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 296358638333685120), (Int.ofNat 20259617642005601376), (Int.ofNat 318063108778697758320), (Int.ofNat 1612585454974785801216), (Int.ofNat 4900261603110891333696), (Int.ofNat 11516692595500371088800), (Int.ofNat 14012211516139942172640), (Int.ofNat 17919235774697221621728), (Int.ofNat 13723583125488024185856), (Int.ofNat 7504076161119172139712), (Int.ofNat 2382060871512503047296), (Int.ofNat 586791901391410905984), (Int.ofNat 65241352831136762880)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 7339702349865599), (Int.negSucc 1380329469091300319), (Int.negSucc 34835862690942951599), (Int.negSucc 260561455337124574847), (Int.negSucc 803369154692230982495), (Int.negSucc 2206534583883754484063), (Int.negSucc 3042578959436411247455), (Int.negSucc 3531455246845350577151), (Int.negSucc 3553572793720210568063), (Int.negSucc 2054951681200353789695), (Int.negSucc 815483253986704238975), (Int.negSucc 195007077190294553087), (Int.negSucc 22771765939239590399)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 47590905886704000), (Int.ofNat 2273021224163573472), (Int.ofNat 28752256286239495536), (Int.ofNat 108179723973284897184), (Int.ofNat 292939369341419495520), (Int.ofNat 545545496273113463616), (Int.ofNat 492554093370290929728), (Int.ofNat 628345659828389319936), (Int.ofNat 398535118736311381248), (Int.ofNat 178756303230800932608), (Int.ofNat 40167550102344118272), (Int.ofNat 2119717327846072320)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 66328893359550719), (Int.negSucc 1748659944970465343), (Int.negSucc 11098254348043082783), (Int.negSucc 25850511323542231487), (Int.negSucc 69350583844327257215), (Int.negSucc 54650287485405242495), (Int.negSucc 66034579671567827711), (Int.negSucc 52692563574307420415), (Int.negSucc 25136207247345306623), (Int.negSucc 3742605481944867839)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 32936370241651200), (Int.ofNat 644961563767661184), (Int.ofNat 1660116791053885248), (Int.ofNat 4670677973595535488), (Int.ofNat 5945946456807091584), (Int.ofNat 2285060961748969728), (Int.ofNat 4582822351246221312), (Int.ofNat 1921113362104657920)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 5304619316782079), (Int.negSucc 90049611637677311), (Int.negSucc 39345622508737151), (Int.negSucc 503209843058103551), (Int.ofNat 242401333233047040), (Int.negSucc 298225208005862399)]]

theorem h2n41_arithmetic_row0 :
    (BiPoly.mul h2p4 h2p40).getD 0 []=h2p41.getD 0 [] := by
  decide +kernel

theorem h2n41_arithmetic_row1 :
    (BiPoly.mul h2p4 h2p40).getD 1 []=h2p41.getD 1 [] := by
  decide +kernel

theorem h2n41_arithmetic_row2 :
    (BiPoly.mul h2p4 h2p40).getD 2 []=h2p41.getD 2 [] := by
  decide +kernel

theorem h2n41_arithmetic_row3 :
    (BiPoly.mul h2p4 h2p40).getD 3 []=h2p41.getD 3 [] := by
  decide +kernel

theorem h2n41_arithmetic_row4 :
    (BiPoly.mul h2p4 h2p40).getD 4 []=h2p41.getD 4 [] := by
  decide +kernel

theorem h2n41_arithmetic_row5 :
    (BiPoly.mul h2p4 h2p40).getD 5 []=h2p41.getD 5 [] := by
  decide +kernel

theorem h2n41_arithmetic_row6 :
    (BiPoly.mul h2p4 h2p40).getD 6 []=h2p41.getD 6 [] := by
  decide +kernel

theorem h2n41_arithmetic_row7 :
    (BiPoly.mul h2p4 h2p40).getD 7 []=h2p41.getD 7 [] := by
  decide +kernel

theorem h2n41_arithmetic_row8 :
    (BiPoly.mul h2p4 h2p40).getD 8 []=h2p41.getD 8 [] := by
  decide +kernel

theorem h2n41_arithmetic_row9 :
    (BiPoly.mul h2p4 h2p40).getD 9 []=h2p41.getD 9 [] := by
  decide +kernel

theorem h2n41_arithmetic_row10 :
    (BiPoly.mul h2p4 h2p40).getD 10 []=h2p41.getD 10 [] := by
  decide +kernel

theorem h2n41_arithmetic_row11 :
    (BiPoly.mul h2p4 h2p40).getD 11 []=h2p41.getD 11 [] := by
  decide +kernel

theorem h2n41_arithmetic_row12 :
    (BiPoly.mul h2p4 h2p40).getD 12 []=h2p41.getD 12 [] := by
  decide +kernel

theorem h2n41_arithmetic_row13 :
    (BiPoly.mul h2p4 h2p40).getD 13 []=h2p41.getD 13 [] := by
  decide +kernel

theorem h2n41_arithmetic_row14 :
    (BiPoly.mul h2p4 h2p40).getD 14 []=h2p41.getD 14 [] := by
  decide +kernel

theorem h2n41_arithmetic_row15 :
    (BiPoly.mul h2p4 h2p40).getD 15 []=h2p41.getD 15 [] := by
  decide +kernel

theorem h2n41_arithmetic_row16 :
    (BiPoly.mul h2p4 h2p40).getD 16 []=h2p41.getD 16 [] := by
  decide +kernel

theorem h2n41_arithmetic_row17 :
    (BiPoly.mul h2p4 h2p40).getD 17 []=h2p41.getD 17 [] := by
  decide +kernel

theorem h2n41_arithmetic_row18 :
    (BiPoly.mul h2p4 h2p40).getD 18 []=h2p41.getD 18 [] := by
  decide +kernel

theorem h2n41_arithmetic_row19 :
    (BiPoly.mul h2p4 h2p40).getD 19 []=h2p41.getD 19 [] := by
  decide +kernel

theorem h2n41_arithmetic_row20 :
    (BiPoly.mul h2p4 h2p40).getD 20 []=h2p41.getD 20 [] := by
  decide +kernel

theorem h2n41_arithmetic_row21 :
    (BiPoly.mul h2p4 h2p40).getD 21 []=h2p41.getD 21 [] := by
  decide +kernel

theorem h2n41_arithmetic_row22 :
    (BiPoly.mul h2p4 h2p40).getD 22 []=h2p41.getD 22 [] := by
  decide +kernel

theorem h2n41_arithmetic : BiPoly.mul h2p4 h2p40=h2p41 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<23 at hk
    have hf : ∀ j : Fin 23, (BiPoly.mul h2p4 h2p40).getD j.val []=h2p41.getD j.val [] :=
      (fun j => Fin.cases h2n41_arithmetic_row0 (fun j => Fin.cases h2n41_arithmetic_row1 (fun j => Fin.cases h2n41_arithmetic_row2 (fun j => Fin.cases h2n41_arithmetic_row3 (fun j => Fin.cases h2n41_arithmetic_row4 (fun j => Fin.cases h2n41_arithmetic_row5 (fun j => Fin.cases h2n41_arithmetic_row6 (fun j => Fin.cases h2n41_arithmetic_row7 (fun j => Fin.cases h2n41_arithmetic_row8 (fun j => Fin.cases h2n41_arithmetic_row9 (fun j => Fin.cases h2n41_arithmetic_row10 (fun j => Fin.cases h2n41_arithmetic_row11 (fun j => Fin.cases h2n41_arithmetic_row12 (fun j => Fin.cases h2n41_arithmetic_row13 (fun j => Fin.cases h2n41_arithmetic_row14 (fun j => Fin.cases h2n41_arithmetic_row15 (fun j => Fin.cases h2n41_arithmetic_row16 (fun j => Fin.cases h2n41_arithmetic_row17 (fun j => Fin.cases h2n41_arithmetic_row18 (fun j => Fin.cases h2n41_arithmetic_row19 (fun j => Fin.cases h2n41_arithmetic_row20 (fun j => Fin.cases h2n41_arithmetic_row21 (fun j => Fin.cases h2n41_arithmetic_row22 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h2n41 : h2e41.toBi mapPolyEnv=h2p41 := by
  change BiPoly.mul (h2e4.toBi mapPolyEnv) (h2e40.toBi mapPolyEnv)=h2p41
  rw [h2n4, h2n40]
  exact h2n41_arithmetic

#print axioms h2n41_arithmetic
end StackSorting.RationalLift
