import BivariateRowEquality
import Horner2Base
import Horner2Node088
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p89 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 5230327353975115776), (Int.negSucc 3971782461123876671), (Int.negSucc 76710705823447793279), (Int.ofNat 7771334623987415616), (Int.negSucc 910059415424186962175), (Int.negSucc 1021499384418466008767), (Int.ofNat 6182327845545610838400), (Int.negSucc 579111717888320556095), (Int.negSucc 4544224654477843560959)], [(Int.ofNat 0), (Int.negSucc 61564149013951362815), (Int.ofNat 73422169612793204832), (Int.ofNat 843974779194873632160), (Int.negSucc 106881786678676003487), (Int.ofNat 13626367600856199737760), (Int.ofNat 12103767517056902411040), (Int.negSucc 72290445634337006912543), (Int.ofNat 8259553938285032304672), (Int.ofNat 43812382900891987917792), (Int.negSucc 3269248434440728236287)], [(Int.ofNat 0), (Int.ofNat 343747048075973023104), (Int.negSucc 589765724725285075391), (Int.negSucc 4210469552511531830879), (Int.negSucc 614248195454892279359), (Int.negSucc 93593466663283512337823), (Int.negSucc 57934870262558917847999), (Int.ofNat 377450651074391234026848), (Int.negSucc 41037568321678779821759), (Int.negSucc 187637320337088506899679), (Int.ofNat 15024341397570900527232), (Int.negSucc 619089039383892599807)], [(Int.ofNat 0), (Int.negSucc 1209970868614774759103), (Int.ofNat 2822193042716743895232), (Int.ofNat 12262496061212933566368), (Int.ofNat 13468745628173101280736), (Int.ofNat 388288547076305206602048), (Int.ofNat 144321765126899910599424), (Int.negSucc 1141794177045654468386783), (Int.ofNat 54475954309903862599392), (Int.ofNat 457758471557413423407552), (Int.ofNat 8822052991275714085248), (Int.negSucc 2786155683123260158463), (Int.ofNat 22535353680366809088)], [(Int.ofNat 0), (Int.ofNat 3005718300879585723136), (Int.negSucc 9095283769005274749743), (Int.negSucc 22281355029562237097791), (Int.negSucc 84941536188870357978655), (Int.negSucc 1080245023694812422021791), (Int.negSucc 206026234155661308784703), (Int.ofNat 2166665725906571256468736), (Int.ofNat 275114889497297119608288), (Int.negSucc 671763036420293152964383), (Int.negSucc 218614201900994690999247), (Int.ofNat 27011748719679492263808), (Int.negSucc 1215712209636841114111), (Int.ofNat 10817009117368791040)], [(Int.ofNat 0), (Int.negSucc 5583696241259045335999), (Int.ofNat 20993711546694673369888), (Int.ofNat 24689452185349645785728), (Int.ofNat 303615747158506489360096), (Int.ofNat 2125995689549846946342016), (Int.ofNat 258501289035246403970720), (Int.negSucc 2577915473793556968820127), (Int.negSucc 1471562958925094711471423), (Int.ofNat 499244143942055372864608), (Int.ofNat 669416279729853293809312), (Int.negSucc 45314467445912746164991), (Int.ofNat 1283194169784561907200), (Int.negSucc 54425881507618731519), (Int.negSucc 54396599596134399)], [(Int.ofNat 0), (Int.ofNat 8015059773329073328992), (Int.negSucc 35938001661751722957039), (Int.negSucc 14767408786154564880415), (Int.negSucc 716374590627394756184511), (Int.negSucc 3068709063270639999455615), (Int.negSucc 688832406242546082216703), (Int.ofNat 1701990502431395169567104), (Int.ofNat 3302723300908899012239744), (Int.ofNat 263704094446182808611776), (Int.negSucc 959909041769409030524047), (Int.negSucc 82409555529149058994239), (Int.ofNat 12493093775914799729472), (Int.negSucc 426286225803241629695), (Int.ofNat 2241747292429332480)], [(Int.ofNat 0), (Int.negSucc 9059129096391272842815), (Int.ofNat 46589508547378807317408), (Int.ofNat 6552412117034734113568), (Int.ofNat 1192926685953035895353536), (Int.ofNat 3378879554707885498749184), (Int.ofNat 1936793718451266661163488), (Int.negSucc 98014238808744305111967), (Int.negSucc 4145230386178600242138591), (Int.negSucc 1515673450654236440845311), (Int.ofNat 525871554088883521458368), (Int.ofNat 404152960779667666311456), (Int.negSucc 30292736348879403517887), (Int.ofNat 737765743436997450240), (Int.negSucc 5293021899203627007)], [(Int.ofNat 0), (Int.ofNat 8145762707067749320320), (Int.negSucc 46311811621453567519327), (Int.negSucc 20374316874842808479903), (Int.negSucc 1454444781280207682263855), (Int.negSucc 3028695369227797869022303), (Int.negSucc 3574882830169731769161375), (Int.negSucc 1207933144706434837945055), (Int.ofNat 2675550169116715955094560), (Int.ofNat 2665335439307486609075392), (Int.ofNat 491473397676061530611168), (Int.negSucc 571676113302828372257791), (Int.negSucc 12314688236714531876687), (Int.ofNat 2676450648750827580928), (Int.negSucc 64830119938615501823)], [(Int.ofNat 0), (Int.negSucc 5853213473422809141247), (Int.ofNat 35536422147526616664032), (Int.ofNat 53082309541299585815264), (Int.ofNat 1330003394858918117091072), (Int.ofNat 2442215206740947902946880), (Int.ofNat 4388618778220485627150112), (Int.ofNat 2078413641417862076726848), (Int.ofNat 29428468251600223432704), (Int.negSucc 2700425172814039271128255), (Int.negSucc 1273173390687926688980255), (Int.ofNat 215503296119262401843392), (Int.ofNat 122866116076688095592576), (Int.negSucc 6143223046121156243487), (Int.ofNat 20555024500912269056)], [(Int.ofNat 0), (Int.ofNat 3361144250152645937216), (Int.negSucc 21103509109764010408799), (Int.negSucc 77111882824335804657215), (Int.negSucc 932565171373836383051055), (Int.negSucc 1908790359548371455418751), (Int.negSucc 3799652196379793379133503), (Int.negSucc 2755726098716690872378399), (Int.negSucc 1778533549578208853937599), (Int.ofNat 1282216329996022128072800), (Int.ofNat 1303049592000011823765376), (Int.ofNat 372047511661666337611424), (Int.negSucc 155135594259100567907727), (Int.negSucc 2954190098272592361727), (Int.ofNat 347021201070660307968)], [(Int.ofNat 0), (Int.negSucc 1536162492259523397311), (Int.ofNat 9696734344180364812480), (Int.ofNat 73175177834442948119264), (Int.ofNat 517894061978326835472576), (Int.ofNat 1395780151082650077702208), (Int.ofNat 2485165183888226983957952), (Int.ofNat 2900833430725765508714016), (Int.ofNat 2001054123007161035079936), (Int.ofNat 453272087682776679196704), (Int.negSucc 743806208797977996361887), (Int.negSucc 574617829085217862469279), (Int.ofNat 22039152875426485968800), (Int.ofNat 18340581141455798884832), (Int.negSucc 222821686943517096575)], [(Int.ofNat 0), (Int.ofNat 553917778119599965696), (Int.negSucc 3441433311786250082991), (Int.negSucc 49030363530308951606143), (Int.negSucc 241148549166207740762495), (Int.negSucc 867214858716702749903551), (Int.negSucc 1358637209377991066400383), (Int.negSucc 2238721444142227087085343), (Int.negSucc 1581687323640959773675775), (Int.negSucc 1199112375236829399921855), (Int.ofNat 55712313166765395650464), (Int.ofNat 324302484717377681035712), (Int.ofNat 119454164246966713384320), (Int.negSucc 14778575294776951449215), (Int.negSucc 716151954935249744255)], [(Int.ofNat 0), (Int.negSucc 155228815821702860095), (Int.ofNat 941589285860825673504), (Int.ofNat 24045658347896020545664), (Int.ofNat 101681356393586190634400), (Int.ofNat 428700472699871017859552), (Int.ofNat 692113462220324774899040), (Int.ofNat 1242023156544684290331712), (Int.ofNat 1115552498944379090755488), (Int.ofNat 964071171271715357020320), (Int.ofNat 352808828684541299112960), (Int.negSucc 22068313320044776199231), (Int.negSucc 112535050334651285359679), (Int.negSucc 5696224778349470495807), (Int.ofNat 868790119080465305856)], [(Int.ofNat 0), (Int.ofNat 32984734677092660192), (Int.negSucc 197954131754506040303), (Int.negSucc 8765409101951746806303), (Int.negSucc 40414435441192769945695), (Int.negSucc 166051641489358365869471), (Int.negSucc 332055480218205972867327), (Int.negSucc 514131875344465097302911), (Int.negSucc 663082757566487587896767), (Int.negSucc 507916968308954663797439), (Int.negSucc 371592216722781308087999), (Int.negSucc 99919227947588127028223), (Int.ofNat 24205735308271052319552), (Int.ofNat 14592327816007790952192), (Int.ofNat 231224095757813319936)], [(Int.ofNat 0), (Int.negSucc 5103445059641248831), (Int.ofNat 31446152074290137568), (Int.ofNat 2383175285868788229920), (Int.ofNat 14433303586526288273728), (Int.ofNat 51914328322088609625248), (Int.ofNat 136151199026461854943200), (Int.ofNat 176417867543066779227936), (Int.ofNat 293547091525512611531904), (Int.ofNat 224451754486840301310144), (Int.ofNat 205538167337434546198464), (Int.ofNat 91404590644509914779200), (Int.ofNat 22822627380495241935744), (Int.negSucc 6157245793077893563775), (Int.negSucc 803518434277854423551)], [(Int.ofNat 0), (Int.ofNat 536288025893279616), (Int.negSucc 3498881927663200127), (Int.negSucc 480787745761729489439), (Int.negSucc 4223716016947170347759), (Int.negSucc 13977701973050736623807), (Int.negSucc 43499711006211584847455), (Int.negSucc 57339150958588598364095), (Int.negSucc 90946248990099009274367), (Int.negSucc 90326570775212544538751), (Int.negSucc 72622805680075964474303), (Int.negSucc 48778989462076960030463), (Int.negSucc 19731832650422350117631), (Int.negSucc 1900911090436660228607), (Int.ofNat 295623230755089572352)], [(Int.ofNat 0), (Int.negSucc 33529186848927743), (Int.ofNat 196938879804627840), (Int.ofNat 71017587948480308352), (Int.ofNat 935775948146121950112), (Int.ofNat 3395940744764466529344), (Int.ofNat 10427387533988845330944), (Int.ofNat 17566972606871302006080), (Int.ofNat 19977711469803517469760), (Int.ofNat 29080760190147153723456), (Int.ofNat 18838545957798861264768), (Int.ofNat 16918454042619162157440), (Int.ofNat 7759616574932025967872), (Int.ofNat 2453975287454181991680), (Int.ofNat 147413472420043736064)], [(Int.ofNat 0), (Int.ofNat 903347981521920), (Int.ofNat 7247167222415616), (Int.negSucc 7472481990431349023), (Int.negSucc 147406255638760803311), (Int.negSucc 710587119085147238975), (Int.negSucc 1903177754782444753343), (Int.negSucc 4361492957214841074431), (Int.negSucc 3583439844131673027647), (Int.negSucc 6272464443057123206399), (Int.negSucc 4328181010599131079935), (Int.negSucc 3520636898684345745407), (Int.negSucc 2060186075651744437247), (Int.negSucc 820959034612100152319), (Int.negSucc 122991467128715381759)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1427462738207999), (Int.ofNat 521843755650548544), (Int.ofNat 15398178671389519584), (Int.ofNat 112944032967455945568), (Int.ofNat 280822240736756291520), (Int.ofNat 762404156514693614016), (Int.ofNat 664924164503874288768), (Int.ofNat 755127815154444328320), (Int.ofNat 867454995152448953856), (Int.ofNat 398216748588513896448), (Int.ofNat 354986971510341445632), (Int.ofNat 131553193471520265216), (Int.ofNat 22892947140737581056)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 18950760406674431), (Int.negSucc 950861181029462783), (Int.negSucc 11688698342611772927), (Int.negSucc 34810281208460477375), (Int.negSucc 84067911012128815871), (Int.negSucc 118873437426089955071), (Int.negSucc 27399889929619717631), (Int.negSucc 113672473027723846655), (Int.negSucc 22715184238048963583), (Int.negSucc 25804250372253514751), (Int.negSucc 12210447575999102975)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 26175095802731520), (Int.ofNat 625746076581438720), (Int.ofNat 3200207150589717888), (Int.ofNat 5057123987305747584), (Int.ofNat 14250582378541511424), (Int.negSucc 3233914458449156351), (Int.ofNat 6512206968106454016), (Int.negSucc 666763021230068735), (Int.ofNat 778864719534981120)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 8487390906851327), (Int.negSucc 148021274376972287), (Int.negSucc 124495885955414015), (Int.negSucc 737634653096560127), (Int.ofNat 147527399098478592), (Int.ofNat 251596475761674240)]]

theorem h2n89_arithmetic_row0 :
    (BiPoly.mul h2p2 h2p88).getD 0 []=h2p89.getD 0 [] := by
  decide +kernel

theorem h2n89_arithmetic_row1 :
    (BiPoly.mul h2p2 h2p88).getD 1 []=h2p89.getD 1 [] := by
  decide +kernel

theorem h2n89_arithmetic_row2 :
    (BiPoly.mul h2p2 h2p88).getD 2 []=h2p89.getD 2 [] := by
  decide +kernel

theorem h2n89_arithmetic_row3 :
    (BiPoly.mul h2p2 h2p88).getD 3 []=h2p89.getD 3 [] := by
  decide +kernel

theorem h2n89_arithmetic_row4 :
    (BiPoly.mul h2p2 h2p88).getD 4 []=h2p89.getD 4 [] := by
  decide +kernel

theorem h2n89_arithmetic_row5 :
    (BiPoly.mul h2p2 h2p88).getD 5 []=h2p89.getD 5 [] := by
  decide +kernel

theorem h2n89_arithmetic_row6 :
    (BiPoly.mul h2p2 h2p88).getD 6 []=h2p89.getD 6 [] := by
  decide +kernel

theorem h2n89_arithmetic_row7 :
    (BiPoly.mul h2p2 h2p88).getD 7 []=h2p89.getD 7 [] := by
  decide +kernel

theorem h2n89_arithmetic_row8 :
    (BiPoly.mul h2p2 h2p88).getD 8 []=h2p89.getD 8 [] := by
  decide +kernel

theorem h2n89_arithmetic_row9 :
    (BiPoly.mul h2p2 h2p88).getD 9 []=h2p89.getD 9 [] := by
  decide +kernel

theorem h2n89_arithmetic_row10 :
    (BiPoly.mul h2p2 h2p88).getD 10 []=h2p89.getD 10 [] := by
  decide +kernel

theorem h2n89_arithmetic_row11 :
    (BiPoly.mul h2p2 h2p88).getD 11 []=h2p89.getD 11 [] := by
  decide +kernel

theorem h2n89_arithmetic_row12 :
    (BiPoly.mul h2p2 h2p88).getD 12 []=h2p89.getD 12 [] := by
  decide +kernel

theorem h2n89_arithmetic_row13 :
    (BiPoly.mul h2p2 h2p88).getD 13 []=h2p89.getD 13 [] := by
  decide +kernel

theorem h2n89_arithmetic_row14 :
    (BiPoly.mul h2p2 h2p88).getD 14 []=h2p89.getD 14 [] := by
  decide +kernel

theorem h2n89_arithmetic_row15 :
    (BiPoly.mul h2p2 h2p88).getD 15 []=h2p89.getD 15 [] := by
  decide +kernel

theorem h2n89_arithmetic_row16 :
    (BiPoly.mul h2p2 h2p88).getD 16 []=h2p89.getD 16 [] := by
  decide +kernel

theorem h2n89_arithmetic_row17 :
    (BiPoly.mul h2p2 h2p88).getD 17 []=h2p89.getD 17 [] := by
  decide +kernel

theorem h2n89_arithmetic_row18 :
    (BiPoly.mul h2p2 h2p88).getD 18 []=h2p89.getD 18 [] := by
  decide +kernel

theorem h2n89_arithmetic_row19 :
    (BiPoly.mul h2p2 h2p88).getD 19 []=h2p89.getD 19 [] := by
  decide +kernel

theorem h2n89_arithmetic_row20 :
    (BiPoly.mul h2p2 h2p88).getD 20 []=h2p89.getD 20 [] := by
  decide +kernel

theorem h2n89_arithmetic_row21 :
    (BiPoly.mul h2p2 h2p88).getD 21 []=h2p89.getD 21 [] := by
  decide +kernel

theorem h2n89_arithmetic_row22 :
    (BiPoly.mul h2p2 h2p88).getD 22 []=h2p89.getD 22 [] := by
  decide +kernel

theorem h2n89_arithmetic : BiPoly.mul h2p2 h2p88=h2p89 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<23 at hk
    have hf : ∀ j : Fin 23, (BiPoly.mul h2p2 h2p88).getD j.val []=h2p89.getD j.val [] :=
      (fun j => Fin.cases h2n89_arithmetic_row0 (fun j => Fin.cases h2n89_arithmetic_row1 (fun j => Fin.cases h2n89_arithmetic_row2 (fun j => Fin.cases h2n89_arithmetic_row3 (fun j => Fin.cases h2n89_arithmetic_row4 (fun j => Fin.cases h2n89_arithmetic_row5 (fun j => Fin.cases h2n89_arithmetic_row6 (fun j => Fin.cases h2n89_arithmetic_row7 (fun j => Fin.cases h2n89_arithmetic_row8 (fun j => Fin.cases h2n89_arithmetic_row9 (fun j => Fin.cases h2n89_arithmetic_row10 (fun j => Fin.cases h2n89_arithmetic_row11 (fun j => Fin.cases h2n89_arithmetic_row12 (fun j => Fin.cases h2n89_arithmetic_row13 (fun j => Fin.cases h2n89_arithmetic_row14 (fun j => Fin.cases h2n89_arithmetic_row15 (fun j => Fin.cases h2n89_arithmetic_row16 (fun j => Fin.cases h2n89_arithmetic_row17 (fun j => Fin.cases h2n89_arithmetic_row18 (fun j => Fin.cases h2n89_arithmetic_row19 (fun j => Fin.cases h2n89_arithmetic_row20 (fun j => Fin.cases h2n89_arithmetic_row21 (fun j => Fin.cases h2n89_arithmetic_row22 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h2n89 : h2e89.toBi mapPolyEnv=h2p89 := by
  change BiPoly.mul (h2e2.toBi mapPolyEnv) (h2e88.toBi mapPolyEnv)=h2p89
  rw [h2n2, h2n88]
  exact h2n89_arithmetic

#print axioms h2n89_arithmetic
end StackSorting.RationalLift
