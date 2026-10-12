import BivariateRowEquality
import Horner4Base
import Horner4Node246
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p247 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 164543096537170272000), (Int.ofNat 1408764073867712392320), (Int.ofNat 2897209249712225015040), (Int.negSucc 2767854879232592451839), (Int.negSucc 9496592722592073043199), (Int.ofNat 1037873524477946232960), (Int.ofNat 6113623095455743929600)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2071012966765937585279), (Int.negSucc 17548849593709041796415), (Int.negSucc 35487379345401807378623), (Int.ofNat 33084595792722380014080), (Int.ofNat 105429781442069364029184), (Int.negSucc 21238177199049909145151), (Int.negSucc 59147358163602691958207), (Int.ofNat 3183286520471912611200)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 12383040814949665581120), (Int.ofNat 102811097235985830375264), (Int.ofNat 203706514044407668683744), (Int.negSucc 178410405641586574186367), (Int.negSucc 544182105733991341122815), (Int.ofNat 130100409408566811680352), (Int.ofNat 246063564545009645548512), (Int.negSucc 3784445548024197201983), (Int.negSucc 694064057480295646463)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 46746593492593597981919), (Int.negSucc 376095525291768652009199), (Int.negSucc 731426411079851453177759), (Int.ofNat 549246878509360083799248), (Int.ofNat 1719688713515628105992256), (Int.negSucc 345202361759746219374287), (Int.negSucc 575495740220090767687583), (Int.negSucc 110720451355384293620495), (Int.ofNat 17626538291950584817632), (Int.negSucc 736655434427517935615)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 124769758030025010845760), (Int.ofNat 962731770401862525964320), (Int.ofNat 1854364968494845317021888), (Int.negSucc 979141754911710229825823), (Int.negSucc 3700576877226651411875135), (Int.ofNat 192314445377734037660832), (Int.ofNat 831363523628509086454656), (Int.ofNat 610303114108099680134112), (Int.negSucc 77893450797212999141183), (Int.ofNat 4910329031232397077504), (Int.negSucc 156949718159973961727)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 249634552306309453848959), (Int.negSucc 1833782874624223868121407), (Int.negSucc 3560208613795489563166607), (Int.ofNat 690849217647501658268976), (Int.ofNat 5670479360854022667614928), (Int.ofNat 1451841440893821812315520), (Int.negSucc 739363945057655366765807), (Int.negSucc 1464954191354901859175375), (Int.ofNat 58488369337842752334960), (Int.ofNat 2271556017233286135840), (Int.ofNat 75845519617268438784), (Int.negSucc 10275550794496677887)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 387082556739213662622960), (Int.ofNat 2701991643029446642333128), (Int.ofNat 5426422256865116303238072), (Int.ofNat 1271143449732421473806616), (Int.negSucc 6092065174773841262548967), (Int.negSucc 5042453287013756065604855), (Int.ofNat 103494089718857939946696), (Int.ofNat 1791255572628958996190664), (Int.ofNat 416661384953446009047384), (Int.negSucc 63600481806724551360527), (Int.ofNat 3374454513014562755904), (Int.negSucc 62226551097073296383), (Int.ofNat 55207443051171840)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 474212849083516792474559), (Int.negSucc 3165455074444660854165647), (Int.negSucc 6788672450263664332760519), (Int.negSucc 4788839938806410272398527), (Int.ofNat 3777522629876479141004760), (Int.ofNat 8617684941386693852451312), (Int.ofNat 1473573236243889566229384), (Int.negSucc 720418927579919937894191), (Int.negSucc 1326181106059097182182647), (Int.ofNat 108919922565137405991888), (Int.negSucc 3830123141908721638079), (Int.ofNat 128203566753233132160), (Int.negSucc 1791350851795794431)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 463774084399831340884400), (Int.ofNat 3011091316751166285723736), (Int.ofNat 7125637068255320974821544), (Int.ofNat 8190038468204491974722168), (Int.ofNat 916540486260071154893712), (Int.negSucc 8833554042758338953065615), (Int.negSucc 4086832624242102231828423), (Int.negSucc 1112221319997911600642983), (Int.ofNat 1590451074226477332090736), (Int.ofNat 122426885596950547270888), (Int.negSucc 21355289128051466400271), (Int.ofNat 870450785016816276160), (Int.negSucc 11456919429725678847)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 363531599068885831861599), (Int.negSucc 2363805052986326081860575), (Int.negSucc 6347863504180423300518135), (Int.negSucc 9600786303684941052940911), (Int.negSucc 5868394883440532622010271), (Int.ofNat 4582380215096598679763712), (Int.ofNat 6201994574434928910148904), (Int.ofNat 2328028384426516127456960), (Int.negSucc 371711629426990365490047), (Int.negSucc 594346302753178186732831), (Int.ofNat 43978441886294405217200), (Int.negSucc 1015292848250984817567), (Int.ofNat 6590742981116430080)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 228140656528955831865440), (Int.ofNat 1548525751539631702672352), (Int.ofNat 4812005878922793616473816), (Int.ofNat 8603501904364740437737872), (Int.ofNat 8582527336459862477276640), (Int.ofNat 1470392992854223269647568), (Int.negSucc 5514353214704195264637879), (Int.negSucc 2613394206594963994133655), (Int.negSucc 1250994772296323170358855), (Int.ofNat 663234619584249974459336), (Int.ofNat 25554173007571888592072), (Int.negSucc 4162775186679048088079), (Int.ofNat 112181026038932225664)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 113956891897623408856799), (Int.negSucc 850090423311958472779855), (Int.negSucc 3091365810282733575418559), (Int.negSucc 6246291339077806120696807), (Int.negSucc 8184512059918308471461431), (Int.negSucc 5537987701334250735040231), (Int.ofNat 1979402845487414488002544), (Int.ofNat 2297691616455237848379320), (Int.ofNat 1673741851035811385809552), (Int.negSucc 33573926697908025895607), (Int.negSucc 144822626541348006958791), (Int.ofNat 6250677683000159375680), (Int.ofNat 8406508082347568608)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 44806741615470419134880), (Int.ofNat 389340560908501543324688), (Int.ofNat 1668222460008001379435312), (Int.ofNat 3815640282703103414989504), (Int.ofNat 5856812455901565507248672), (Int.ofNat 6102513330037725511646120), (Int.ofNat 1706495215209809149647576), (Int.negSucc 1333435747583171195527999), (Int.negSucc 998819811066001769224831), (Int.negSucc 572321877526852398362775), (Int.ofNat 124196113278103976283952), (Int.ofNat 6326756731912064074552), (Int.negSucc 428365428690970230031)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 13624724149812837465279), (Int.negSucc 146763401879988156755583), (Int.negSucc 746595787249802631118847), (Int.negSucc 1995448576862700230109135), (Int.negSucc 3361369186276495281974799), (Int.negSucc 4383084053770480258440551), (Int.negSucc 3191947989482942016481423), (Int.negSucc 40238174895163062227599), (Int.ofNat 288188064291079235997936), (Int.ofNat 529603716761305732657048), (Int.ofNat 36109533168497170487848), (Int.negSucc 16980090546890163611087), (Int.ofNat 62783602812916975488)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3118056909014680517040), (Int.ofNat 44535111378980134100296), (Int.ofNat 272488512822171349198344), (Int.ofNat 887099428428362904176728), (Int.ofNat 1629136042890332518153064), (Int.ofNat 2343549547586511239660368), (Int.ofNat 2586452864548604587429584), (Int.ofNat 967887573012389777763072), (Int.ofNat 76599801265485895536640), (Int.negSucc 153577521695169961446135), (Int.negSucc 121241279999944952884607), (Int.ofNat 6034002802886975165248), (Int.ofNat 767478476041662972096)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 514687631951227761279), (Int.negSucc 10549821043069182790383), (Int.negSucc 79371020507168026208583), (Int.negSucc 326181211156848288923183), (Int.negSucc 687580149513501509724295), (Int.negSucc 1005136598150046721899511), (Int.negSucc 1364118228613402938189319), (Int.negSucc 1015855489325265031473431), (Int.negSucc 238903829035339962216167), (Int.negSucc 63413554340604067591487), (Int.ofNat 66852447599176120402704), (Int.ofNat 9655803926712832606896), (Int.negSucc 448736302681374005087)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 57096838177233380720), (Int.ofNat 1870472324520798237944), (Int.ofNat 17940155576847542399976), (Int.ofNat 95466171502405677539608), (Int.ofNat 250033653581274309501664), (Int.ofNat 372080023461020875854408), (Int.ofNat 518456781645862483475664), (Int.ofNat 590647217209653116047608), (Int.ofNat 255850920745289292558432), (Int.ofNat 85278247680623689730976), (Int.ofNat 3001526149646398877856), (Int.negSucc 9482087470256063720543), (Int.negSucc 435248456116891436351)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3728030086839619039), (Int.negSucc 232997221179855331103), (Int.negSucc 3027797310267553112631), (Int.negSucc 21285514387448497338735), (Int.negSucc 74528693257268109651311), (Int.negSucc 124410576764050492408039), (Int.negSucc 154807294358352240364199), (Int.negSucc 220757745756204911300591), (Int.negSucc 163865608086797677445903), (Int.negSucc 55361646165419759988335), (Int.negSucc 20018048900965002895103), (Int.ofNat 1434653851708628787936), (Int.ofNat 481467770536403969856)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 103655370912350400), (Int.ofNat 18207510141344242608), (Int.ofNat 359810624448305350728), (Int.ofNat 3430524638322654388224), (Int.ofNat 17030751630859959751200), (Int.ofNat 36351975360971127669432), (Int.ofNat 41265813227806642993440), (Int.ofNat 55482973961946471650112), (Int.ofNat 65348410427569839930432), (Int.ofNat 29328268052333698434528), (Int.ofNat 11389772681643369937248), (Int.ofNat 1993595940665302673088), (Int.negSucc 49828604523749961983)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 674757220353756479), (Int.negSucc 27038643241117581071), (Int.negSucc 370973405449346489015), (Int.negSucc 2769915656716269387671), (Int.negSucc 8440835690129615578079), (Int.negSucc 10672972323849207434639), (Int.negSucc 10152600708661377952559), (Int.negSucc 15971595984409364011871), (Int.negSucc 11576672847750320950463), (Int.negSucc 4094216253139523875775), (Int.negSucc 1323675992542660734527), (Int.negSucc 112603870466111424383)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 977794378678802880), (Int.ofNat 23590850299521071184), (Int.ofNat 290450259414275160240), (Int.ofNat 1399357853054703588384), (Int.ofNat 2427678054444205365984), (Int.ofNat 1748760013576781012448), (Int.ofNat 2221936310151492254208), (Int.ofNat 2898248506685678774016), (Int.ofNat 1200192790744645126272), (Int.ofNat 397635891035753698560), (Int.ofNat 58225350717642580992)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 639559598975153855), (Int.negSucc 16301119045596422255), (Int.negSucc 146591458971395348303), (Int.negSucc 403775559761734408895), (Int.negSucc 348027007363738364447), (Int.negSucc 150244835404492823615), (Int.negSucc 387654358452637010687), (Int.negSucc 262944558094332506111), (Int.negSucc 76167809132980980095), (Int.negSucc 11178085267667596031)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 276967364468595840), (Int.ofNat 7757883590853528864), (Int.ofNat 41344352263779177312), (Int.ofNat 58263463542914371008), (Int.ofNat 8647311109933269504), (Int.ofNat 13923431925761821824), (Int.ofNat 33378883979972241024), (Int.ofNat 10368332974334663424), (Int.ofNat 749350492626309120)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 84095217331487999), (Int.negSucc 2006968723540840511), (Int.negSucc 5601765575524474943), (Int.negSucc 2275326224793613439), (Int.ofNat 2485619326037798784), (Int.negSucc 1695803677213070591), (Int.negSucc 749350492626309119)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 11553998772939264), (Int.ofNat 208977824369102976), (Int.ofNat 250708402437883776), (Int.negSucc 242062502417130239)]]

theorem h4n247_arithmetic_row0 :
    (BiPoly.mul h4p5 h4p246).getD 0 []=h4p247.getD 0 [] := by
  decide +kernel

theorem h4n247_arithmetic_row1 :
    (BiPoly.mul h4p5 h4p246).getD 1 []=h4p247.getD 1 [] := by
  decide +kernel

theorem h4n247_arithmetic_row2 :
    (BiPoly.mul h4p5 h4p246).getD 2 []=h4p247.getD 2 [] := by
  decide +kernel

theorem h4n247_arithmetic_row3 :
    (BiPoly.mul h4p5 h4p246).getD 3 []=h4p247.getD 3 [] := by
  decide +kernel

theorem h4n247_arithmetic_row4 :
    (BiPoly.mul h4p5 h4p246).getD 4 []=h4p247.getD 4 [] := by
  decide +kernel

theorem h4n247_arithmetic_row5 :
    (BiPoly.mul h4p5 h4p246).getD 5 []=h4p247.getD 5 [] := by
  decide +kernel

theorem h4n247_arithmetic_row6 :
    (BiPoly.mul h4p5 h4p246).getD 6 []=h4p247.getD 6 [] := by
  decide +kernel

theorem h4n247_arithmetic_row7 :
    (BiPoly.mul h4p5 h4p246).getD 7 []=h4p247.getD 7 [] := by
  decide +kernel

theorem h4n247_arithmetic_row8 :
    (BiPoly.mul h4p5 h4p246).getD 8 []=h4p247.getD 8 [] := by
  decide +kernel

theorem h4n247_arithmetic_row9 :
    (BiPoly.mul h4p5 h4p246).getD 9 []=h4p247.getD 9 [] := by
  decide +kernel

theorem h4n247_arithmetic_row10 :
    (BiPoly.mul h4p5 h4p246).getD 10 []=h4p247.getD 10 [] := by
  decide +kernel

theorem h4n247_arithmetic_row11 :
    (BiPoly.mul h4p5 h4p246).getD 11 []=h4p247.getD 11 [] := by
  decide +kernel

theorem h4n247_arithmetic_row12 :
    (BiPoly.mul h4p5 h4p246).getD 12 []=h4p247.getD 12 [] := by
  decide +kernel

theorem h4n247_arithmetic_row13 :
    (BiPoly.mul h4p5 h4p246).getD 13 []=h4p247.getD 13 [] := by
  decide +kernel

theorem h4n247_arithmetic_row14 :
    (BiPoly.mul h4p5 h4p246).getD 14 []=h4p247.getD 14 [] := by
  decide +kernel

theorem h4n247_arithmetic_row15 :
    (BiPoly.mul h4p5 h4p246).getD 15 []=h4p247.getD 15 [] := by
  decide +kernel

theorem h4n247_arithmetic_row16 :
    (BiPoly.mul h4p5 h4p246).getD 16 []=h4p247.getD 16 [] := by
  decide +kernel

theorem h4n247_arithmetic_row17 :
    (BiPoly.mul h4p5 h4p246).getD 17 []=h4p247.getD 17 [] := by
  decide +kernel

theorem h4n247_arithmetic_row18 :
    (BiPoly.mul h4p5 h4p246).getD 18 []=h4p247.getD 18 [] := by
  decide +kernel

theorem h4n247_arithmetic_row19 :
    (BiPoly.mul h4p5 h4p246).getD 19 []=h4p247.getD 19 [] := by
  decide +kernel

theorem h4n247_arithmetic_row20 :
    (BiPoly.mul h4p5 h4p246).getD 20 []=h4p247.getD 20 [] := by
  decide +kernel

theorem h4n247_arithmetic_row21 :
    (BiPoly.mul h4p5 h4p246).getD 21 []=h4p247.getD 21 [] := by
  decide +kernel

theorem h4n247_arithmetic_row22 :
    (BiPoly.mul h4p5 h4p246).getD 22 []=h4p247.getD 22 [] := by
  decide +kernel

theorem h4n247_arithmetic_row23 :
    (BiPoly.mul h4p5 h4p246).getD 23 []=h4p247.getD 23 [] := by
  decide +kernel

theorem h4n247_arithmetic_row24 :
    (BiPoly.mul h4p5 h4p246).getD 24 []=h4p247.getD 24 [] := by
  decide +kernel

theorem h4n247_arithmetic : BiPoly.mul h4p5 h4p246=h4p247 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<25 at hk
    have hf : ∀ j : Fin 25, (BiPoly.mul h4p5 h4p246).getD j.val []=h4p247.getD j.val [] :=
      (fun j => Fin.cases h4n247_arithmetic_row0 (fun j => Fin.cases h4n247_arithmetic_row1 (fun j => Fin.cases h4n247_arithmetic_row2 (fun j => Fin.cases h4n247_arithmetic_row3 (fun j => Fin.cases h4n247_arithmetic_row4 (fun j => Fin.cases h4n247_arithmetic_row5 (fun j => Fin.cases h4n247_arithmetic_row6 (fun j => Fin.cases h4n247_arithmetic_row7 (fun j => Fin.cases h4n247_arithmetic_row8 (fun j => Fin.cases h4n247_arithmetic_row9 (fun j => Fin.cases h4n247_arithmetic_row10 (fun j => Fin.cases h4n247_arithmetic_row11 (fun j => Fin.cases h4n247_arithmetic_row12 (fun j => Fin.cases h4n247_arithmetic_row13 (fun j => Fin.cases h4n247_arithmetic_row14 (fun j => Fin.cases h4n247_arithmetic_row15 (fun j => Fin.cases h4n247_arithmetic_row16 (fun j => Fin.cases h4n247_arithmetic_row17 (fun j => Fin.cases h4n247_arithmetic_row18 (fun j => Fin.cases h4n247_arithmetic_row19 (fun j => Fin.cases h4n247_arithmetic_row20 (fun j => Fin.cases h4n247_arithmetic_row21 (fun j => Fin.cases h4n247_arithmetic_row22 (fun j => Fin.cases h4n247_arithmetic_row23 (fun j => Fin.cases h4n247_arithmetic_row24 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n247 : h4e247.toBi mapPolyEnv=h4p247 := by
  change BiPoly.mul (h4e5.toBi mapPolyEnv) (h4e246.toBi mapPolyEnv)=h4p247
  rw [h4n5, h4n246]
  exact h4n247_arithmetic

#print axioms h4n247_arithmetic
end StackSorting.RationalLift
