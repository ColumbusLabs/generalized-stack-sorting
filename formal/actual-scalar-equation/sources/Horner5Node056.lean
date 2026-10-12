import BivariateRowEquality
import Horner5Base
import Horner5Node055
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p56 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 25927113725406194688), (Int.ofNat 284666092835637767040), (Int.negSucc 429253894186091746559), (Int.negSucc 5450481310892409929087), (Int.negSucc 1341242333493375407615), (Int.ofNat 11416050359645702281344), (Int.ofNat 5705484204544075899648), (Int.negSucc 5310514554523172320895), (Int.negSucc 3021194503524257141759)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 338104259109984489983), (Int.negSucc 3551352579171075006719), (Int.ofNat 6571975668971153559552), (Int.ofNat 69810463202035549144320), (Int.ofNat 7173585826989361532928), (Int.negSucc 127882500154044340135679), (Int.negSucc 44726340821289976682495), (Int.ofNat 51891202694636484090624), (Int.ofNat 20535565914454324271616), (Int.negSucc 1051130833441739900927)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2086729492352113315584), (Int.ofNat 20740222836717165978912), (Int.negSucc 47573686302117448414463), (Int.negSucc 414788510301976960390655), (Int.ofNat 7340930874695478668544), (Int.ofNat 642346155043407005856192), (Int.ofNat 164232286570122108420096), (Int.negSucc 199251589570530569178623), (Int.negSucc 68925651098453010413567), (Int.negSucc 2656660360642348824287), (Int.ofNat 524152470433517874432)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 8096877671226613793279), (Int.negSucc 75082958575361129022335), (Int.ofNat 214734724756300889144640), (Int.ofNat 1508789405686653263854080), (Int.negSucc 142511265511708240415231), (Int.negSucc 1883772996339396802869503), (Int.negSucc 457237487387356039246463), (Int.ofNat 351315607913349262073856), (Int.ofNat 188796504669465209103360), (Int.ofNat 38564070517236205680768), (Int.negSucc 6104511590159926620863), (Int.ofNat 273448324025846880768)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 22105150562724917270976), (Int.ofNat 187995173067781474812480), (Int.negSucc 672236418462290310928895), (Int.negSucc 3745219739754789235999295), (Int.ofNat 365497136001889340413248), (Int.ofNat 3535763357872502192339136), (Int.ofNat 1298491724813030525269440), (Int.negSucc 125437427537319516443327), (Int.negSucc 458259680484779598890495), (Int.negSucc 117724260273912349877375), (Int.ofNat 11869703446580248458816), (Int.negSucc 770898544062886339199), (Int.ofNat 30401830276348861440)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 44975943096153790808447), (Int.negSucc 343820185793163164764943), (Int.ofNat 1540019256294353412067632), (Int.ofNat 6722899458943997024137152), (Int.ofNat 101052009031698673528320), (Int.negSucc 4392912681772961494521311), (Int.negSucc 3295733448808723969045151), (Int.negSucc 710049409063026939375551), (Int.ofNat 727943417811823527399168), (Int.ofNat 201549746546412767467632), (Int.ofNat 20236293857381054071536), (Int.negSucc 3386100137888715110783), (Int.ofNat 88460319371883224832), (Int.negSucc 158390098824038399)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 70395493915478486259648), (Int.ofNat 472548528978595745254848), (Int.negSucc 2661606920975903829418319), (Int.negSucc 9089682808831145277024095), (Int.negSucc 2701612842079881474455039), (Int.ofNat 3533595423047365147408512), (Int.ofNat 5968992918642968216098080), (Int.ofNat 1877762415588135343017408), (Int.negSucc 388866593422749724516799), (Int.negSucc 304278839220695877419327), (Int.negSucc 97104288805482787297487), (Int.ofNat 10624088536561932339744), (Int.negSucc 448701712336259025407), (Int.ofNat 5431373048767057920)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 86167884179366769818591), (Int.negSucc 493886002607164991789567), (Int.ofNat 3533350026484994574480048), (Int.ofNat 9657808862626410227489376), (Int.ofNat 7632386971214862656349504), (Int.negSucc 1208402251645373491768703), (Int.negSucc 6886061713374146156248415), (Int.negSucc 3169770513902652114211391), (Int.negSucc 790880110078786288983647), (Int.ofNat 401795769044198816949888), (Int.ofNat 128727963913193454929328), (Int.ofNat 3262726686423454248672), (Int.negSucc 813472586225090115839), (Int.ofNat 22198321878923796480)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 82944765047727669345408), (Int.ofNat 391175747114335238929248), (Int.negSucc 3639771621924627607839071), (Int.negSucc 8563714979053782470627663), (Int.negSucc 12271388211660700598020991), (Int.negSucc 2123116140547649869146431), (Int.ofNat 4277224966149379193504256), (Int.ofNat 4334194043455502204316000), (Int.ofNat 1865683631347348424154624), (Int.negSucc 170073431646359502322655), (Int.negSucc 84171365000228500694495), (Int.negSucc 38462520813140335964111), (Int.ofNat 2629370705980873596480), (Int.negSucc 37140354534660539903)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 62508159048635962831583), (Int.negSucc 228532041709361514936431), (Int.ofNat 2923596613914803781290352), (Int.ofNat 6843941436439803598068816), (Int.ofNat 13318614812438256087295056), (Int.ofNat 6106958804747405993447232), (Int.ofNat 128284382357815102789824), (Int.negSucc 4118327383339050729860447), (Int.negSucc 1997710056386183350461887), (Int.negSucc 487370675288766754309391), (Int.ofNat 45117905010133778282448), (Int.ofNat 41860721777771936765520), (Int.ofNat 1055122546288928077008), (Int.negSucc 164312092103039505791)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 36257202979059184024896), (Int.ofNat 89764994997949184707104), (Int.negSucc 1834467084613625565536207), (Int.negSucc 5170238460228148920879263), (Int.negSucc 10484492503078683473338367), (Int.negSucc 9160849995159064319725823), (Int.negSucc 3343453293681852613027199), (Int.ofNat 1717122756441781834969536), (Int.ofNat 1537939033009607546374464), (Int.ofNat 908600733207996369232320), (Int.ofNat 21188037450181059073296), (Int.negSucc 4170319599748445183519), (Int.negSucc 6800345786549092840703), (Int.ofNat 111541979912473464192)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 15553885318537780365119), (Int.negSucc 13923227995764223640543), (Int.ofNat 902239497537835184504784), (Int.ofNat 3580063283991410471995920), (Int.ofNat 6420916123330262040215280), (Int.ofNat 9219500695402082426926656), (Int.ofNat 4597212379721708029010112), (Int.ofNat 1197068202209855386023264), (Int.negSucc 860601322087568559901727), (Int.negSucc 656244234792212178004703), (Int.negSucc 152189712388235581344143), (Int.negSucc 19717952799183193661039), (Int.ofNat 4233219194165664086640), (Int.ofNat 364577553121083110784)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4447868000432092701120), (Int.negSucc 10246085031790301332607), (Int.negSucc 354002839366408968821471), (Int.negSucc 2102168648517414067754351), (Int.negSucc 3416784416855135455456799), (Int.negSucc 6468913167754473300797567), (Int.negSucc 4561810135440879009886847), (Int.negSucc 2467315143799900613608895), (Int.negSucc 47761551359238881675519), (Int.ofNat 184687960578261176652480), (Int.ofNat 189733760648392777040736), (Int.ofNat 20072764729035992209968), (Int.ofNat 2624638600706493670560), (Int.negSucc 291700959944565630527)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 518204772465663228479), (Int.ofNat 10497785411024858328336), (Int.ofNat 117879508615113034759440), (Int.ofNat 978267655673103074228640), (Int.ofNat 1770866377407672900441408), (Int.ofNat 3242397053182560931228896), (Int.ofNat 3575852981945243140342176), (Int.ofNat 2122603446899256092785440), (Int.ofNat 746122999900126456718496), (Int.ofNat 76248064912809506268096), (Int.negSucc 78147389622126421062719), (Int.negSucc 18543058531465232919743), (Int.negSucc 4149688651271483490719), (Int.negSucc 228947116495368795263)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 200446318613813568191), (Int.negSucc 5608051636117263603839), (Int.negSucc 37966418921502243660527), (Int.negSucc 345849777560652231793823), (Int.negSucc 880002707820736877710847), (Int.negSucc 1241391833606432061952127), (Int.negSucc 2071080638820852719602463), (Int.negSucc 1356253145161999212930047), (Int.negSucc 800769930294923366766335), (Int.negSucc 169978267480617361748159), (Int.negSucc 26555315826730051294847), (Int.ofNat 10426229476082857710720), (Int.ofNat 1814660200443673594368), (Int.ofNat 274874926999541846400)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 125004825690971147424), (Int.ofNat 2150524476977473195200), (Int.ofNat 13013181024423043893840), (Int.ofNat 91402106197798425059712), (Int.ofNat 366969319477643930150880), (Int.ofNat 434112664110038890935552), (Int.ofNat 833116654601010046957536), (Int.ofNat 743511127159025743639968), (Int.ofNat 478336409511329536477920), (Int.ofNat 175219448930133275805120), (Int.ofNat 46960060081272764628672), (Int.ofNat 2130413259584522848320), (Int.negSucc 4310689266418675391), (Int.negSucc 15918348312690412031)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 33276208761192098303), (Int.negSucc 623777675912513565983), (Int.negSucc 4324139045929215644831), (Int.negSucc 18882206865273128110127), (Int.negSucc 113891473699796542767551), (Int.negSucc 164686761410778277964927), (Int.negSucc 227919914180833446535103), (Int.negSucc 326525563914192072206495), (Int.negSucc 203987174181654360776255), (Int.negSucc 112911304339431824401727), (Int.negSucc 30950497568987436680063), (Int.negSucc 6454972020613671052991), (Int.negSucc 621515164957992878975), (Int.negSucc 67430237355952554239)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5035551563567387808), (Int.ofNat 134555072252824147824), (Int.ofNat 1181924538494875199568), (Int.ofNat 3685673884551900424848), (Int.ofNat 24257129836063261530384), (Int.ofNat 59116487672622726837504), (Int.ofNat 47984781625131832949376), (Int.ofNat 99264684157872554261376), (Int.ofNat 73489857122037723746112), (Int.ofNat 46103654926102971494592), (Int.ofNat 15388381795839639217344), (Int.ofNat 3992069661070847328000), (Int.ofNat 505923716336513735808), (Int.ofNat 28401024484178339328)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 409827347066403647), (Int.negSucc 20352636254798218367), (Int.negSucc 238700435499243637487), (Int.negSucc 821405588090745391199), (Int.negSucc 3330830484524513874815), (Int.negSucc 15650557611239280962303), (Int.negSucc 12057825858318058851071), (Int.negSucc 18040185070393874135039), (Int.negSucc 22180195242382801205375), (Int.negSucc 12817933143593695300799), (Int.negSucc 5756332051950423101567), (Int.negSucc 1420132314000133009151), (Int.negSucc 191091795671895708671), (Int.negSucc 4161014166684713471)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 13211464229758080), (Int.ofNat 1923855221968827552), (Int.ofNat 33117285383026655472), (Int.ofNat 171339203993237444880), (Int.ofNat 314058457466677367280), (Int.ofNat 2582435692219995021888), (Int.ofNat 3719825356174494046272), (Int.ofNat 1637361035229433470912), (Int.ofNat 4580345701261842547392), (Int.ofNat 2761056994179569760000), (Int.ofNat 1443179666798443267200), (Int.ofNat 346749291007924902912), (Int.ofNat 33632656729589343744), (Int.ofNat 201004653158129664)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 85663630596067199), (Int.negSucc 2861570590497098783), (Int.negSucc 24546823549475654735), (Int.negSucc 39276219390346554335), (Int.negSucc 212998625288946766079), (Int.negSucc 833585237043495599231), (Int.negSucc 133521058771310062655), (Int.negSucc 459768568941108091007), (Int.negSucc 472933842019525304063), (Int.negSucc 236939212187104499711), (Int.negSucc 53772100423242236927), (Int.negSucc 2154454925269966847)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 119392008047191296), (Int.ofNat 1938271424586678720), (Int.ofNat 6941220643701956448), (Int.ofNat 2528538363058387392), (Int.ofNat 99886099738721742144), (Int.ofNat 55067800297854912768), (Int.negSucc 11124879287063727743), (Int.ofNat 50355975105345129984), (Int.ofNat 26861371162779737088), (Int.ofNat 3705895891065544704)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 59285466434972159), (Int.negSucc 634922407981655423), (Int.ofNat 147303313394518080), (Int.negSucc 3648651027849104255), (Int.negSucc 12530743179486531839), (Int.ofNat 7194164140116974592), (Int.negSucc 1994821231978363391), (Int.negSucc 1752445618953707519)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 9548314770207744), (Int.ofNat 81655174721422080), (Int.negSucc 239919682769801855), (Int.ofNat 1019169996018647040), (Int.negSucc 566092070463767039)]]

theorem h5n56_arithmetic_row0 :
    (BiPoly.mul h5p5 h5p55).getD 0 []=h5p56.getD 0 [] := by
  decide +kernel

theorem h5n56_arithmetic_row1 :
    (BiPoly.mul h5p5 h5p55).getD 1 []=h5p56.getD 1 [] := by
  decide +kernel

theorem h5n56_arithmetic_row2 :
    (BiPoly.mul h5p5 h5p55).getD 2 []=h5p56.getD 2 [] := by
  decide +kernel

theorem h5n56_arithmetic_row3 :
    (BiPoly.mul h5p5 h5p55).getD 3 []=h5p56.getD 3 [] := by
  decide +kernel

theorem h5n56_arithmetic_row4 :
    (BiPoly.mul h5p5 h5p55).getD 4 []=h5p56.getD 4 [] := by
  decide +kernel

theorem h5n56_arithmetic_row5 :
    (BiPoly.mul h5p5 h5p55).getD 5 []=h5p56.getD 5 [] := by
  decide +kernel

theorem h5n56_arithmetic_row6 :
    (BiPoly.mul h5p5 h5p55).getD 6 []=h5p56.getD 6 [] := by
  decide +kernel

theorem h5n56_arithmetic_row7 :
    (BiPoly.mul h5p5 h5p55).getD 7 []=h5p56.getD 7 [] := by
  decide +kernel

theorem h5n56_arithmetic_row8 :
    (BiPoly.mul h5p5 h5p55).getD 8 []=h5p56.getD 8 [] := by
  decide +kernel

theorem h5n56_arithmetic_row9 :
    (BiPoly.mul h5p5 h5p55).getD 9 []=h5p56.getD 9 [] := by
  decide +kernel

theorem h5n56_arithmetic_row10 :
    (BiPoly.mul h5p5 h5p55).getD 10 []=h5p56.getD 10 [] := by
  decide +kernel

theorem h5n56_arithmetic_row11 :
    (BiPoly.mul h5p5 h5p55).getD 11 []=h5p56.getD 11 [] := by
  decide +kernel

theorem h5n56_arithmetic_row12 :
    (BiPoly.mul h5p5 h5p55).getD 12 []=h5p56.getD 12 [] := by
  decide +kernel

theorem h5n56_arithmetic_row13 :
    (BiPoly.mul h5p5 h5p55).getD 13 []=h5p56.getD 13 [] := by
  decide +kernel

theorem h5n56_arithmetic_row14 :
    (BiPoly.mul h5p5 h5p55).getD 14 []=h5p56.getD 14 [] := by
  decide +kernel

theorem h5n56_arithmetic_row15 :
    (BiPoly.mul h5p5 h5p55).getD 15 []=h5p56.getD 15 [] := by
  decide +kernel

theorem h5n56_arithmetic_row16 :
    (BiPoly.mul h5p5 h5p55).getD 16 []=h5p56.getD 16 [] := by
  decide +kernel

theorem h5n56_arithmetic_row17 :
    (BiPoly.mul h5p5 h5p55).getD 17 []=h5p56.getD 17 [] := by
  decide +kernel

theorem h5n56_arithmetic_row18 :
    (BiPoly.mul h5p5 h5p55).getD 18 []=h5p56.getD 18 [] := by
  decide +kernel

theorem h5n56_arithmetic_row19 :
    (BiPoly.mul h5p5 h5p55).getD 19 []=h5p56.getD 19 [] := by
  decide +kernel

theorem h5n56_arithmetic_row20 :
    (BiPoly.mul h5p5 h5p55).getD 20 []=h5p56.getD 20 [] := by
  decide +kernel

theorem h5n56_arithmetic_row21 :
    (BiPoly.mul h5p5 h5p55).getD 21 []=h5p56.getD 21 [] := by
  decide +kernel

theorem h5n56_arithmetic_row22 :
    (BiPoly.mul h5p5 h5p55).getD 22 []=h5p56.getD 22 [] := by
  decide +kernel

theorem h5n56_arithmetic_row23 :
    (BiPoly.mul h5p5 h5p55).getD 23 []=h5p56.getD 23 [] := by
  decide +kernel

theorem h5n56_arithmetic : BiPoly.mul h5p5 h5p55=h5p56 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<24 at hk
    have hf : ∀ j : Fin 24, (BiPoly.mul h5p5 h5p55).getD j.val []=h5p56.getD j.val [] :=
      (fun j => Fin.cases h5n56_arithmetic_row0 (fun j => Fin.cases h5n56_arithmetic_row1 (fun j => Fin.cases h5n56_arithmetic_row2 (fun j => Fin.cases h5n56_arithmetic_row3 (fun j => Fin.cases h5n56_arithmetic_row4 (fun j => Fin.cases h5n56_arithmetic_row5 (fun j => Fin.cases h5n56_arithmetic_row6 (fun j => Fin.cases h5n56_arithmetic_row7 (fun j => Fin.cases h5n56_arithmetic_row8 (fun j => Fin.cases h5n56_arithmetic_row9 (fun j => Fin.cases h5n56_arithmetic_row10 (fun j => Fin.cases h5n56_arithmetic_row11 (fun j => Fin.cases h5n56_arithmetic_row12 (fun j => Fin.cases h5n56_arithmetic_row13 (fun j => Fin.cases h5n56_arithmetic_row14 (fun j => Fin.cases h5n56_arithmetic_row15 (fun j => Fin.cases h5n56_arithmetic_row16 (fun j => Fin.cases h5n56_arithmetic_row17 (fun j => Fin.cases h5n56_arithmetic_row18 (fun j => Fin.cases h5n56_arithmetic_row19 (fun j => Fin.cases h5n56_arithmetic_row20 (fun j => Fin.cases h5n56_arithmetic_row21 (fun j => Fin.cases h5n56_arithmetic_row22 (fun j => Fin.cases h5n56_arithmetic_row23 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n56 : h5e56.toBi mapPolyEnv=h5p56 := by
  change BiPoly.mul (h5e5.toBi mapPolyEnv) (h5e55.toBi mapPolyEnv)=h5p56
  rw [h5n5, h5n55]
  exact h5n56_arithmetic

#print axioms h5n56_arithmetic
end StackSorting.RationalLift
