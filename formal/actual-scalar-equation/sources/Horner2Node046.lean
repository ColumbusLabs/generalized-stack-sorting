import BivariateRowEquality
import Horner2Base
import Horner2Node045
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p46 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 8642371241802064895), (Int.negSucc 86246326370077190783), (Int.ofNat 229330957765441106304), (Int.ofNat 1587496145865362203392), (Int.negSucc 1140415368034237067519), (Int.negSucc 2664934751847663692927), (Int.ofNat 763106683666305059712), (Int.ofNat 1007064834508085713920)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 104059048461526098432), (Int.ofNat 993478818225421713024), (Int.negSucc 2954806416783698459903), (Int.negSucc 18727851838029455718143), (Int.ofNat 15196241194332098139648), (Int.ofNat 24766324105168351545984), (Int.negSucc 9094437147738720925439), (Int.negSucc 7195565582632021390847), (Int.ofNat 350376944480579966976)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 591517448989178340095), (Int.negSucc 5328411345024455273183), (Int.ofNat 18231500362279906284768), (Int.ofNat 101303484567016291460640), (Int.negSucc 88554220330916019543839), (Int.negSucc 100794840578384630862239), (Int.ofNat 36956307907271873796768), (Int.ofNat 22265323033606294538592), (Int.ofNat 1060270943691955566240), (Int.negSucc 174717490144505958143)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2107441774753026257664), (Int.ofNat 17591799738676228143264), (Int.negSucc 70938540961829951573375), (Int.negSucc 330687776366704844917343), (Int.ofNat 289637311206358238845248), (Int.ofNat 237492180328389397915680), (Int.negSucc 48123376625332177703423), (Int.negSucc 46716502978844615115935), (Int.negSucc 15155394300618499018943), (Int.ofNat 2125986638061924500544), (Int.negSucc 91149441341948960255)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 5260941746155279499327), (Int.negSucc 39812316204428983961567), (Int.ofNat 192952581396695802697824), (Int.ofNat 724766222154862431051264), (Int.negSucc 556961289615800639010431), (Int.negSucc 384134316013310693853599), (Int.negSucc 96819635549698325606303), (Int.ofNat 91915608416626882638144), (Int.ofNat 45682224111014484639744), (Int.negSucc 4314817381648443513407), (Int.ofNat 267100124779745066880), (Int.negSucc 10133943425449620479)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 9731039285895984103488), (Int.ofNat 65063373107396086856592), (Int.negSucc 385450543808818088181311), (Int.negSucc 1130749720350985155479807), (Int.ofNat 540104427724618291959936), (Int.ofNat 540065483519724845693568), (Int.ofNat 461692697200151485048512), (Int.negSucc 133093952429182289285183), (Int.negSucc 63871629397077735208127), (Int.negSucc 7626436833374964127823), (Int.ofNat 1148105672361024504192), (Int.negSucc 29539569823569087743), (Int.ofNat 52796699608012800)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 13734125352596844649727), (Int.negSucc 78718677866205650245295), (Int.ofNat 580470441049355505203424), (Int.ofNat 1318674108210041098324800), (Int.ofNat 121967933541204351786816), (Int.negSucc 759767591037267888562751), (Int.negSucc 768204017976903365088095), (Int.ofNat 9189260351675961463776), (Int.ofNat 56561308058829544833696), (Int.ofNat 37238534848027450178256), (Int.negSucc 3722332907172163241567), (Int.ofNat 151430491827950040576), (Int.negSucc 1810457682922352639)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 14988502707192078623136), (Int.ofNat 70921486962323935061424), (Int.negSucc 668234388074633288018015), (Int.negSucc 1232361124590795689486975), (Int.negSucc 1189799932272954177509375), (Int.ofNat 832833091784144119536192), (Int.ofNat 694316794697001234125184), (Int.ofNat 371462636955558765409056), (Int.negSucc 51274625537133790914143), (Int.negSucc 45418762629571697890895), (Int.negSucc 1212891581998283660447), (Int.ofNat 276746511685082284800), (Int.negSucc 7399440626307932159)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 12659752308717144491999), (Int.negSucc 46810676433737333422991), (Int.ofNat 591833495667313248018000), (Int.ofNat 1030377039426485219370912), (Int.ofNat 1870285765520794135793376), (Int.negSucc 329747293554100059875039), (Int.negSucc 401677567132025103834527), (Int.negSucc 671591143730916865528415), (Int.negSucc 1578025588666400103935), (Int.ofNat 12850406841214536320592), (Int.ofNat 13993823243530013583792), (Int.negSucc 896236460798152644287), (Int.ofNat 12380118178220179968)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 8176300707494843118528), (Int.ofNat 21190370095221661770624), (Int.negSucc 403889079066176340849407), (Int.negSucc 847047693653939639135951), (Int.negSucc 1722204811638018254169023), (Int.negSucc 643195416831883803521759), (Int.ofNat 198756388913920332090624), (Int.ofNat 502428261801513045667776), (Int.ofNat 161897064738548337715584), (Int.ofNat 13410233865588450041472), (Int.negSucc 14455712292103029218495), (Int.negSucc 394098094619102347631), (Int.ofNat 54770697367679835264)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3909433618858218223103), (Int.negSucc 4821861285236514908639), (Int.ofNat 212421810423602029237968), (Int.ofNat 663943315998507971919168), (Int.ofNat 1108682706723034931691264), (Int.ofNat 1301738541498102704695584), (Int.ofNat 11502278643101831737440), (Int.negSucc 81448268988849397726175), (Int.negSucc 269301010609138113349727), (Int.negSucc 20155666594605559686239), (Int.negSucc 1362724847557822556687), (Int.ofNat 2358733286188201936896), (Int.negSucc 37180659970824488063)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1275194820654375231936), (Int.negSucc 1455980107302815593727), (Int.negSucc 86868708648373550003231), (Int.negSucc 442542403350255302076239), (Int.negSucc 589080264370130446304255), (Int.negSucc 1182348092599127657975711), (Int.negSucc 338553755331673186623551), (Int.negSucc 141917247727128006443711), (Int.ofNat 159483344480512746394560), (Int.ofNat 39109067188952419920768), (Int.ofNat 10258112092901617970592), (Int.negSucc 1326727873652351480015), (Int.negSucc 121525851040361036927)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 207427846156322335103), (Int.ofNat 2166809416116940518912), (Int.ofNat 28965428390979165751680), (Int.ofNat 229215051097903554756864), (Int.ofNat 320632823483677817424480), (Int.ofNat 653323473168685624865664), (Int.ofNat 528726149979934191806400), (Int.ofNat 151794983559571339619520), (Int.ofNat 23608878040687700666880), (Int.negSucc 46062464377822339630271), (Int.negSucc 6924010412073634746047), (Int.negSucc 1093639037924047470623), (Int.ofNat 97233653314855210176)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 34692922001101258943), (Int.negSucc 1297759465556910998255), (Int.negSucc 9029981681834934836543), (Int.negSucc 87844185777962535149471), (Int.negSucc 181811783207583947573183), (Int.negSucc 245663761351250737970783), (Int.negSucc 417561082650562783670207), (Int.negSucc 138178416089617907638751), (Int.negSucc 86920372503069877267199), (Int.ofNat 15441886487644368880896), (Int.ofNat 3683232974324136727296), (Int.ofNat 1404147498240226775328), (Int.ofNat 76315705498456265088)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 32122517536836597120), (Int.ofNat 539468562278673605904), (Int.ofNat 3086022729720472777728), (Int.ofNat 24353050679201069337408), (Int.ofNat 87169402053460608993024), (Int.ofNat 80964114464099340353568), (Int.ofNat 191835015825622115843712), (Int.ofNat 122070949805426380827552), (Int.ofNat 57931987789811530827360), (Int.ofNat 14169321191371958636256), (Int.negSucc 1634316274804471477343), (Int.negSucc 436946052316254317567), (Int.negSucc 91624975666513948799)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 9545757693487118687), (Int.negSucc 167827172353663673807), (Int.negSucc 1083877106066878179743), (Int.negSucc 5030440947331527502751), (Int.negSucc 30123263491755840221183), (Int.negSucc 33616843414157783070431), (Int.negSucc 52253692293890116738367), (Int.negSucc 73512400287025416980735), (Int.negSucc 28001081760272897684543), (Int.negSucc 16236080025066235614239), (Int.negSucc 1051589610162490739327), (Int.negSucc 95494195348604527679), (Int.ofNat 5306116104230137344)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1546311893576914080), (Int.ofNat 38552407723597267440), (Int.ofNat 318950168185929767760), (Int.ofNat 944677839573585432864), (Int.ofNat 6895883235269421935136), (Int.ofNat 14382860487498887649408), (Int.ofNat 9336751945555477790592), (Int.ofNat 25992702405483129297504), (Int.ofNat 14001940561462093276704), (Int.ofNat 7399080859948945909632), (Int.ofNat 1866162052884375577728), (Int.ofNat 190001091971576912256), (Int.ofNat 22476745785317518080)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 132205294278881855), (Int.negSucc 6167077733065233311), (Int.negSucc 68857600245963398783), (Int.negSucc 215022521697751309967), (Int.negSucc 974804188387247265023), (Int.negSucc 4347831214988107364735), (Int.negSucc 2310344047833692494463), (Int.negSucc 4785181599307362961823), (Int.negSucc 5709496879909785010175), (Int.negSucc 2259307235508926245055), (Int.negSucc 1003991310219911249663), (Int.negSucc 136697484832127614079), (Int.negSucc 9467008161392779775)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4403821409919360), (Int.ofNat 612730530457586784), (Int.ofNat 10096481056660226928), (Int.ofNat 48682859942503593504), (Int.ofNat 86789779845087099744), (Int.ofNat 782231542246565856288), (Int.ofNat 926699696025761266272), (Int.ofNat 301513728131500483584), (Int.ofNat 1382387806086314908032), (Int.ofNat 630949339602657280512), (Int.ofNat 283836700827572503680), (Int.ofNat 52843252340344218624), (Int.ofNat 1387004722228237824)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 28554543532022399), (Int.negSucc 914059527483302495), (Int.negSucc 7516148527758918959), (Int.negSucc 10380224116046437055), (Int.negSucc 68200131044052713951), (Int.negSucc 245041958321684035199), (Int.ofNat 768674710040028480), (Int.negSucc 145162769044339302911), (Int.negSucc 144240222746193336575), (Int.negSucc 52982965359048582143), (Int.negSucc 9756879303248833535), (Int.negSucc 67001551052709887)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 39797336015730432), (Int.ofNat 626328652717235520), (Int.ofNat 2085520361351845536), (Int.ofNat 713890357577695872), (Int.ofNat 32105897001903468672), (Int.ofNat 13169797298573247360), (Int.negSucc 5076376695876519935), (Int.ofNat 18480767956191618048), (Int.ofNat 7516004080461299712), (Int.ofNat 651150090703945728)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 19761822144990719), (Int.negSucc 208458031070482559), (Int.ofNat 79502267628715968), (Int.negSucc 1268971845299161343), (Int.negSucc 3917164288745895551), (Int.ofNat 2549080688557284864), (Int.negSucc 853637767480710143), (Int.negSucc 584148539651235839)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3182771590069248), (Int.ofNat 27218391573807360), (Int.negSucc 79973227589933951), (Int.ofNat 339723332006215680), (Int.negSucc 188697356821255679)]]

theorem h2n46_arithmetic_row0 :
    (BiPoly.mul h2p42 h2p45).getD 0 []=h2p46.getD 0 [] := by
  decide +kernel

theorem h2n46_arithmetic_row1 :
    (BiPoly.mul h2p42 h2p45).getD 1 []=h2p46.getD 1 [] := by
  decide +kernel

theorem h2n46_arithmetic_row2 :
    (BiPoly.mul h2p42 h2p45).getD 2 []=h2p46.getD 2 [] := by
  decide +kernel

theorem h2n46_arithmetic_row3 :
    (BiPoly.mul h2p42 h2p45).getD 3 []=h2p46.getD 3 [] := by
  decide +kernel

theorem h2n46_arithmetic_row4 :
    (BiPoly.mul h2p42 h2p45).getD 4 []=h2p46.getD 4 [] := by
  decide +kernel

theorem h2n46_arithmetic_row5 :
    (BiPoly.mul h2p42 h2p45).getD 5 []=h2p46.getD 5 [] := by
  decide +kernel

theorem h2n46_arithmetic_row6 :
    (BiPoly.mul h2p42 h2p45).getD 6 []=h2p46.getD 6 [] := by
  decide +kernel

theorem h2n46_arithmetic_row7 :
    (BiPoly.mul h2p42 h2p45).getD 7 []=h2p46.getD 7 [] := by
  decide +kernel

theorem h2n46_arithmetic_row8 :
    (BiPoly.mul h2p42 h2p45).getD 8 []=h2p46.getD 8 [] := by
  decide +kernel

theorem h2n46_arithmetic_row9 :
    (BiPoly.mul h2p42 h2p45).getD 9 []=h2p46.getD 9 [] := by
  decide +kernel

theorem h2n46_arithmetic_row10 :
    (BiPoly.mul h2p42 h2p45).getD 10 []=h2p46.getD 10 [] := by
  decide +kernel

theorem h2n46_arithmetic_row11 :
    (BiPoly.mul h2p42 h2p45).getD 11 []=h2p46.getD 11 [] := by
  decide +kernel

theorem h2n46_arithmetic_row12 :
    (BiPoly.mul h2p42 h2p45).getD 12 []=h2p46.getD 12 [] := by
  decide +kernel

theorem h2n46_arithmetic_row13 :
    (BiPoly.mul h2p42 h2p45).getD 13 []=h2p46.getD 13 [] := by
  decide +kernel

theorem h2n46_arithmetic_row14 :
    (BiPoly.mul h2p42 h2p45).getD 14 []=h2p46.getD 14 [] := by
  decide +kernel

theorem h2n46_arithmetic_row15 :
    (BiPoly.mul h2p42 h2p45).getD 15 []=h2p46.getD 15 [] := by
  decide +kernel

theorem h2n46_arithmetic_row16 :
    (BiPoly.mul h2p42 h2p45).getD 16 []=h2p46.getD 16 [] := by
  decide +kernel

theorem h2n46_arithmetic_row17 :
    (BiPoly.mul h2p42 h2p45).getD 17 []=h2p46.getD 17 [] := by
  decide +kernel

theorem h2n46_arithmetic_row18 :
    (BiPoly.mul h2p42 h2p45).getD 18 []=h2p46.getD 18 [] := by
  decide +kernel

theorem h2n46_arithmetic_row19 :
    (BiPoly.mul h2p42 h2p45).getD 19 []=h2p46.getD 19 [] := by
  decide +kernel

theorem h2n46_arithmetic_row20 :
    (BiPoly.mul h2p42 h2p45).getD 20 []=h2p46.getD 20 [] := by
  decide +kernel

theorem h2n46_arithmetic_row21 :
    (BiPoly.mul h2p42 h2p45).getD 21 []=h2p46.getD 21 [] := by
  decide +kernel

theorem h2n46_arithmetic_row22 :
    (BiPoly.mul h2p42 h2p45).getD 22 []=h2p46.getD 22 [] := by
  decide +kernel

theorem h2n46_arithmetic : BiPoly.mul h2p42 h2p45=h2p46 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<23 at hk
    have hf : ∀ j : Fin 23, (BiPoly.mul h2p42 h2p45).getD j.val []=h2p46.getD j.val [] :=
      (fun j => Fin.cases h2n46_arithmetic_row0 (fun j => Fin.cases h2n46_arithmetic_row1 (fun j => Fin.cases h2n46_arithmetic_row2 (fun j => Fin.cases h2n46_arithmetic_row3 (fun j => Fin.cases h2n46_arithmetic_row4 (fun j => Fin.cases h2n46_arithmetic_row5 (fun j => Fin.cases h2n46_arithmetic_row6 (fun j => Fin.cases h2n46_arithmetic_row7 (fun j => Fin.cases h2n46_arithmetic_row8 (fun j => Fin.cases h2n46_arithmetic_row9 (fun j => Fin.cases h2n46_arithmetic_row10 (fun j => Fin.cases h2n46_arithmetic_row11 (fun j => Fin.cases h2n46_arithmetic_row12 (fun j => Fin.cases h2n46_arithmetic_row13 (fun j => Fin.cases h2n46_arithmetic_row14 (fun j => Fin.cases h2n46_arithmetic_row15 (fun j => Fin.cases h2n46_arithmetic_row16 (fun j => Fin.cases h2n46_arithmetic_row17 (fun j => Fin.cases h2n46_arithmetic_row18 (fun j => Fin.cases h2n46_arithmetic_row19 (fun j => Fin.cases h2n46_arithmetic_row20 (fun j => Fin.cases h2n46_arithmetic_row21 (fun j => Fin.cases h2n46_arithmetic_row22 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h2n46 : h2e46.toBi mapPolyEnv=h2p46 := by
  change BiPoly.mul (h2e42.toBi mapPolyEnv) (h2e45.toBi mapPolyEnv)=h2p46
  rw [h2n42, h2n45]
  exact h2n46_arithmetic

#print axioms h2n46_arithmetic
end StackSorting.RationalLift
