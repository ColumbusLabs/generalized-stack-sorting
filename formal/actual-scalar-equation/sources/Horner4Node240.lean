import BivariateRowEquality
import Horner4Base
import Horner4Node133
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p240 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 292521060510524927999), (Int.negSucc 2083970440169831335679), (Int.negSucc 343769991664997473919), (Int.ofNat 18194600459033569566720), (Int.ofNat 3832006190967859196160), (Int.negSucc 55027465145170976298239), (Int.ofNat 34983509935107868041600)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3648959923707128718720), (Int.ofNat 24826531468383901992384), (Int.negSucc 919982649761815605695), (Int.negSucc 217575932695950261508991), (Int.negSucc 16362806642321935954175), (Int.ofNat 623043928141023090363840), (Int.negSucc 445666677277737972558527), (Int.ofNat 36663267660325591449600)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 21616336672929826600319), (Int.negSucc 137856934543279650845183), (Int.ofNat 40617241741471796089056), (Int.ofNat 1201523820276707163499104), (Int.negSucc 66428610700435315305407), (Int.negSucc 3125973058821310018568255), (Int.ofNat 2321825502483919788681312), (Int.negSucc 268597368442377914971679), (Int.ofNat 14595537675098310253056)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 80819645052469308697440), (Int.ofNat 471808476170481177299952), (Int.negSucc 287198048440487760239807), (Int.negSucc 4031510099181888096106703), (Int.ofNat 661791496877112004195104), (Int.ofNat 9035685359433469797035472), (Int.negSucc 6203630212639815338366975), (Int.ofNat 441837812428920937909008), (Int.negSucc 30544220812683873502655), (Int.ofNat 2687316451189335687168)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 213549287593657538116799), (Int.negSucc 1108988239585715287521119), (Int.ofNat 1088008517346561310945248), (Int.ofNat 9139432972873744707405120), (Int.negSucc 2013512144580318994101791), (Int.negSucc 16346814538379595743852063), (Int.ofNat 7620442460794388311181280), (Int.ofNat 1812305819957433810011712), (Int.negSucc 275697953149133703355487), (Int.ofNat 10708319768813284421376), (Int.ofNat 215836320920346372096)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 422740354341791288221920), (Int.ofNat 1888348657059945788640912), (Int.negSucc 2677980257191448020346687), (Int.negSucc 14812896334454524434902975), (Int.ofNat 2500607995301909066694912), (Int.ofNat 18678818832255596158973136), (Int.ofNat 2648004081775633559901888), (Int.negSucc 9534540827571159196011743), (Int.ofNat 1137610208086073733542112), (Int.negSucc 73411707985335806884991), (Int.ofNat 2720117610735679581696), (Int.ofNat 4897186845160439808)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 648107649187766380894319), (Int.negSucc 2393930599065855199678535), (Int.ofNat 4638583219839473808791784), (Int.ofNat 17907008432039561882991672), (Int.ofNat 1496225753111811441257352), (Int.negSucc 12514011020250640842480407), (Int.negSucc 24387917510581901547748199), (Int.ofNat 17369780527331636571782280), (Int.negSucc 401408669492071213466807), (Int.negSucc 54257438817545756439167), (Int.ofNat 525849588195390584064), (Int.ofNat 163475429080437130752), (Int.negSucc 30113150755184639)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 784359760112739290886720), (Int.ofNat 2285178747148101404191536), (Int.negSucc 5901441670562916531690743), (Int.negSucc 17044857198102718689595631), (Int.negSucc 11197148344306421243235623), (Int.ofNat 3001794785676037245601296), (Int.ofNat 38282895081066543989330616), (Int.negSucc 9815706808733174469519743), (Int.negSucc 5615004343958591918116919), (Int.ofNat 717259219250158919224176), (Int.negSucc 37974585138696345321215), (Int.ofNat 913713594960081158400), (Int.ofNat 396737922788692992)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 757008155582615989345679), (Int.negSucc 1639938275984200660810727), (Int.ofNat 5668774262452261729419912), (Int.ofNat 14033685141797953364383896), (Int.ofNat 21542755459606360118521296), (Int.ofNat 3492437477973226361622672), (Int.negSucc 27405389108508283264205783), (Int.negSucc 16006455612466025990140007), (Int.ofNat 13082747139691318903783920), (Int.negSucc 776528514073620801341687), (Int.ofNat 11960547257199144625440), (Int.negSucc 393314687663203963391), (Int.ofNat 24333763639916001792)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 584893802795826627424800), (Int.ofNat 871857830843163358042272), (Int.negSucc 4213507356268875145935047), (Int.negSucc 11280326214091760342340911), (Int.negSucc 25419139287868390206240479), (Int.negSucc 8023919938926282795758687), (Int.ofNat 2945856763295888526829560), (Int.ofNat 35148748785797433965914128), (Int.negSucc 9427005337681464182442767), (Int.negSucc 1815851668668068898548303), (Int.ofNat 219929808824594140118112), (Int.negSucc 8724447618419443776959), (Int.ofNat 139620574411779890688)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 361335570157782577131359), (Int.negSucc 333643890138948843896255), (Int.ofNat 2510711882346175052361864), (Int.ofNat 9201684755091156457981056), (Int.ofNat 21387741017293049494699872), (Int.ofNat 13534384814007294153318192), (Int.ofNat 11448141736425119534507448), (Int.negSucc 25893751824601463714970263), (Int.negSucc 6873521358321157023227351), (Int.ofNat 5020202647599391949536776), (Int.negSucc 261774849493491678616199), (Int.ofNat 1703771801510628209088), (Int.ofNat 68757366637461974784)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 177422600741127937804320), (Int.ofNat 89819926865320763790000), (Int.negSucc 1277646089368949593439567), (Int.negSucc 6994502807507257699258919), (Int.negSucc 14073083342796178155030647), (Int.negSucc 17289188098206892051002119), (Int.negSucc 11233060347488344930769951), (Int.ofNat 1832630107979797738152840), (Int.ofNat 17844105662629033369491216), (Int.negSucc 3377133912360685125395831), (Int.negSucc 410850706986339443639543), (Int.ofNat 37273907779477921838112), (Int.negSucc 877325352567027292607)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 68474243754094500940319), (Int.negSucc 20476637754142397798159), (Int.ofNat 605845958697703287584736), (Int.ofNat 4507292303187699121335312), (Int.ofNat 8063350011220772605203552), (Int.ofNat 15496615465910206042342776), (Int.ofNat 7851904272747339560877432), (Int.ofNat 10921708078190639380535472), (Int.negSucc 11804419323068794693146383), (Int.negSucc 2415982176202425050491367), (Int.ofNat 1031736491159287576932912), (Int.negSucc 25752827712361366297031), (Int.negSucc 721094355286069703903)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 20406472078038652644960), (Int.ofNat 8363713776827429099760), (Int.negSucc 280020852192365801669855), (Int.negSucc 2358350758987737339451007), (Int.negSucc 4463426346064619268454079), (Int.negSucc 9777605394174000641223527), (Int.negSucc 6970803793344553437137135), (Int.negSucc 8740997404404242238131615), (Int.negSucc 320531428260634513210703), (Int.ofNat 5124722437020223909896648), (Int.negSucc 460221130852922861154791), (Int.negSucc 67376201297407830598847), (Int.ofNat 2726978899888829719872)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 4570186436535369989999), (Int.negSucc 4889841140745347355815), (Int.ofNat 119414989348422074384808), (Int.ofNat 994897356422373012353160), (Int.ofNat 2408714449218176019764808), (Int.ofNat 4514242816912203022141200), (Int.ofNat 5989352089726053542207856), (Int.ofNat 3692805045643915821373584), (Int.ofNat 5078404266770886190503312), (Int.negSucc 2523110826731951406092375), (Int.negSucc 597472465725473453610767), (Int.ofNat 93879507289141340209728), (Int.ofNat 1089084472767953717760)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 737258277037981170240), (Int.ofNat 2098216872508516854384), (Int.negSucc 42557052134189871445223), (Int.negSucc 340919896466810233993055), (Int.negSucc 1160299526159291552934935), (Int.negSucc 1685858274545714147000903), (Int.negSucc 3605065306393882724704151), (Int.negSucc 1737937648634977873250999), (Int.negSucc 3202091142019061293569527), (Int.negSucc 599050194764913643211855), (Int.ofNat 747576723784412120990832), (Int.ofNat 2841991473780537344208), (Int.negSucc 4781557556644572110015)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 79855827406122245519), (Int.negSucc 588392580426301194407), (Int.ofNat 11706707524983169560312), (Int.ofNat 95547497831787511567752), (Int.ofNat 456038745601353946015392), (Int.ofNat 617017149812888396345496), (Int.ofNat 1413149168720139952514544), (Int.ofNat 1232244772444807365022200), (Int.ofNat 943167624406528935246768), (Int.ofNat 1205507639210687643867552), (Int.negSucc 183821920708611647425247), (Int.negSucc 70336733520799216519199), (Int.ofNat 1003382645481413392896)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5091689287835769120), (Int.ofNat 105225501769134309408), (Int.negSucc 2340573618213134065175), (Int.negSucc 21753079597324602331535), (Int.negSucc 138306624906316503173903), (Int.negSucc 242912702946647837055383), (Int.negSucc 364209812333006146944695), (Int.negSucc 672945493597398344140991), (Int.negSucc 224995287675432480140303), (Int.negSucc 543122393192311540772303), (Int.negSucc 159759289278904031749151), (Int.ofNat 38525699473888388103072), (Int.ofNat 3183043751133546019968)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 138738727221145919), (Int.negSucc 11072242226507993423), (Int.ofNat 318148984292932867464), (Int.ofNat 3897563380066227263904), (Int.ofNat 31142366821731877139376), (Int.ofNat 86766416015621575861080), (Int.ofNat 73696885484526812830896), (Int.ofNat 216833139062260004081664), (Int.ofNat 118916071893835781424768), (Int.ofNat 104264765299870854960096), (Int.ofNat 130845120197888351218464), (Int.ofNat 6006752286634626294528), (Int.negSucc 2022414740395230173183)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 527769208554208704), (Int.negSucc 26274266651290836815), (Int.negSucc 514517849115964016759), (Int.negSucc 4995372772347532565255), (Int.negSucc 23265349523368082871119), (Int.negSucc 19583818168481333668655), (Int.negSucc 37141404597655215919055), (Int.negSucc 57024212257889893753343), (Int.negSucc 8875937661164835700031), (Int.negSucc 37628422528527884379455), (Int.negSucc 12884563099487980880063), (Int.negSucc 262162300041815212799)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 998404178800743360), (Int.ofNat 44246202051599444304), (Int.ofNat 536507687168450445744), (Int.ofNat 4209796050550216829856), (Int.ofNat 6361440155885831717088), (Int.ofNat 2573622277900668381600), (Int.ofNat 14170110009057434847168), (Int.ofNat 3300145068604896966528), (Int.ofNat 3858759597417918097536), (Int.ofNat 4865758869189300774912), (Int.ofNat 611571783986613775872)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1850627046954285503), (Int.negSucc 34384884091543201967), (Int.negSucc 467015550387795052271), (Int.negSucc 1466135188267451088671), (Int.negSucc 142556812449949053791), (Int.negSucc 1436050011945012344063), (Int.negSucc 1588911988366900816127), (Int.ofNat 211413832373404970496), (Int.negSucc 745416812127598842239), (Int.negSucc 204955572313050094079)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 982750319367064704), (Int.ofNat 26422691505105174048), (Int.ofNat 190814213815307904672), (Int.ofNat 108864554479389536256), (Int.negSucc 56015299638228598271), (Int.ofNat 299825733136150316160), (Int.negSucc 64968817304050478207), (Int.ofNat 36779496349056215040), (Int.ofNat 22480514778789273600)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 410236992795214079), (Int.negSucc 11227097768208710975), (Int.negSucc 24622010750460791231), (Int.ofNat 22818587302543062528), (Int.negSucc 21454392591951433343), (Int.ofNat 3889797855695516160)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 103985988956453376), (Int.ofNat 1672828441409020032), (Int.negSucc 1089281260877086079)]]

theorem h4n240_arithmetic_row0 :
    (BiPoly.mul h4p103 h4p133).getD 0 []=h4p240.getD 0 [] := by
  decide +kernel

theorem h4n240_arithmetic_row1 :
    (BiPoly.mul h4p103 h4p133).getD 1 []=h4p240.getD 1 [] := by
  decide +kernel

theorem h4n240_arithmetic_row2 :
    (BiPoly.mul h4p103 h4p133).getD 2 []=h4p240.getD 2 [] := by
  decide +kernel

theorem h4n240_arithmetic_row3 :
    (BiPoly.mul h4p103 h4p133).getD 3 []=h4p240.getD 3 [] := by
  decide +kernel

theorem h4n240_arithmetic_row4 :
    (BiPoly.mul h4p103 h4p133).getD 4 []=h4p240.getD 4 [] := by
  decide +kernel

theorem h4n240_arithmetic_row5 :
    (BiPoly.mul h4p103 h4p133).getD 5 []=h4p240.getD 5 [] := by
  decide +kernel

theorem h4n240_arithmetic_row6 :
    (BiPoly.mul h4p103 h4p133).getD 6 []=h4p240.getD 6 [] := by
  decide +kernel

theorem h4n240_arithmetic_row7 :
    (BiPoly.mul h4p103 h4p133).getD 7 []=h4p240.getD 7 [] := by
  decide +kernel

theorem h4n240_arithmetic_row8 :
    (BiPoly.mul h4p103 h4p133).getD 8 []=h4p240.getD 8 [] := by
  decide +kernel

theorem h4n240_arithmetic_row9 :
    (BiPoly.mul h4p103 h4p133).getD 9 []=h4p240.getD 9 [] := by
  decide +kernel

theorem h4n240_arithmetic_row10 :
    (BiPoly.mul h4p103 h4p133).getD 10 []=h4p240.getD 10 [] := by
  decide +kernel

theorem h4n240_arithmetic_row11 :
    (BiPoly.mul h4p103 h4p133).getD 11 []=h4p240.getD 11 [] := by
  decide +kernel

theorem h4n240_arithmetic_row12 :
    (BiPoly.mul h4p103 h4p133).getD 12 []=h4p240.getD 12 [] := by
  decide +kernel

theorem h4n240_arithmetic_row13 :
    (BiPoly.mul h4p103 h4p133).getD 13 []=h4p240.getD 13 [] := by
  decide +kernel

theorem h4n240_arithmetic_row14 :
    (BiPoly.mul h4p103 h4p133).getD 14 []=h4p240.getD 14 [] := by
  decide +kernel

theorem h4n240_arithmetic_row15 :
    (BiPoly.mul h4p103 h4p133).getD 15 []=h4p240.getD 15 [] := by
  decide +kernel

theorem h4n240_arithmetic_row16 :
    (BiPoly.mul h4p103 h4p133).getD 16 []=h4p240.getD 16 [] := by
  decide +kernel

theorem h4n240_arithmetic_row17 :
    (BiPoly.mul h4p103 h4p133).getD 17 []=h4p240.getD 17 [] := by
  decide +kernel

theorem h4n240_arithmetic_row18 :
    (BiPoly.mul h4p103 h4p133).getD 18 []=h4p240.getD 18 [] := by
  decide +kernel

theorem h4n240_arithmetic_row19 :
    (BiPoly.mul h4p103 h4p133).getD 19 []=h4p240.getD 19 [] := by
  decide +kernel

theorem h4n240_arithmetic_row20 :
    (BiPoly.mul h4p103 h4p133).getD 20 []=h4p240.getD 20 [] := by
  decide +kernel

theorem h4n240_arithmetic_row21 :
    (BiPoly.mul h4p103 h4p133).getD 21 []=h4p240.getD 21 [] := by
  decide +kernel

theorem h4n240_arithmetic_row22 :
    (BiPoly.mul h4p103 h4p133).getD 22 []=h4p240.getD 22 [] := by
  decide +kernel

theorem h4n240_arithmetic_row23 :
    (BiPoly.mul h4p103 h4p133).getD 23 []=h4p240.getD 23 [] := by
  decide +kernel

theorem h4n240_arithmetic_row24 :
    (BiPoly.mul h4p103 h4p133).getD 24 []=h4p240.getD 24 [] := by
  decide +kernel

theorem h4n240_arithmetic : BiPoly.mul h4p103 h4p133=h4p240 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<25 at hk
    have hf : ∀ j : Fin 25, (BiPoly.mul h4p103 h4p133).getD j.val []=h4p240.getD j.val [] :=
      (fun j => Fin.cases h4n240_arithmetic_row0 (fun j => Fin.cases h4n240_arithmetic_row1 (fun j => Fin.cases h4n240_arithmetic_row2 (fun j => Fin.cases h4n240_arithmetic_row3 (fun j => Fin.cases h4n240_arithmetic_row4 (fun j => Fin.cases h4n240_arithmetic_row5 (fun j => Fin.cases h4n240_arithmetic_row6 (fun j => Fin.cases h4n240_arithmetic_row7 (fun j => Fin.cases h4n240_arithmetic_row8 (fun j => Fin.cases h4n240_arithmetic_row9 (fun j => Fin.cases h4n240_arithmetic_row10 (fun j => Fin.cases h4n240_arithmetic_row11 (fun j => Fin.cases h4n240_arithmetic_row12 (fun j => Fin.cases h4n240_arithmetic_row13 (fun j => Fin.cases h4n240_arithmetic_row14 (fun j => Fin.cases h4n240_arithmetic_row15 (fun j => Fin.cases h4n240_arithmetic_row16 (fun j => Fin.cases h4n240_arithmetic_row17 (fun j => Fin.cases h4n240_arithmetic_row18 (fun j => Fin.cases h4n240_arithmetic_row19 (fun j => Fin.cases h4n240_arithmetic_row20 (fun j => Fin.cases h4n240_arithmetic_row21 (fun j => Fin.cases h4n240_arithmetic_row22 (fun j => Fin.cases h4n240_arithmetic_row23 (fun j => Fin.cases h4n240_arithmetic_row24 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n240 : h4e240.toBi mapPolyEnv=h4p240 := by
  change BiPoly.mul (h4e103.toBi mapPolyEnv) (h4e133.toBi mapPolyEnv)=h4p240
  rw [h4n103, h4n133]
  exact h4n240_arithmetic

#print axioms h4n240_arithmetic
end StackSorting.RationalLift
