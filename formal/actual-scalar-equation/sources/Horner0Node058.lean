import BivariateRowEquality
import Horner0Base
import Horner0Node057
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p58 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 292521060510524928000), (Int.ofNat 2083970440169831335680), (Int.ofNat 343769991664997473920), (Int.negSucc 18194600459033569566719), (Int.negSucc 3832006190967859196159), (Int.ofNat 55027465145170976298240), (Int.negSucc 34983509935107868041599)], [(Int.ofNat 0), (Int.negSucc 3648959923707128718719), (Int.negSucc 24826531468383901992383), (Int.ofNat 919982649761815605696), (Int.ofNat 217575932695950261508992), (Int.ofNat 16362806642321935954176), (Int.negSucc 623043928141023090363839), (Int.ofNat 445666677277737972558528), (Int.negSucc 36663267660325591449599)], [(Int.ofNat 0), (Int.ofNat 21616336672929826600320), (Int.ofNat 137856934543279650845184), (Int.negSucc 40617241741471796089055), (Int.negSucc 1201523820276707163499103), (Int.ofNat 66428610700435315305408), (Int.ofNat 3125973058821310018568256), (Int.negSucc 2321825502483919788681311), (Int.ofNat 268597368442377914971680), (Int.negSucc 14595537675098310253055)], [(Int.ofNat 0), (Int.negSucc 80819645052469308697439), (Int.negSucc 471808476170481177299951), (Int.ofNat 287198048440487760239808), (Int.ofNat 4031510099181888096106704), (Int.negSucc 661791496877112004195103), (Int.negSucc 9035685359433469797035471), (Int.ofNat 6203630212639815338366976), (Int.negSucc 441837812428920937909007), (Int.ofNat 30544220812683873502656), (Int.negSucc 2687316451189335687167)], [(Int.ofNat 0), (Int.ofNat 213549287593657538116800), (Int.ofNat 1108988239585715287521120), (Int.negSucc 1088008517346561310945247), (Int.negSucc 9139432972873744707405119), (Int.ofNat 2013512144580318994101792), (Int.ofNat 16346814538379595743852064), (Int.negSucc 7620442460794388311181279), (Int.negSucc 1812305819957433810011711), (Int.ofNat 275697953149133703355488), (Int.negSucc 10708319768813284421375), (Int.negSucc 215836320920346372095)], [(Int.ofNat 0), (Int.negSucc 422740354341791288221919), (Int.negSucc 1888348657059945788640911), (Int.ofNat 2677980257191448020346688), (Int.ofNat 14812896334454524434902976), (Int.negSucc 2500607995301909066694911), (Int.negSucc 18678818832255596158973135), (Int.negSucc 2648004081775633559901887), (Int.ofNat 9534540827571159196011744), (Int.negSucc 1137610208086073733542111), (Int.ofNat 73411707985335806884992), (Int.negSucc 2720117610735679581695), (Int.negSucc 4897186845160439807)], [(Int.ofNat 0), (Int.ofNat 648107649187766380894320), (Int.ofNat 2393930599065855199678536), (Int.negSucc 4638583219839473808791783), (Int.negSucc 17907008432039561882991671), (Int.negSucc 1496225753111811441257351), (Int.ofNat 12514011020250640842480408), (Int.ofNat 24387917510581901547748200), (Int.negSucc 17369780527331636571782279), (Int.ofNat 401408669492071213466808), (Int.ofNat 54257438817545756439168), (Int.negSucc 525849588195390584063), (Int.negSucc 163475429080437130751), (Int.ofNat 30113150755184640)], [(Int.ofNat 0), (Int.negSucc 784359760112739290886719), (Int.negSucc 2285178747148101404191535), (Int.ofNat 5901441670562916531690744), (Int.ofNat 17044857198102718689595632), (Int.ofNat 11197148344306421243235624), (Int.negSucc 3001794785676037245601295), (Int.negSucc 38282895081066543989330615), (Int.ofNat 9815706808733174469519744), (Int.ofNat 5615004343958591918116920), (Int.negSucc 717259219250158919224175), (Int.ofNat 37974585138696345321216), (Int.negSucc 913713594960081158399), (Int.negSucc 396737922788692991)], [(Int.ofNat 0), (Int.ofNat 757008155582615989345680), (Int.ofNat 1639938275984200660810728), (Int.negSucc 5668774262452261729419911), (Int.negSucc 14033685141797953364383895), (Int.negSucc 21542755459606360118521295), (Int.negSucc 3492437477973226361622671), (Int.ofNat 27405389108508283264205784), (Int.ofNat 16006455612466025990140008), (Int.negSucc 13082747139691318903783919), (Int.ofNat 776528514073620801341688), (Int.negSucc 11960547257199144625439), (Int.ofNat 393314687663203963392), (Int.negSucc 24333763639916001791)], [(Int.ofNat 0), (Int.negSucc 584893802795826627424799), (Int.negSucc 871857830843163358042271), (Int.ofNat 4213507356268875145935048), (Int.ofNat 11280326214091760342340912), (Int.ofNat 25419139287868390206240480), (Int.ofNat 8023919938926282795758688), (Int.negSucc 2945856763295888526829559), (Int.negSucc 35148748785797433965914127), (Int.ofNat 9427005337681464182442768), (Int.ofNat 1815851668668068898548304), (Int.negSucc 219929808824594140118111), (Int.ofNat 8724447618419443776960), (Int.negSucc 139620574411779890687)], [(Int.ofNat 0), (Int.ofNat 361335570157782577131360), (Int.ofNat 333643890138948843896256), (Int.negSucc 2510711882346175052361863), (Int.negSucc 9201684755091156457981055), (Int.negSucc 21387741017293049494699871), (Int.negSucc 13534384814007294153318191), (Int.negSucc 11448141736425119534507447), (Int.ofNat 25893751824601463714970264), (Int.ofNat 6873521358321157023227352), (Int.negSucc 5020202647599391949536775), (Int.ofNat 261774849493491678616200), (Int.negSucc 1703771801510628209087), (Int.negSucc 68757366637461974783)], [(Int.ofNat 0), (Int.negSucc 177422600741127937804319), (Int.negSucc 89819926865320763789999), (Int.ofNat 1277646089368949593439568), (Int.ofNat 6994502807507257699258920), (Int.ofNat 14073083342796178155030648), (Int.ofNat 17289188098206892051002120), (Int.ofNat 11233060347488344930769952), (Int.negSucc 1832630107979797738152839), (Int.negSucc 17844105662629033369491215), (Int.ofNat 3377133912360685125395832), (Int.ofNat 410850706986339443639544), (Int.negSucc 37273907779477921838111), (Int.ofNat 877325352567027292608)], [(Int.ofNat 0), (Int.ofNat 68474243754094500940320), (Int.ofNat 20476637754142397798160), (Int.negSucc 605845958697703287584735), (Int.negSucc 4507292303187699121335311), (Int.negSucc 8063350011220772605203551), (Int.negSucc 15496615465910206042342775), (Int.negSucc 7851904272747339560877431), (Int.negSucc 10921708078190639380535471), (Int.ofNat 11804419323068794693146384), (Int.ofNat 2415982176202425050491368), (Int.negSucc 1031736491159287576932911), (Int.ofNat 25752827712361366297032), (Int.ofNat 721094355286069703904)], [(Int.ofNat 0), (Int.negSucc 20406472078038652644959), (Int.negSucc 8363713776827429099759), (Int.ofNat 280020852192365801669856), (Int.ofNat 2358350758987737339451008), (Int.ofNat 4463426346064619268454080), (Int.ofNat 9777605394174000641223528), (Int.ofNat 6970803793344553437137136), (Int.ofNat 8740997404404242238131616), (Int.ofNat 320531428260634513210704), (Int.negSucc 5124722437020223909896647), (Int.ofNat 460221130852922861154792), (Int.ofNat 67376201297407830598848), (Int.negSucc 2726978899888829719871)], [(Int.ofNat 0), (Int.ofNat 4570186436535369990000), (Int.ofNat 4889841140745347355816), (Int.negSucc 119414989348422074384807), (Int.negSucc 994897356422373012353159), (Int.negSucc 2408714449218176019764807), (Int.negSucc 4514242816912203022141199), (Int.negSucc 5989352089726053542207855), (Int.negSucc 3692805045643915821373583), (Int.negSucc 5078404266770886190503311), (Int.ofNat 2523110826731951406092376), (Int.ofNat 597472465725473453610768), (Int.negSucc 93879507289141340209727), (Int.negSucc 1089084472767953717759)], [(Int.ofNat 0), (Int.negSucc 737258277037981170239), (Int.negSucc 2098216872508516854383), (Int.ofNat 42557052134189871445224), (Int.ofNat 340919896466810233993056), (Int.ofNat 1160299526159291552934936), (Int.ofNat 1685858274545714147000904), (Int.ofNat 3605065306393882724704152), (Int.ofNat 1737937648634977873251000), (Int.ofNat 3202091142019061293569528), (Int.ofNat 599050194764913643211856), (Int.negSucc 747576723784412120990831), (Int.negSucc 2841991473780537344207), (Int.ofNat 4781557556644572110016)], [(Int.ofNat 0), (Int.ofNat 79855827406122245520), (Int.ofNat 588392580426301194408), (Int.negSucc 11706707524983169560311), (Int.negSucc 95547497831787511567751), (Int.negSucc 456038745601353946015391), (Int.negSucc 617017149812888396345495), (Int.negSucc 1413149168720139952514543), (Int.negSucc 1232244772444807365022199), (Int.negSucc 943167624406528935246767), (Int.negSucc 1205507639210687643867551), (Int.ofNat 183821920708611647425248), (Int.ofNat 70336733520799216519200), (Int.negSucc 1003382645481413392895)], [(Int.ofNat 0), (Int.negSucc 5091689287835769119), (Int.negSucc 105225501769134309407), (Int.ofNat 2340573618213134065176), (Int.ofNat 21753079597324602331536), (Int.ofNat 138306624906316503173904), (Int.ofNat 242912702946647837055384), (Int.ofNat 364209812333006146944696), (Int.ofNat 672945493597398344140992), (Int.ofNat 224995287675432480140304), (Int.ofNat 543122393192311540772304), (Int.ofNat 159759289278904031749152), (Int.negSucc 38525699473888388103071), (Int.negSucc 3183043751133546019967)], [(Int.ofNat 0), (Int.ofNat 138738727221145920), (Int.ofNat 11072242226507993424), (Int.negSucc 318148984292932867463), (Int.negSucc 3897563380066227263903), (Int.negSucc 31142366821731877139375), (Int.negSucc 86766416015621575861079), (Int.negSucc 73696885484526812830895), (Int.negSucc 216833139062260004081663), (Int.negSucc 118916071893835781424767), (Int.negSucc 104264765299870854960095), (Int.negSucc 130845120197888351218463), (Int.negSucc 6006752286634626294527), (Int.ofNat 2022414740395230173184)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 527769208554208703), (Int.ofNat 26274266651290836816), (Int.ofNat 514517849115964016760), (Int.ofNat 4995372772347532565256), (Int.ofNat 23265349523368082871120), (Int.ofNat 19583818168481333668656), (Int.ofNat 37141404597655215919056), (Int.ofNat 57024212257889893753344), (Int.ofNat 8875937661164835700032), (Int.ofNat 37628422528527884379456), (Int.ofNat 12884563099487980880064), (Int.ofNat 262162300041815212800)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 998404178800743359), (Int.negSucc 44246202051599444303), (Int.negSucc 536507687168450445743), (Int.negSucc 4209796050550216829855), (Int.negSucc 6361440155885831717087), (Int.negSucc 2573622277900668381599), (Int.negSucc 14170110009057434847167), (Int.negSucc 3300145068604896966527), (Int.negSucc 3858759597417918097535), (Int.negSucc 4865758869189300774911), (Int.negSucc 611571783986613775871)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1850627046954285504), (Int.ofNat 34384884091543201968), (Int.ofNat 467015550387795052272), (Int.ofNat 1466135188267451088672), (Int.ofNat 142556812449949053792), (Int.ofNat 1436050011945012344064), (Int.ofNat 1588911988366900816128), (Int.negSucc 211413832373404970495), (Int.ofNat 745416812127598842240), (Int.ofNat 204955572313050094080)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 982750319367064703), (Int.negSucc 26422691505105174047), (Int.negSucc 190814213815307904671), (Int.negSucc 108864554479389536255), (Int.ofNat 56015299638228598272), (Int.negSucc 299825733136150316159), (Int.ofNat 64968817304050478208), (Int.negSucc 36779496349056215039), (Int.negSucc 22480514778789273599)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 410236992795214080), (Int.ofNat 11227097768208710976), (Int.ofNat 24622010750460791232), (Int.negSucc 22818587302543062527), (Int.ofNat 21454392591951433344), (Int.negSucc 3889797855695516159)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 103985988956453375), (Int.negSucc 1672828441409020031), (Int.ofNat 1089281260877086080)]]

theorem h0n58_arithmetic_row0 :
    (BiPoly.mul h0p46 h0p57).getD 0 []=h0p58.getD 0 [] := by
  decide +kernel

theorem h0n58_arithmetic_row1 :
    (BiPoly.mul h0p46 h0p57).getD 1 []=h0p58.getD 1 [] := by
  decide +kernel

theorem h0n58_arithmetic_row2 :
    (BiPoly.mul h0p46 h0p57).getD 2 []=h0p58.getD 2 [] := by
  decide +kernel

theorem h0n58_arithmetic_row3 :
    (BiPoly.mul h0p46 h0p57).getD 3 []=h0p58.getD 3 [] := by
  decide +kernel

theorem h0n58_arithmetic_row4 :
    (BiPoly.mul h0p46 h0p57).getD 4 []=h0p58.getD 4 [] := by
  decide +kernel

theorem h0n58_arithmetic_row5 :
    (BiPoly.mul h0p46 h0p57).getD 5 []=h0p58.getD 5 [] := by
  decide +kernel

theorem h0n58_arithmetic_row6 :
    (BiPoly.mul h0p46 h0p57).getD 6 []=h0p58.getD 6 [] := by
  decide +kernel

theorem h0n58_arithmetic_row7 :
    (BiPoly.mul h0p46 h0p57).getD 7 []=h0p58.getD 7 [] := by
  decide +kernel

theorem h0n58_arithmetic_row8 :
    (BiPoly.mul h0p46 h0p57).getD 8 []=h0p58.getD 8 [] := by
  decide +kernel

theorem h0n58_arithmetic_row9 :
    (BiPoly.mul h0p46 h0p57).getD 9 []=h0p58.getD 9 [] := by
  decide +kernel

theorem h0n58_arithmetic_row10 :
    (BiPoly.mul h0p46 h0p57).getD 10 []=h0p58.getD 10 [] := by
  decide +kernel

theorem h0n58_arithmetic_row11 :
    (BiPoly.mul h0p46 h0p57).getD 11 []=h0p58.getD 11 [] := by
  decide +kernel

theorem h0n58_arithmetic_row12 :
    (BiPoly.mul h0p46 h0p57).getD 12 []=h0p58.getD 12 [] := by
  decide +kernel

theorem h0n58_arithmetic_row13 :
    (BiPoly.mul h0p46 h0p57).getD 13 []=h0p58.getD 13 [] := by
  decide +kernel

theorem h0n58_arithmetic_row14 :
    (BiPoly.mul h0p46 h0p57).getD 14 []=h0p58.getD 14 [] := by
  decide +kernel

theorem h0n58_arithmetic_row15 :
    (BiPoly.mul h0p46 h0p57).getD 15 []=h0p58.getD 15 [] := by
  decide +kernel

theorem h0n58_arithmetic_row16 :
    (BiPoly.mul h0p46 h0p57).getD 16 []=h0p58.getD 16 [] := by
  decide +kernel

theorem h0n58_arithmetic_row17 :
    (BiPoly.mul h0p46 h0p57).getD 17 []=h0p58.getD 17 [] := by
  decide +kernel

theorem h0n58_arithmetic_row18 :
    (BiPoly.mul h0p46 h0p57).getD 18 []=h0p58.getD 18 [] := by
  decide +kernel

theorem h0n58_arithmetic_row19 :
    (BiPoly.mul h0p46 h0p57).getD 19 []=h0p58.getD 19 [] := by
  decide +kernel

theorem h0n58_arithmetic_row20 :
    (BiPoly.mul h0p46 h0p57).getD 20 []=h0p58.getD 20 [] := by
  decide +kernel

theorem h0n58_arithmetic_row21 :
    (BiPoly.mul h0p46 h0p57).getD 21 []=h0p58.getD 21 [] := by
  decide +kernel

theorem h0n58_arithmetic_row22 :
    (BiPoly.mul h0p46 h0p57).getD 22 []=h0p58.getD 22 [] := by
  decide +kernel

theorem h0n58_arithmetic_row23 :
    (BiPoly.mul h0p46 h0p57).getD 23 []=h0p58.getD 23 [] := by
  decide +kernel

theorem h0n58_arithmetic_row24 :
    (BiPoly.mul h0p46 h0p57).getD 24 []=h0p58.getD 24 [] := by
  decide +kernel

theorem h0n58_arithmetic : BiPoly.mul h0p46 h0p57=h0p58 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<25 at hk
    have hf : ∀ j : Fin 25, (BiPoly.mul h0p46 h0p57).getD j.val []=h0p58.getD j.val [] :=
      (fun j => Fin.cases h0n58_arithmetic_row0 (fun j => Fin.cases h0n58_arithmetic_row1 (fun j => Fin.cases h0n58_arithmetic_row2 (fun j => Fin.cases h0n58_arithmetic_row3 (fun j => Fin.cases h0n58_arithmetic_row4 (fun j => Fin.cases h0n58_arithmetic_row5 (fun j => Fin.cases h0n58_arithmetic_row6 (fun j => Fin.cases h0n58_arithmetic_row7 (fun j => Fin.cases h0n58_arithmetic_row8 (fun j => Fin.cases h0n58_arithmetic_row9 (fun j => Fin.cases h0n58_arithmetic_row10 (fun j => Fin.cases h0n58_arithmetic_row11 (fun j => Fin.cases h0n58_arithmetic_row12 (fun j => Fin.cases h0n58_arithmetic_row13 (fun j => Fin.cases h0n58_arithmetic_row14 (fun j => Fin.cases h0n58_arithmetic_row15 (fun j => Fin.cases h0n58_arithmetic_row16 (fun j => Fin.cases h0n58_arithmetic_row17 (fun j => Fin.cases h0n58_arithmetic_row18 (fun j => Fin.cases h0n58_arithmetic_row19 (fun j => Fin.cases h0n58_arithmetic_row20 (fun j => Fin.cases h0n58_arithmetic_row21 (fun j => Fin.cases h0n58_arithmetic_row22 (fun j => Fin.cases h0n58_arithmetic_row23 (fun j => Fin.cases h0n58_arithmetic_row24 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n58 : h0e58.toBi mapPolyEnv=h0p58 := by
  change BiPoly.mul (h0e46.toBi mapPolyEnv) (h0e57.toBi mapPolyEnv)=h0p58
  rw [h0n46, h0n57]
  exact h0n58_arithmetic

#print axioms h0n58_arithmetic
end StackSorting.RationalLift
