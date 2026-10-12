import BivariateRowEquality
import Horner0Base
import Horner0Node057
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p92 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 877563181531574783999), (Int.negSucc 6251911320509494007039), (Int.negSucc 1031309974994992421759), (Int.ofNat 54583801377100708700160), (Int.ofNat 11496018572903577588480), (Int.negSucc 165082395435512928894719), (Int.ofNat 104950529805323604124800)], [(Int.ofNat 0), (Int.ofNat 10946879771121386156160), (Int.ofNat 74479594405151705977152), (Int.negSucc 2759947949285446817087), (Int.negSucc 652727798087850784526975), (Int.negSucc 49088419926965807862527), (Int.ofNat 1869131784423069271091520), (Int.negSucc 1337000031833213917675583), (Int.ofNat 109989802980976774348800)], [(Int.ofNat 0), (Int.negSucc 64849010018789479800959), (Int.negSucc 413570803629838952535551), (Int.ofNat 121851725224415388267168), (Int.ofNat 3604571460830121490497312), (Int.negSucc 199285832101305945916223), (Int.negSucc 9377919176463930055704767), (Int.ofNat 6965476507451759366043936), (Int.negSucc 805792105327133744915039), (Int.ofNat 43786613025294930759168)], [(Int.ofNat 0), (Int.ofNat 242458935157407926092320), (Int.ofNat 1415425428511443531899856), (Int.negSucc 861594145321463280719423), (Int.negSucc 12094530297545664288320111), (Int.ofNat 1985374490631336012585312), (Int.ofNat 27107056078300409391106416), (Int.negSucc 18610890637919446015100927), (Int.ofNat 1325513437286762813727024), (Int.negSucc 91632662438051620507967), (Int.ofNat 8061949353568007061504)], [(Int.ofNat 0), (Int.negSucc 640647862780972614350399), (Int.negSucc 3326964718757145862563359), (Int.ofNat 3264025552039683932835744), (Int.ofNat 27418298918621234122215360), (Int.negSucc 6040536433740956982305375), (Int.negSucc 49040443615138787231556191), (Int.ofNat 22861327382383164933543840), (Int.ofNat 5436917459872301430035136), (Int.negSucc 827093859447401110066463), (Int.ofNat 32124959306439853264128), (Int.ofNat 647508962761039116288)], [(Int.ofNat 0), (Int.ofNat 1268221063025373864665760), (Int.ofNat 5665045971179837365922736), (Int.negSucc 8033940771574344061040063), (Int.negSucc 44438689003363573304708927), (Int.ofNat 7501823985905727200084736), (Int.ofNat 56036456496766788476919408), (Int.ofNat 7944012245326900679705664), (Int.negSucc 28603622482713477588035231), (Int.ofNat 3412830624258221200626336), (Int.negSucc 220235123956007420654975), (Int.ofNat 8160352832207038745088), (Int.ofNat 14691560535481319424)], [(Int.ofNat 0), (Int.negSucc 1944322947563299142682959), (Int.negSucc 7181791797197565599035607), (Int.ofNat 13915749659518421426375352), (Int.ofNat 53721025296118685648975016), (Int.ofNat 4488677259335434323772056), (Int.negSucc 37542033060751922527441223), (Int.negSucc 73163752531745704643244599), (Int.ofNat 52109341581994909715346840), (Int.negSucc 1204226008476213640400423), (Int.negSucc 162772316452637269317503), (Int.ofNat 1577548764586171752192), (Int.ofNat 490426287241311392256), (Int.negSucc 90339452265553919)], [(Int.ofNat 0), (Int.ofNat 2353079280338217872660160), (Int.ofNat 6855536241444304212574608), (Int.negSucc 17704325011688749595072231), (Int.negSucc 51134571594308156068786895), (Int.negSucc 33591445032919263729706871), (Int.ofNat 9005384357028111736803888), (Int.ofNat 114848685243199631967991848), (Int.negSucc 29447120426199523408559231), (Int.negSucc 16845013031875775754350759), (Int.ofNat 2151777657750476757672528), (Int.negSucc 113923755416089035963647), (Int.ofNat 2741140784880243475200), (Int.ofNat 1190213768366078976)], [(Int.ofNat 0), (Int.negSucc 2271024466747847968037039), (Int.negSucc 4919814827952601982432183), (Int.ofNat 17006322787356785188259736), (Int.ofNat 42101055425393860093151688), (Int.ofNat 64628266378819080355563888), (Int.ofNat 10477312433919679084868016), (Int.negSucc 82216167325524849792617351), (Int.negSucc 48019366837398077970420023), (Int.ofNat 39248241419073956711351760), (Int.negSucc 2329585542220862404025063), (Int.ofNat 35881641771597433876320), (Int.negSucc 1179944062989611890175), (Int.ofNat 73001290919748005376)], [(Int.ofNat 0), (Int.ofNat 1754681408387479882274400), (Int.ofNat 2615573492529490074126816), (Int.negSucc 12640522068806625437805143), (Int.negSucc 33840978642275281027022735), (Int.negSucc 76257417863605170618721439), (Int.negSucc 24071759816778848387276063), (Int.ofNat 8837570289887665580488680), (Int.ofNat 105446246357392301897742384), (Int.negSucc 28281016013044392547328303), (Int.negSucc 5447555006004206695644911), (Int.ofNat 659789426473782420354336), (Int.negSucc 26173342855258331330879), (Int.ofNat 418861723235339672064)], [(Int.ofNat 0), (Int.negSucc 1084006710473347731394079), (Int.negSucc 1000931670416846531688767), (Int.ofNat 7532135647038525157085592), (Int.ofNat 27605054265273469373943168), (Int.ofNat 64163223051879148484099616), (Int.ofNat 40603154442021882459954576), (Int.ofNat 34344425209275358603522344), (Int.negSucc 77681255473804391144910791), (Int.negSucc 20620564074963471069682055), (Int.ofNat 15060607942798175848610328), (Int.negSucc 785324548480475035848599), (Int.ofNat 5111315404531884627264), (Int.ofNat 206272099912385924352)], [(Int.ofNat 0), (Int.ofNat 532267802223383813412960), (Int.ofNat 269459780595962291370000), (Int.negSucc 3832938268106848780318703), (Int.negSucc 20983508422521773097776759), (Int.negSucc 42219250028388534465091943), (Int.negSucc 51867564294620676153006359), (Int.negSucc 33699181042465034792309855), (Int.ofNat 5497890323939393214458520), (Int.ofNat 53532316987887100108473648), (Int.negSucc 10131401737082055376187495), (Int.negSucc 1232552120959018330918631), (Int.ofNat 111821723338433765514336), (Int.negSucc 2631976057701081877823)], [(Int.ofNat 0), (Int.negSucc 205422731262283502820959), (Int.negSucc 61429913262427193394479), (Int.ofNat 1817537876093109862754208), (Int.ofNat 13521876909563097364005936), (Int.ofNat 24190050033662317815610656), (Int.ofNat 46489846397730618127028328), (Int.ofNat 23555712818242018682632296), (Int.ofNat 32765124234571918141606416), (Int.negSucc 35413257969206384079439151), (Int.negSucc 7247946528607275151474103), (Int.ofNat 3095209473477862730798736), (Int.negSucc 77258483137084098891095), (Int.negSucc 2163283065858209111711)], [(Int.ofNat 0), (Int.ofNat 61219416234115957934880), (Int.ofNat 25091141330482287299280), (Int.negSucc 840062556577097405009567), (Int.negSucc 7075052276963212018353023), (Int.negSucc 13390279038193857805362239), (Int.negSucc 29332816182522001923670583), (Int.negSucc 20912411380033660311411407), (Int.negSucc 26222992213212726714394847), (Int.negSucc 961594284781903539632111), (Int.ofNat 15374167311060671729689944), (Int.negSucc 1380663392558768583464375), (Int.negSucc 202128603892223491796543), (Int.ofNat 8180936699666489159616)], [(Int.ofNat 0), (Int.negSucc 13710559309606109969999), (Int.negSucc 14669523422236042067447), (Int.ofNat 358244968045266223154424), (Int.ofNat 2984692069267119037059480), (Int.ofNat 7226143347654528059294424), (Int.ofNat 13542728450736609066423600), (Int.ofNat 17968056269178160626623568), (Int.ofNat 11078415136931747464120752), (Int.ofNat 15235212800312658571509936), (Int.negSucc 7569332480195854218277127), (Int.negSucc 1792417397176420360832303), (Int.ofNat 281638521867424020629184), (Int.ofNat 3267253418303861153280)], [(Int.ofNat 0), (Int.ofNat 2211774831113943510720), (Int.ofNat 6294650617525550563152), (Int.negSucc 127671156402569614335671), (Int.negSucc 1022759689400430701979167), (Int.negSucc 3480898578477874658804807), (Int.negSucc 5057574823637142441002711), (Int.negSucc 10815195919181648174112455), (Int.negSucc 5213812945904933619752999), (Int.negSucc 9606273426057183880708583), (Int.negSucc 1797150584294740929635567), (Int.ofNat 2242730171353236362972496), (Int.ofNat 8525974421341612032624), (Int.negSucc 14344672669933716330047)], [(Int.ofNat 0), (Int.negSucc 239567482218366736559), (Int.negSucc 1765177741278903583223), (Int.ofNat 35120122574949508680936), (Int.ofNat 286642493495362534703256), (Int.ofNat 1368116236804061838046176), (Int.ofNat 1851051449438665189036488), (Int.ofNat 4239447506160419857543632), (Int.ofNat 3696734317334422095066600), (Int.ofNat 2829502873219586805740304), (Int.ofNat 3616522917632062931602656), (Int.negSucc 551465762125834942275743), (Int.negSucc 211010200562397649557599), (Int.ofNat 3010147936444240178688)], [(Int.ofNat 0), (Int.ofNat 15275067863507307360), (Int.ofNat 315676505307402928224), (Int.negSucc 7021720854639402195527), (Int.negSucc 65259238791973806994607), (Int.negSucc 414919874718949509521711), (Int.negSucc 728738108839943511166151), (Int.negSucc 1092629436999018440834087), (Int.negSucc 2018836480792195032422975), (Int.negSucc 674985863026297440420911), (Int.negSucc 1629367179576934622316911), (Int.negSucc 479277867836712095247455), (Int.ofNat 115577098421665164309216), (Int.ofNat 9549131253400638059904)], [(Int.ofNat 0), (Int.negSucc 416216181663437759), (Int.negSucc 33216726679523980271), (Int.ofNat 954446952878798602392), (Int.ofNat 11692690140198681791712), (Int.ofNat 93427100465195631418128), (Int.ofNat 260299248046864727583240), (Int.ofNat 221090656453580438492688), (Int.ofNat 650499417186780012244992), (Int.ofNat 356748215681507344274304), (Int.ofNat 312794295899612564880288), (Int.ofNat 392535360593665053655392), (Int.ofNat 18020256859903878883584), (Int.negSucc 6067244221185690519551)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1583307625662626112), (Int.negSucc 78822799953872510447), (Int.negSucc 1543553547347892050279), (Int.negSucc 14986118317042597695767), (Int.negSucc 69796048570104248613359), (Int.negSucc 58751454505444001005967), (Int.negSucc 111424213792965647757167), (Int.negSucc 171072636773669681260031), (Int.negSucc 26627812983494507100095), (Int.negSucc 112885267585583653138367), (Int.negSucc 38653689298463942640191), (Int.negSucc 786486900125445638399)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2995212536402230080), (Int.ofNat 132738606154798332912), (Int.ofNat 1609523061505351337232), (Int.ofNat 12629388151650650489568), (Int.ofNat 19084320467657495151264), (Int.ofNat 7720866833702005144800), (Int.ofNat 42510330027172304541504), (Int.ofNat 9900435205814690899584), (Int.ofNat 11576278792253754292608), (Int.ofNat 14597276607567902324736), (Int.ofNat 1834715351959841327616)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 5551881140862856511), (Int.negSucc 103154652274629605903), (Int.negSucc 1401046651163385156815), (Int.negSucc 4398405564802353266015), (Int.negSucc 427670437349847161375), (Int.negSucc 4308150035835037032191), (Int.negSucc 4766735965100702448383), (Int.ofNat 634241497120214911488), (Int.negSucc 2236250436382796526719), (Int.negSucc 614866716939150282239)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2948250958101194112), (Int.ofNat 79268074515315522144), (Int.ofNat 572442641445923714016), (Int.ofNat 326593663438168608768), (Int.negSucc 168045898914685794815), (Int.ofNat 899477199408450948480), (Int.negSucc 194906451912151434623), (Int.ofNat 110338489047168645120), (Int.ofNat 67441544336367820800)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1230710978385642239), (Int.negSucc 33681293304626132927), (Int.negSucc 73866032251382373695), (Int.ofNat 68455761907629187584), (Int.negSucc 64363177775854300031), (Int.ofNat 11669393567086548480)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 311957966869360128), (Int.ofNat 5018485324227060096), (Int.negSucc 3267843782631258239)]]

theorem h0n92_arithmetic_row0 :
    (BiPoly.mul h0p91 h0p57).getD 0 []=h0p92.getD 0 [] := by
  decide +kernel

theorem h0n92_arithmetic_row1 :
    (BiPoly.mul h0p91 h0p57).getD 1 []=h0p92.getD 1 [] := by
  decide +kernel

theorem h0n92_arithmetic_row2 :
    (BiPoly.mul h0p91 h0p57).getD 2 []=h0p92.getD 2 [] := by
  decide +kernel

theorem h0n92_arithmetic_row3 :
    (BiPoly.mul h0p91 h0p57).getD 3 []=h0p92.getD 3 [] := by
  decide +kernel

theorem h0n92_arithmetic_row4 :
    (BiPoly.mul h0p91 h0p57).getD 4 []=h0p92.getD 4 [] := by
  decide +kernel

theorem h0n92_arithmetic_row5 :
    (BiPoly.mul h0p91 h0p57).getD 5 []=h0p92.getD 5 [] := by
  decide +kernel

theorem h0n92_arithmetic_row6 :
    (BiPoly.mul h0p91 h0p57).getD 6 []=h0p92.getD 6 [] := by
  decide +kernel

theorem h0n92_arithmetic_row7 :
    (BiPoly.mul h0p91 h0p57).getD 7 []=h0p92.getD 7 [] := by
  decide +kernel

theorem h0n92_arithmetic_row8 :
    (BiPoly.mul h0p91 h0p57).getD 8 []=h0p92.getD 8 [] := by
  decide +kernel

theorem h0n92_arithmetic_row9 :
    (BiPoly.mul h0p91 h0p57).getD 9 []=h0p92.getD 9 [] := by
  decide +kernel

theorem h0n92_arithmetic_row10 :
    (BiPoly.mul h0p91 h0p57).getD 10 []=h0p92.getD 10 [] := by
  decide +kernel

theorem h0n92_arithmetic_row11 :
    (BiPoly.mul h0p91 h0p57).getD 11 []=h0p92.getD 11 [] := by
  decide +kernel

theorem h0n92_arithmetic_row12 :
    (BiPoly.mul h0p91 h0p57).getD 12 []=h0p92.getD 12 [] := by
  decide +kernel

theorem h0n92_arithmetic_row13 :
    (BiPoly.mul h0p91 h0p57).getD 13 []=h0p92.getD 13 [] := by
  decide +kernel

theorem h0n92_arithmetic_row14 :
    (BiPoly.mul h0p91 h0p57).getD 14 []=h0p92.getD 14 [] := by
  decide +kernel

theorem h0n92_arithmetic_row15 :
    (BiPoly.mul h0p91 h0p57).getD 15 []=h0p92.getD 15 [] := by
  decide +kernel

theorem h0n92_arithmetic_row16 :
    (BiPoly.mul h0p91 h0p57).getD 16 []=h0p92.getD 16 [] := by
  decide +kernel

theorem h0n92_arithmetic_row17 :
    (BiPoly.mul h0p91 h0p57).getD 17 []=h0p92.getD 17 [] := by
  decide +kernel

theorem h0n92_arithmetic_row18 :
    (BiPoly.mul h0p91 h0p57).getD 18 []=h0p92.getD 18 [] := by
  decide +kernel

theorem h0n92_arithmetic_row19 :
    (BiPoly.mul h0p91 h0p57).getD 19 []=h0p92.getD 19 [] := by
  decide +kernel

theorem h0n92_arithmetic_row20 :
    (BiPoly.mul h0p91 h0p57).getD 20 []=h0p92.getD 20 [] := by
  decide +kernel

theorem h0n92_arithmetic_row21 :
    (BiPoly.mul h0p91 h0p57).getD 21 []=h0p92.getD 21 [] := by
  decide +kernel

theorem h0n92_arithmetic_row22 :
    (BiPoly.mul h0p91 h0p57).getD 22 []=h0p92.getD 22 [] := by
  decide +kernel

theorem h0n92_arithmetic_row23 :
    (BiPoly.mul h0p91 h0p57).getD 23 []=h0p92.getD 23 [] := by
  decide +kernel

theorem h0n92_arithmetic_row24 :
    (BiPoly.mul h0p91 h0p57).getD 24 []=h0p92.getD 24 [] := by
  decide +kernel

theorem h0n92_arithmetic : BiPoly.mul h0p91 h0p57=h0p92 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<25 at hk
    have hf : ∀ j : Fin 25, (BiPoly.mul h0p91 h0p57).getD j.val []=h0p92.getD j.val [] :=
      (fun j => Fin.cases h0n92_arithmetic_row0 (fun j => Fin.cases h0n92_arithmetic_row1 (fun j => Fin.cases h0n92_arithmetic_row2 (fun j => Fin.cases h0n92_arithmetic_row3 (fun j => Fin.cases h0n92_arithmetic_row4 (fun j => Fin.cases h0n92_arithmetic_row5 (fun j => Fin.cases h0n92_arithmetic_row6 (fun j => Fin.cases h0n92_arithmetic_row7 (fun j => Fin.cases h0n92_arithmetic_row8 (fun j => Fin.cases h0n92_arithmetic_row9 (fun j => Fin.cases h0n92_arithmetic_row10 (fun j => Fin.cases h0n92_arithmetic_row11 (fun j => Fin.cases h0n92_arithmetic_row12 (fun j => Fin.cases h0n92_arithmetic_row13 (fun j => Fin.cases h0n92_arithmetic_row14 (fun j => Fin.cases h0n92_arithmetic_row15 (fun j => Fin.cases h0n92_arithmetic_row16 (fun j => Fin.cases h0n92_arithmetic_row17 (fun j => Fin.cases h0n92_arithmetic_row18 (fun j => Fin.cases h0n92_arithmetic_row19 (fun j => Fin.cases h0n92_arithmetic_row20 (fun j => Fin.cases h0n92_arithmetic_row21 (fun j => Fin.cases h0n92_arithmetic_row22 (fun j => Fin.cases h0n92_arithmetic_row23 (fun j => Fin.cases h0n92_arithmetic_row24 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n92 : h0e92.toBi mapPolyEnv=h0p92 := by
  change BiPoly.mul (h0e91.toBi mapPolyEnv) (h0e57.toBi mapPolyEnv)=h0p92
  rw [h0n91, h0n57]
  exact h0n92_arithmetic

#print axioms h0n92_arithmetic
end StackSorting.RationalLift
