import BivariateRowEquality
import Horner4Base
import Horner4Node255
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p256 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 329086193074340543999), (Int.negSucc 2817528147735424784639), (Int.negSucc 5794418499424450030079), (Int.ofNat 5535709758465184903680), (Int.ofNat 18993185445184146086400), (Int.negSucc 2075747048955892465919), (Int.negSucc 12227246190911487859199)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4142025933531875170560), (Int.ofNat 35097699187418083592832), (Int.ofNat 70974758690803614757248), (Int.negSucc 66169191585444760028159), (Int.negSucc 210859562884138728058367), (Int.ofNat 42476354398099818290304), (Int.ofNat 118294716327205383916416), (Int.negSucc 6366573040943825222399)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 24766081629899331162239), (Int.negSucc 205622194471971660750527), (Int.negSucc 407413028088815337367487), (Int.ofNat 356820811283173148372736), (Int.ofNat 1088364211467982682245632), (Int.negSucc 260200818817133623360703), (Int.negSucc 492127129090019291097023), (Int.ofNat 7568891096048394403968), (Int.ofNat 1388128114960591292928)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 93493186985187195963840), (Int.ofNat 752191050583537304018400), (Int.ofNat 1462852822159702906355520), (Int.negSucc 1098493757018720167598495), (Int.negSucc 3439377427031256211984511), (Int.ofNat 690404723519492438748576), (Int.ofNat 1150991480440181535375168), (Int.ofNat 221440902710768587240992), (Int.negSucc 35253076583901169635263), (Int.ofNat 1473310868855035871232)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 249539516060050021691519), (Int.negSucc 1925463540803725051928639), (Int.negSucc 3708729936989690634043775), (Int.ofNat 1958283509823420459651648), (Int.ofNat 7401153754453302823750272), (Int.negSucc 384628890755468075321663), (Int.negSucc 1662727047257018172909311), (Int.negSucc 1220606228216199360268223), (Int.ofNat 155786901594425998282368), (Int.negSucc 9820658062464794155007), (Int.ofNat 313899436319947923456)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 499269104612618907697920), (Int.ofNat 3667565749248447736242816), (Int.ofNat 7120417227590979126333216), (Int.negSucc 1381698435295003316537951), (Int.negSucc 11340958721708045335229855), (Int.negSucc 2903682881787643624631039), (Int.ofNat 1478727890115310733531616), (Int.ofNat 2929908382709803718350752), (Int.negSucc 116976738675685504669919), (Int.negSucc 4543112034466572271679), (Int.negSucc 151691039234536877567), (Int.ofNat 20551101588993355776)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 774165113478427325245919), (Int.negSucc 5403983286058893284666255), (Int.negSucc 10852844513730232606476143), (Int.negSucc 2542286899464842947613231), (Int.ofNat 12184130349547682525097936), (Int.ofNat 10084906574027512131209712), (Int.negSucc 206988179437715879893391), (Int.negSucc 3582511145257917992381327), (Int.negSucc 833322769906892018094767), (Int.ofNat 127200963613449102721056), (Int.negSucc 6748909026029125511807), (Int.ofNat 124453102194146592768), (Int.negSucc 110414886102343679)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 948425698167033584949120), (Int.ofNat 6330910148889321708331296), (Int.ofNat 13577344900527328665521040), (Int.ofNat 9577679877612820544797056), (Int.negSucc 7555045259752958282009519), (Int.negSucc 17235369882773387704902623), (Int.negSucc 2947146472487779132458767), (Int.ofNat 1440837855159839875788384), (Int.ofNat 2652362212118194364365296), (Int.negSucc 217839845130274811983775), (Int.ofNat 7660246283817443276160), (Int.negSucc 256407133506466264319), (Int.ofNat 3582701703591588864)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 927548168799662681768799), (Int.negSucc 6022182633502332571447471), (Int.negSucc 14251274136510641949643087), (Int.negSucc 16380076936408983949444335), (Int.negSucc 1833080972520142309787423), (Int.ofNat 17667108085516677906131232), (Int.ofNat 8173665248484204463656848), (Int.ofNat 2224442639995823201285968), (Int.negSucc 3180902148452954664181471), (Int.negSucc 244853771193901094541775), (Int.ofNat 42710578256102932800544), (Int.negSucc 1740901570033632552319), (Int.ofNat 22913838859451357696)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 727063198137771663723200), (Int.ofNat 4727610105972652163721152), (Int.ofNat 12695727008360846601036272), (Int.ofNat 19201572607369882105881824), (Int.ofNat 11736789766881065244020544), (Int.negSucc 9164760430193197359527423), (Int.negSucc 12403989148869857820297807), (Int.negSucc 4656056768853032254913919), (Int.ofNat 743423258853980730980096), (Int.ofNat 1188692605506356373465664), (Int.negSucc 87956883772588810434399), (Int.ofNat 2030585696501969635136), (Int.negSucc 13181485962232860159)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 456281313057911663730879), (Int.negSucc 3097051503079263405344703), (Int.negSucc 9624011757845587232947631), (Int.negSucc 17207003808729480875475743), (Int.negSucc 17165054672919724954553279), (Int.negSucc 2940785985708446539295135), (Int.ofNat 11028706429408390529275760), (Int.ofNat 5226788413189927988267312), (Int.ofNat 2501989544592646340717712), (Int.negSucc 1326469239168499948918671), (Int.negSucc 51108346015143777184143), (Int.ofNat 8325550373358096176160), (Int.negSucc 224362052077864451327)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 227913783795246817713600), (Int.ofNat 1700180846623916945559712), (Int.ofNat 6182731620565467150837120), (Int.ofNat 12492582678155612241393616), (Int.ofNat 16369024119836616942922864), (Int.ofNat 11075975402668501470080464), (Int.negSucc 3958805690974828976005087), (Int.negSucc 4595383232910475696758639), (Int.negSucc 3347483702071622771619103), (Int.ofNat 67147853395816051791216), (Int.ofNat 289645253082696013917584), (Int.negSucc 12501355366000318751359), (Int.negSucc 16813016164695137215)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 89613483230940838269759), (Int.negSucc 778681121817003086649375), (Int.negSucc 3336444920016002758870623), (Int.negSucc 7631280565406206829979007), (Int.negSucc 11713624911803131014497343), (Int.negSucc 12205026660075451023292239), (Int.negSucc 3412990430419618299295151), (Int.ofNat 2666871495166342391056000), (Int.ofNat 1997639622132003538449664), (Int.ofNat 1144643755053704796725552), (Int.negSucc 248392226556207952567903), (Int.negSucc 12653513463824128149103), (Int.ofNat 856730857381940460064)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 27249448299625674930560), (Int.ofNat 293526803759976313511168), (Int.ofNat 1493191574499605262237696), (Int.ofNat 3990897153725400460218272), (Int.ofNat 6722738372552990563949600), (Int.ofNat 8766168107540960516881104), (Int.ofNat 6383895978965884032962848), (Int.ofNat 80476349790326124455200), (Int.negSucc 576376128582158471995871), (Int.negSucc 1059207433522611465314095), (Int.negSucc 72219066336994340975695), (Int.ofNat 33960181093780327222176), (Int.negSucc 125567205625833950975)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 6236113818029361034079), (Int.negSucc 89070222757960268200591), (Int.negSucc 544977025644342698396687), (Int.negSucc 1774198856856725808353455), (Int.negSucc 3258272085780665036306127), (Int.negSucc 4687099095173022479320735), (Int.negSucc 5172905729097209174859167), (Int.negSucc 1935775146024779555526143), (Int.negSucc 153199602530971791073279), (Int.ofNat 307155043390339922892272), (Int.ofNat 242482559999889905769216), (Int.negSucc 12068005605773950330495), (Int.negSucc 1534956952083325944191)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1029375263902455522560), (Int.ofNat 21099642086138365580768), (Int.ofNat 158742041014336052417168), (Int.ofNat 652362422313696577846368), (Int.ofNat 1375160299027003019448592), (Int.ofNat 2010273196300093443799024), (Int.ofNat 2728236457226805876378640), (Int.ofNat 2031710978650530062946864), (Int.ofNat 477807658070679924432336), (Int.ofNat 126827108681208135182976), (Int.negSucc 133704895198352240805407), (Int.negSucc 19311607853425665213791), (Int.ofNat 897472605362748010176)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 114193676354466761439), (Int.negSucc 3740944649041596475887), (Int.negSucc 35880311153695084799951), (Int.negSucc 190932343004811355079215), (Int.negSucc 500067307162548619003327), (Int.negSucc 744160046922041751708815), (Int.negSucc 1036913563291724966951327), (Int.negSucc 1181294434419306232095215), (Int.negSucc 511701841490578585116863), (Int.negSucc 170556495361247379461951), (Int.negSucc 6003052299292797755711), (Int.ofNat 18964174940512127441088), (Int.ofNat 870496912233782872704)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7456060173679238080), (Int.ofNat 465994442359710662208), (Int.ofNat 6055594620535106225264), (Int.ofNat 42571028774896994677472), (Int.ofNat 149057386514536219302624), (Int.ofNat 248821153528100984816080), (Int.ofNat 309614588716704480728400), (Int.ofNat 441515491512409822601184), (Int.ofNat 327731216173595354891808), (Int.ofNat 110723292330839519976672), (Int.ofNat 40036097801930005790208), (Int.negSucc 2869307703417257575871), (Int.negSucc 962935541072807939711)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 207310741824700799), (Int.negSucc 36415020282688485215), (Int.negSucc 719621248896610701455), (Int.negSucc 6861049276645308776447), (Int.negSucc 34061503261719919502399), (Int.negSucc 72703950721942255338863), (Int.negSucc 82531626455613285986879), (Int.negSucc 110965947923892943300223), (Int.negSucc 130696820855139679860863), (Int.negSucc 58656536104667396869055), (Int.negSucc 22779545363286739874495), (Int.negSucc 3987191881330605346175), (Int.ofNat 99657209047499923968)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1349514440707512960), (Int.ofNat 54077286482235162144), (Int.ofNat 741946810898692978032), (Int.ofNat 5539831313432538775344), (Int.ofNat 16881671380259231156160), (Int.ofNat 21345944647698414869280), (Int.ofNat 20305201417322755905120), (Int.ofNat 31943191968818728023744), (Int.ofNat 23153345695500641900928), (Int.ofNat 8188432506279047751552), (Int.ofNat 2647351985085321469056), (Int.ofNat 225207740932222848768)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1955588757357605759), (Int.negSucc 47181700599042142367), (Int.negSucc 580900518828550320479), (Int.negSucc 2798715706109407176767), (Int.negSucc 4855356108888410731967), (Int.negSucc 3497520027153562024895), (Int.negSucc 4443872620302984508415), (Int.negSucc 5796497013371357548031), (Int.negSucc 2400385581489290252543), (Int.negSucc 795271782071507397119), (Int.negSucc 116450701435285161983)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1279119197950307712), (Int.ofNat 32602238091192844512), (Int.ofNat 293182917942790696608), (Int.ofNat 807551119523468817792), (Int.ofNat 696054014727476728896), (Int.ofNat 300489670808985647232), (Int.ofNat 775308716905274021376), (Int.ofNat 525889116188665012224), (Int.ofNat 152335618265961960192), (Int.ofNat 22356170535335192064)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 553934728937191679), (Int.negSucc 15515767181707057727), (Int.negSucc 82688704527558354623), (Int.negSucc 116526927085828742015), (Int.negSucc 17294622219866539007), (Int.negSucc 27846863851523643647), (Int.negSucc 66757767959944482047), (Int.negSucc 20736665948669326847), (Int.negSucc 1498700985252618239)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 168190434662976000), (Int.ofNat 4013937447081681024), (Int.ofNat 11203531151048949888), (Int.ofNat 4550652449587226880), (Int.negSucc 4971238652075597567), (Int.ofNat 3391607354426141184), (Int.ofNat 1498700985252618240)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 23107997545878527), (Int.negSucc 417955648738205951), (Int.negSucc 501416804875767551), (Int.ofNat 484125004834260480)]]

theorem h4n256_arithmetic_row0 :
    (BiPoly.mul h4p5 h4p255).getD 0 []=h4p256.getD 0 [] := by
  decide +kernel

theorem h4n256_arithmetic_row1 :
    (BiPoly.mul h4p5 h4p255).getD 1 []=h4p256.getD 1 [] := by
  decide +kernel

theorem h4n256_arithmetic_row2 :
    (BiPoly.mul h4p5 h4p255).getD 2 []=h4p256.getD 2 [] := by
  decide +kernel

theorem h4n256_arithmetic_row3 :
    (BiPoly.mul h4p5 h4p255).getD 3 []=h4p256.getD 3 [] := by
  decide +kernel

theorem h4n256_arithmetic_row4 :
    (BiPoly.mul h4p5 h4p255).getD 4 []=h4p256.getD 4 [] := by
  decide +kernel

theorem h4n256_arithmetic_row5 :
    (BiPoly.mul h4p5 h4p255).getD 5 []=h4p256.getD 5 [] := by
  decide +kernel

theorem h4n256_arithmetic_row6 :
    (BiPoly.mul h4p5 h4p255).getD 6 []=h4p256.getD 6 [] := by
  decide +kernel

theorem h4n256_arithmetic_row7 :
    (BiPoly.mul h4p5 h4p255).getD 7 []=h4p256.getD 7 [] := by
  decide +kernel

theorem h4n256_arithmetic_row8 :
    (BiPoly.mul h4p5 h4p255).getD 8 []=h4p256.getD 8 [] := by
  decide +kernel

theorem h4n256_arithmetic_row9 :
    (BiPoly.mul h4p5 h4p255).getD 9 []=h4p256.getD 9 [] := by
  decide +kernel

theorem h4n256_arithmetic_row10 :
    (BiPoly.mul h4p5 h4p255).getD 10 []=h4p256.getD 10 [] := by
  decide +kernel

theorem h4n256_arithmetic_row11 :
    (BiPoly.mul h4p5 h4p255).getD 11 []=h4p256.getD 11 [] := by
  decide +kernel

theorem h4n256_arithmetic_row12 :
    (BiPoly.mul h4p5 h4p255).getD 12 []=h4p256.getD 12 [] := by
  decide +kernel

theorem h4n256_arithmetic_row13 :
    (BiPoly.mul h4p5 h4p255).getD 13 []=h4p256.getD 13 [] := by
  decide +kernel

theorem h4n256_arithmetic_row14 :
    (BiPoly.mul h4p5 h4p255).getD 14 []=h4p256.getD 14 [] := by
  decide +kernel

theorem h4n256_arithmetic_row15 :
    (BiPoly.mul h4p5 h4p255).getD 15 []=h4p256.getD 15 [] := by
  decide +kernel

theorem h4n256_arithmetic_row16 :
    (BiPoly.mul h4p5 h4p255).getD 16 []=h4p256.getD 16 [] := by
  decide +kernel

theorem h4n256_arithmetic_row17 :
    (BiPoly.mul h4p5 h4p255).getD 17 []=h4p256.getD 17 [] := by
  decide +kernel

theorem h4n256_arithmetic_row18 :
    (BiPoly.mul h4p5 h4p255).getD 18 []=h4p256.getD 18 [] := by
  decide +kernel

theorem h4n256_arithmetic_row19 :
    (BiPoly.mul h4p5 h4p255).getD 19 []=h4p256.getD 19 [] := by
  decide +kernel

theorem h4n256_arithmetic_row20 :
    (BiPoly.mul h4p5 h4p255).getD 20 []=h4p256.getD 20 [] := by
  decide +kernel

theorem h4n256_arithmetic_row21 :
    (BiPoly.mul h4p5 h4p255).getD 21 []=h4p256.getD 21 [] := by
  decide +kernel

theorem h4n256_arithmetic_row22 :
    (BiPoly.mul h4p5 h4p255).getD 22 []=h4p256.getD 22 [] := by
  decide +kernel

theorem h4n256_arithmetic_row23 :
    (BiPoly.mul h4p5 h4p255).getD 23 []=h4p256.getD 23 [] := by
  decide +kernel

theorem h4n256_arithmetic_row24 :
    (BiPoly.mul h4p5 h4p255).getD 24 []=h4p256.getD 24 [] := by
  decide +kernel

theorem h4n256_arithmetic : BiPoly.mul h4p5 h4p255=h4p256 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<25 at hk
    have hf : ∀ j : Fin 25, (BiPoly.mul h4p5 h4p255).getD j.val []=h4p256.getD j.val [] :=
      (fun j => Fin.cases h4n256_arithmetic_row0 (fun j => Fin.cases h4n256_arithmetic_row1 (fun j => Fin.cases h4n256_arithmetic_row2 (fun j => Fin.cases h4n256_arithmetic_row3 (fun j => Fin.cases h4n256_arithmetic_row4 (fun j => Fin.cases h4n256_arithmetic_row5 (fun j => Fin.cases h4n256_arithmetic_row6 (fun j => Fin.cases h4n256_arithmetic_row7 (fun j => Fin.cases h4n256_arithmetic_row8 (fun j => Fin.cases h4n256_arithmetic_row9 (fun j => Fin.cases h4n256_arithmetic_row10 (fun j => Fin.cases h4n256_arithmetic_row11 (fun j => Fin.cases h4n256_arithmetic_row12 (fun j => Fin.cases h4n256_arithmetic_row13 (fun j => Fin.cases h4n256_arithmetic_row14 (fun j => Fin.cases h4n256_arithmetic_row15 (fun j => Fin.cases h4n256_arithmetic_row16 (fun j => Fin.cases h4n256_arithmetic_row17 (fun j => Fin.cases h4n256_arithmetic_row18 (fun j => Fin.cases h4n256_arithmetic_row19 (fun j => Fin.cases h4n256_arithmetic_row20 (fun j => Fin.cases h4n256_arithmetic_row21 (fun j => Fin.cases h4n256_arithmetic_row22 (fun j => Fin.cases h4n256_arithmetic_row23 (fun j => Fin.cases h4n256_arithmetic_row24 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n256 : h4e256.toBi mapPolyEnv=h4p256 := by
  change BiPoly.mul (h4e5.toBi mapPolyEnv) (h4e255.toBi mapPolyEnv)=h4p256
  rw [h4n5, h4n255]
  exact h4n256_arithmetic

#print axioms h4n256_arithmetic
end StackSorting.RationalLift
