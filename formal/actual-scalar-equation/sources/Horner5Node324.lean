import BivariateRowEquality
import Horner5Base
import Horner5Node323
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p324 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 8642371241802064895), (Int.negSucc 94888697611879255679), (Int.ofNat 143084631395363915520), (Int.ofNat 1816827103630803309696), (Int.ofNat 447080777831125135872), (Int.negSucc 3805350119881900760447), (Int.negSucc 1901828068181358633215), (Int.ofNat 1770171518174390773632), (Int.ofNat 1007064834508085713920)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 112701419703328163328), (Int.ofNat 1183784193057025002240), (Int.negSucc 2190658556323717853183), (Int.negSucc 23270154400678516381439), (Int.negSucc 2391195275663120510975), (Int.ofNat 42627500051348113378560), (Int.ofNat 14908780273763325560832), (Int.negSucc 17297067564878828030207), (Int.negSucc 6845188638151441423871), (Int.ofNat 350376944480579966976)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 695576497450704438527), (Int.negSucc 6913407612239055326303), (Int.ofNat 15857895434039149471488), (Int.ofNat 138262836767325653463552), (Int.negSucc 2446976958231826222847), (Int.negSucc 214115385014469001952063), (Int.negSucc 54744095523374036140031), (Int.ofNat 66417196523510189726208), (Int.ofNat 22975217032817670137856), (Int.ofNat 885553453547449608096), (Int.negSucc 174717490144505958143)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2698959223742204597760), (Int.ofNat 25027652858453709674112), (Int.negSucc 71578241585433629714879), (Int.negSucc 502929801895551087951359), (Int.ofNat 47503755170569413471744), (Int.ofNat 627924332113132267623168), (Int.ofNat 152412495795785346415488), (Int.negSucc 117105202637783087357951), (Int.negSucc 62932168223155069701119), (Int.negSucc 12854690172412068560255), (Int.ofNat 2034837196719975540288), (Int.negSucc 91149441341948960255)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 7368383520908305756991), (Int.negSucc 62665057689260491604159), (Int.ofNat 224078806154096770309632), (Int.ofNat 1248406579918263078666432), (Int.negSucc 121832378667296446804415), (Int.negSucc 1178587785957500730779711), (Int.negSucc 432830574937676841756479), (Int.ofNat 41812475845773172147776), (Int.ofNat 152753226828259866296832), (Int.ofNat 39241420091304116625792), (Int.negSucc 3956567815526749486271), (Int.ofNat 256966181354295446400), (Int.negSucc 10133943425449620479)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 14991981032051263602816), (Int.ofNat 114606728597721054921648), (Int.negSucc 513339752098117804022543), (Int.negSucc 2240966486314665674712383), (Int.negSucc 33684003010566224509439), (Int.ofNat 1464304227257653831507104), (Int.ofNat 1098577816269574656348384), (Int.ofNat 236683136354342313125184), (Int.negSucc 242647805937274509133055), (Int.negSucc 67183248848804255822543), (Int.negSucc 6745431285793684690511), (Int.ofNat 1128700045962905036928), (Int.negSucc 29486773123961074943), (Int.ofNat 52796699608012800)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 23465164638492828753215), (Int.negSucc 157516176326198581751615), (Int.ofNat 887202306991967943139440), (Int.ofNat 3029894269610381759008032), (Int.ofNat 900537614026627158151680), (Int.negSucc 1177865141015788382469503), (Int.negSucc 1989664306214322738699359), (Int.negSucc 625920805196045114339135), (Int.ofNat 129622197807583241505600), (Int.ofNat 101426279740231959139776), (Int.ofNat 32368096268494262432496), (Int.negSucc 3541362845520644113247), (Int.ofNat 149567237445419675136), (Int.negSucc 1810457682922352639)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 28722628059788923272864), (Int.ofNat 164628667535721663929856), (Int.negSucc 1177783342161664858160015), (Int.negSucc 3219269620875470075829791), (Int.negSucc 2544128990404954218783167), (Int.ofNat 402800750548457830589568), (Int.ofNat 2295353904458048718749472), (Int.ofNat 1056590171300884038070464), (Int.ofNat 263626703359595429661216), (Int.negSucc 133931923014732938983295), (Int.negSucc 42909321304397818309775), (Int.negSucc 1087575562141151416223), (Int.ofNat 271157528741696705280), (Int.negSucc 7399440626307932159)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 27648255015909223115135), (Int.negSucc 130391915704778412976415), (Int.ofNat 1213257207308209202613024), (Int.ofNat 2854571659684594156875888), (Int.ofNat 4090462737220233532673664), (Int.ofNat 707705380182549956382144), (Int.negSucc 1425741655383126397834751), (Int.negSucc 1444731347818500734771999), (Int.negSucc 621894543782449474718207), (Int.ofNat 56691143882119834107552), (Int.ofNat 28057121666742833564832), (Int.ofNat 12820840271046778654704), (Int.negSucc 876456901993624532159), (Int.ofNat 12380118178220179968)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 20836053016211987610528), (Int.ofNat 76177347236453838312144), (Int.negSucc 974532204638267927096783), (Int.negSucc 2281313812146601199356271), (Int.negSucc 4439538270812752029098351), (Int.negSucc 2035652934915801997815743), (Int.negSucc 42761460785938367596607), (Int.ofNat 1372775794446350243286816), (Int.ofNat 665903352128727783487296), (Int.ofNat 162456891762922251436464), (Int.negSucc 15039301670044592760815), (Int.negSucc 13953573925923978921839), (Int.negSucc 351707515429642692335), (Int.ofNat 54770697367679835264)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 12085734326353061341631), (Int.negSucc 29921664999316394902367), (Int.ofNat 611489028204541855178736), (Int.ofNat 1723412820076049640293088), (Int.ofNat 3494830834359561157779456), (Int.ofNat 3053616665053021439908608), (Int.ofNat 1114484431227284204342400), (Int.negSucc 572374252147260611656511), (Int.negSucc 512646344336535848791487), (Int.negSucc 302866911069332123077439), (Int.negSucc 7062679150060353024431), (Int.ofNat 1390106533249481727840), (Int.ofNat 2266781928849697613568), (Int.negSucc 37180659970824488063)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5184628439512593455040), (Int.ofNat 4641075998588074546848), (Int.negSucc 300746499179278394834927), (Int.negSucc 1193354427997136823998639), (Int.negSucc 2140305374443420680071759), (Int.negSucc 3073166898467360808975551), (Int.negSucc 1532404126573902676336703), (Int.negSucc 399022734069951795341087), (Int.ofNat 286867107362522853300576), (Int.ofNat 218748078264070726001568), (Int.ofNat 50729904129411860448048), (Int.ofNat 6572650933061064553680), (Int.negSucc 1411073064721888028879), (Int.negSucc 121525851040361036927)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1482622666810697567039), (Int.ofNat 3415361677263433777536), (Int.ofNat 118000946455469656273824), (Int.ofNat 700722882839138022584784), (Int.ofNat 1138928138951711818485600), (Int.ofNat 2156304389251491100265856), (Int.ofNat 1520603378480293003295616), (Int.ofNat 822438381266633537869632), (Int.ofNat 15920517119746293891840), (Int.negSucc 61562653526087058884159), (Int.negSucc 63244586882797592346911), (Int.negSucc 6690921576345330736655), (Int.negSucc 874879533568831223519), (Int.ofNat 97233653314855210176)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 172734924155221076160), (Int.negSucc 3499261803674952776111), (Int.negSucc 39293169538371011586479), (Int.negSucc 326089218557701024742879), (Int.negSucc 590288792469224300147135), (Int.negSucc 1080799017727520310409631), (Int.negSucc 1191950993981747713447391), (Int.negSucc 707534482299752030928479), (Int.negSucc 248707666633375485572831), (Int.negSucc 25416021637603168756031), (Int.ofNat 26049129874042140354240), (Int.ofNat 6181019510488410973248), (Int.ofNat 1383229550423827830240), (Int.ofNat 76315705498456265088)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 66815439537937856064), (Int.ofNat 1869350545372421201280), (Int.ofNat 12655472973834081220176), (Int.ofNat 115283259186884077264608), (Int.ofNat 293334235940245625903616), (Int.ofNat 413797277868810687317376), (Int.ofNat 690360212940284239867488), (Int.ofNat 452084381720666404310016), (Int.ofNat 266923310098307788922112), (Int.ofNat 56659422493539120582720), (Int.ofNat 8851771942243350431616), (Int.negSucc 3475409825360952570239), (Int.negSucc 604886733481224531455), (Int.negSucc 91624975666513948799)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 41668275230323715807), (Int.negSucc 716841492325824398399), (Int.negSucc 4337727008141014631279), (Int.negSucc 30467368732599475019903), (Int.negSucc 122323106492547976716959), (Int.negSucc 144704221370012963645183), (Int.negSucc 277705551533670015652511), (Int.negSucc 247837042386341914546655), (Int.negSucc 159445469837109845492639), (Int.negSucc 58406482976711091935039), (Int.negSucc 15653353360424254876223), (Int.negSucc 710137753194840949439), (Int.ofNat 1436896422139558464), (Int.ofNat 5306116104230137344)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 11092069587064032768), (Int.ofNat 207925891970837855328), (Int.ofNat 1441379681976405214944), (Int.ofNat 6294068955091042703376), (Int.ofNat 37963824566598847589184), (Int.ofNat 54895587136926092654976), (Int.ofNat 75973304726944482178368), (Int.ofNat 108841854638064024068832), (Int.ofNat 67995724727218120258752), (Int.ofNat 37637101446477274800576), (Int.ofNat 10316832522995812226688), (Int.ofNat 2151657340204557017664), (Int.ofNat 207171721652664292992), (Int.ofNat 22476745785317518080)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1678517187855795935), (Int.negSucc 44851690750941382607), (Int.negSucc 393974846164958399855), (Int.negSucc 1228557961517300141615), (Int.negSucc 8085709945354420510127), (Int.negSucc 19705495890874242279167), (Int.negSucc 15994927208377277649791), (Int.negSucc 33088228052624184753791), (Int.negSucc 24496619040679241248703), (Int.negSucc 15367884975367657164863), (Int.negSucc 5129460598613213072447), (Int.negSucc 1330689887023615775999), (Int.negSucc 168641238778837911935), (Int.negSucc 9467008161392779775)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 136609115688801216), (Int.ofNat 6784212084932739456), (Int.ofNat 79566811833081212496), (Int.ofNat 273801862696915130400), (Int.ofNat 1110276828174837958272), (Int.ofNat 5216852537079760320768), (Int.ofNat 4019275286106019617024), (Int.ofNat 6013395023464624711680), (Int.ofNat 7393398414127600401792), (Int.ofNat 4272644381197898433600), (Int.ofNat 1918777350650141033856), (Int.ofNat 473377438000044336384), (Int.ofNat 63697265223965236224), (Int.ofNat 1387004722228237824)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 4403821409919359), (Int.negSucc 641285073989609183), (Int.negSucc 11039095127675551823), (Int.negSucc 57113067997745814959), (Int.negSucc 104686152488892455759), (Int.negSucc 860811897406665007295), (Int.negSucc 1239941785391498015423), (Int.negSucc 545787011743144490303), (Int.negSucc 1526781900420614182463), (Int.negSucc 920352331393189919999), (Int.negSucc 481059888932814422399), (Int.negSucc 115583097002641634303), (Int.negSucc 11210885576529781247), (Int.negSucc 67001551052709887)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 28554543532022400), (Int.ofNat 953856863499032928), (Int.ofNat 8182274516491884912), (Int.ofNat 13092073130115518112), (Int.ofNat 70999541762982255360), (Int.ofNat 277861745681165199744), (Int.ofNat 44507019590436687552), (Int.ofNat 153256189647036030336), (Int.ofNat 157644614006508434688), (Int.ofNat 78979737395701499904), (Int.ofNat 17924033474414078976), (Int.ofNat 718151641756655616)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 39797336015730431), (Int.negSucc 646090474862226239), (Int.negSucc 2313740214567318815), (Int.negSucc 842846121019462463), (Int.negSucc 33295366579573914047), (Int.negSucc 18355933432618304255), (Int.ofNat 3708293095687909248), (Int.negSucc 16785325035115043327), (Int.negSucc 8953790387593245695), (Int.negSucc 1235298630355181567)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 19761822144990720), (Int.ofNat 211640802660551808), (Int.negSucc 49101104464839359), (Int.ofNat 1216217009283034752), (Int.ofNat 4176914393162177280), (Int.negSucc 2398054713372324863), (Int.ofNat 664940410659454464), (Int.ofNat 584148539651235840)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3182771590069247), (Int.negSucc 27218391573807359), (Int.ofNat 79973227589933952), (Int.negSucc 339723332006215679), (Int.ofNat 188697356821255680)]]

theorem h5n324_arithmetic_row0 :
    (BiPoly.mul h5p5 h5p323).getD 0 []=h5p324.getD 0 [] := by
  decide +kernel

theorem h5n324_arithmetic_row1 :
    (BiPoly.mul h5p5 h5p323).getD 1 []=h5p324.getD 1 [] := by
  decide +kernel

theorem h5n324_arithmetic_row2 :
    (BiPoly.mul h5p5 h5p323).getD 2 []=h5p324.getD 2 [] := by
  decide +kernel

theorem h5n324_arithmetic_row3 :
    (BiPoly.mul h5p5 h5p323).getD 3 []=h5p324.getD 3 [] := by
  decide +kernel

theorem h5n324_arithmetic_row4 :
    (BiPoly.mul h5p5 h5p323).getD 4 []=h5p324.getD 4 [] := by
  decide +kernel

theorem h5n324_arithmetic_row5 :
    (BiPoly.mul h5p5 h5p323).getD 5 []=h5p324.getD 5 [] := by
  decide +kernel

theorem h5n324_arithmetic_row6 :
    (BiPoly.mul h5p5 h5p323).getD 6 []=h5p324.getD 6 [] := by
  decide +kernel

theorem h5n324_arithmetic_row7 :
    (BiPoly.mul h5p5 h5p323).getD 7 []=h5p324.getD 7 [] := by
  decide +kernel

theorem h5n324_arithmetic_row8 :
    (BiPoly.mul h5p5 h5p323).getD 8 []=h5p324.getD 8 [] := by
  decide +kernel

theorem h5n324_arithmetic_row9 :
    (BiPoly.mul h5p5 h5p323).getD 9 []=h5p324.getD 9 [] := by
  decide +kernel

theorem h5n324_arithmetic_row10 :
    (BiPoly.mul h5p5 h5p323).getD 10 []=h5p324.getD 10 [] := by
  decide +kernel

theorem h5n324_arithmetic_row11 :
    (BiPoly.mul h5p5 h5p323).getD 11 []=h5p324.getD 11 [] := by
  decide +kernel

theorem h5n324_arithmetic_row12 :
    (BiPoly.mul h5p5 h5p323).getD 12 []=h5p324.getD 12 [] := by
  decide +kernel

theorem h5n324_arithmetic_row13 :
    (BiPoly.mul h5p5 h5p323).getD 13 []=h5p324.getD 13 [] := by
  decide +kernel

theorem h5n324_arithmetic_row14 :
    (BiPoly.mul h5p5 h5p323).getD 14 []=h5p324.getD 14 [] := by
  decide +kernel

theorem h5n324_arithmetic_row15 :
    (BiPoly.mul h5p5 h5p323).getD 15 []=h5p324.getD 15 [] := by
  decide +kernel

theorem h5n324_arithmetic_row16 :
    (BiPoly.mul h5p5 h5p323).getD 16 []=h5p324.getD 16 [] := by
  decide +kernel

theorem h5n324_arithmetic_row17 :
    (BiPoly.mul h5p5 h5p323).getD 17 []=h5p324.getD 17 [] := by
  decide +kernel

theorem h5n324_arithmetic_row18 :
    (BiPoly.mul h5p5 h5p323).getD 18 []=h5p324.getD 18 [] := by
  decide +kernel

theorem h5n324_arithmetic_row19 :
    (BiPoly.mul h5p5 h5p323).getD 19 []=h5p324.getD 19 [] := by
  decide +kernel

theorem h5n324_arithmetic_row20 :
    (BiPoly.mul h5p5 h5p323).getD 20 []=h5p324.getD 20 [] := by
  decide +kernel

theorem h5n324_arithmetic_row21 :
    (BiPoly.mul h5p5 h5p323).getD 21 []=h5p324.getD 21 [] := by
  decide +kernel

theorem h5n324_arithmetic_row22 :
    (BiPoly.mul h5p5 h5p323).getD 22 []=h5p324.getD 22 [] := by
  decide +kernel

theorem h5n324_arithmetic_row23 :
    (BiPoly.mul h5p5 h5p323).getD 23 []=h5p324.getD 23 [] := by
  decide +kernel

theorem h5n324_arithmetic : BiPoly.mul h5p5 h5p323=h5p324 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<24 at hk
    have hf : ∀ j : Fin 24, (BiPoly.mul h5p5 h5p323).getD j.val []=h5p324.getD j.val [] :=
      (fun j => Fin.cases h5n324_arithmetic_row0 (fun j => Fin.cases h5n324_arithmetic_row1 (fun j => Fin.cases h5n324_arithmetic_row2 (fun j => Fin.cases h5n324_arithmetic_row3 (fun j => Fin.cases h5n324_arithmetic_row4 (fun j => Fin.cases h5n324_arithmetic_row5 (fun j => Fin.cases h5n324_arithmetic_row6 (fun j => Fin.cases h5n324_arithmetic_row7 (fun j => Fin.cases h5n324_arithmetic_row8 (fun j => Fin.cases h5n324_arithmetic_row9 (fun j => Fin.cases h5n324_arithmetic_row10 (fun j => Fin.cases h5n324_arithmetic_row11 (fun j => Fin.cases h5n324_arithmetic_row12 (fun j => Fin.cases h5n324_arithmetic_row13 (fun j => Fin.cases h5n324_arithmetic_row14 (fun j => Fin.cases h5n324_arithmetic_row15 (fun j => Fin.cases h5n324_arithmetic_row16 (fun j => Fin.cases h5n324_arithmetic_row17 (fun j => Fin.cases h5n324_arithmetic_row18 (fun j => Fin.cases h5n324_arithmetic_row19 (fun j => Fin.cases h5n324_arithmetic_row20 (fun j => Fin.cases h5n324_arithmetic_row21 (fun j => Fin.cases h5n324_arithmetic_row22 (fun j => Fin.cases h5n324_arithmetic_row23 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n324 : h5e324.toBi mapPolyEnv=h5p324 := by
  change BiPoly.mul (h5e5.toBi mapPolyEnv) (h5e323.toBi mapPolyEnv)=h5p324
  rw [h5n5, h5n323]
  exact h5n324_arithmetic

#print axioms h5n324_arithmetic
end StackSorting.RationalLift
