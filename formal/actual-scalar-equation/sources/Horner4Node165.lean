import BivariateRowEquality
import Horner4Base
import Horner4Node164
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p165 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 740443934417266224000), (Int.ofNat 6339438332404705765440), (Int.ofNat 13037441623705012567680), (Int.negSucc 12455346956546666033279), (Int.negSucc 42734667251664328694399), (Int.ofNat 4670430860150758048320), (Int.ofNat 27511303929550847683200)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 9319558350446719133759), (Int.negSucc 78969823171690688083871), (Int.negSucc 159693207054308133203807), (Int.ofNat 148880681067250710063360), (Int.ofNat 474434016489312138131328), (Int.negSucc 95571797395724591153183), (Int.negSucc 266163111736212113811935), (Int.ofNat 14324789342123606750400)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 55723683667273495115040), (Int.ofNat 462649937561936236688688), (Int.ofNat 916679313199834509076848), (Int.negSucc 802846825387139583838655), (Int.negSucc 2448819475802961035052671), (Int.ofNat 585451842338550652561584), (Int.ofNat 1107286040452543404968304), (Int.negSucc 17030004966108887408927), (Int.negSucc 3123288258661330409087)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 210359670716671190918639), (Int.negSucc 1692429863812958934041399), (Int.negSucc 3291418849859331539299919), (Int.ofNat 2471610953292120377096616), (Int.ofNat 7738599210820326476965152), (Int.negSucc 1553410627918857987184295), (Int.negSucc 2589730830990408454594127), (Int.negSucc 498242031099229321292231), (Int.ofNat 79319422313777631679344), (Int.negSucc 3314949454923830710271)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 561463911135112548805920), (Int.ofNat 4332292966808381366839440), (Int.ofNat 8344642358226803926598496), (Int.negSucc 4406137897102696034216207), (Int.negSucc 16652595947519931353438111), (Int.ofNat 865415004199803169473744), (Int.ofNat 3741135856328290889045952), (Int.ofNat 2746364013486448560603504), (Int.negSucc 350520528587458496135327), (Int.ofNat 22096480640545786848768), (Int.negSucc 706273731719882827775)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1123355485378392542320319), (Int.negSucc 8252022935809007406546335), (Int.negSucc 16020938762079703034249735), (Int.ofNat 3108821479413757462210392), (Int.ofNat 25517157123843102004267176), (Int.ofNat 6533286484022198155419840), (Int.negSucc 3327137752759449150446135), (Int.negSucc 6592293861097058366289191), (Int.ofNat 263197662020292385507320), (Int.ofNat 10222002077549787611280), (Int.ofNat 341304838277707974528), (Int.negSucc 46239978575235050495)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1741871505326461481803320), (Int.ofNat 12158962393632509890499076), (Int.ofNat 24418900155893023364571324), (Int.ofNat 5720145523795896632129772), (Int.negSucc 27414293286482285681470355), (Int.negSucc 22691039791561902295221851), (Int.ofNat 465723403734860729760132), (Int.ofNat 8060650076830315482857988), (Int.ofNat 1874976232290507040713228), (Int.negSucc 286202168130260481122375), (Int.ofNat 15185045308565532401568), (Int.negSucc 280019479936829833727), (Int.ofNat 248433493730273280)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2133957820875825566135519), (Int.negSucc 14244547835000973843745415), (Int.negSucc 30549026026186489497422339), (Int.negSucc 21549779724628846225793375), (Int.ofNat 16998851834444156134521420), (Int.ofNat 38779582236240122336030904), (Int.ofNat 6631079563097503048032228), (Int.negSucc 3241885174109639720523863), (Int.negSucc 5967814977265937319821915), (Int.ofNat 490139651543118326963496), (Int.negSucc 17235554138589247371359), (Int.ofNat 576916050389549094720), (Int.negSucc 8061078833081074943)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2086983379799241033979800), (Int.ofNat 13549910925380248285756812), (Int.ofNat 32065366807148944386696948), (Int.ofNat 36855173106920213886249756), (Int.ofNat 4124432188170320197021704), (Int.negSucc 39750993192412525288795271), (Int.negSucc 18390746809089460043227907), (Int.negSucc 5004995939990602202893427), (Int.ofNat 7157029834019147994408312), (Int.ofNat 550920985186277462718996), (Int.negSucc 96098801076231598801223), (Int.ofNat 3917028532575673242720), (Int.negSucc 51556137433765554815)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1635892195809986243377199), (Int.negSucc 10637122738438467368372591), (Int.negSucc 28565385768811904852331611), (Int.negSucc 43203538366582234738234103), (Int.negSucc 26407776975482396799046223), (Int.ofNat 20620710967934694058936704), (Int.ofNat 27908975584957180095670068), (Int.ofNat 10476127729919322573556320), (Int.negSucc 1672702332421456644705215), (Int.negSucc 2674558362389301840297743), (Int.ofNat 197902988488324823477400), (Int.negSucc 4568817817129431679055), (Int.ofNat 29658343415023935360)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1026632954380301243394480), (Int.ofNat 6968365881928342662025584), (Int.ofNat 21654026455152571274132172), (Int.ofNat 38715758569641331969820424), (Int.ofNat 38621373014069381147744880), (Int.ofNat 6616768467844004713414056), (Int.negSucc 24814589466168878690870459), (Int.negSucc 11760273929677337973601451), (Int.negSucc 5629476475333454266614851), (Int.ofNat 2984555788129124885067012), (Int.ofNat 114993778534073498664324), (Int.negSucc 18732488340055716396359), (Int.ofNat 504814617175195015488)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 512806013539305339855599), (Int.negSucc 3825406904903813127509351), (Int.negSucc 13911146146272301089383519), (Int.negSucc 28108311025850127543135635), (Int.negSucc 36830304269632388121576443), (Int.negSucc 24920944656004128307681043), (Int.ofNat 8907312804693365196011448), (Int.ofNat 10339612274048570317706940), (Int.ofNat 7531838329661151236142984), (Int.negSucc 151082670140586116530235), (Int.negSucc 651701819436066031314563), (Int.ofNat 28128049573500717190560), (Int.ofNat 37829286370564058736)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 201630337269616886106960), (Int.ofNat 1752032524088256944961096), (Int.ofNat 7507001070036006207458904), (Int.ofNat 17170381272163965367452768), (Int.ofNat 26355656051557044782619024), (Int.ofNat 27461309985169764802407540), (Int.ofNat 7679228468444141173414092), (Int.negSucc 6000460864124270379875999), (Int.negSucc 4494689149797007961511743), (Int.negSucc 2575448448870835792632491), (Int.ofNat 558882509751467893277784), (Int.ofNat 28470405293604288335484), (Int.negSucc 1927644429109366035143)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 61311258674157768593759), (Int.negSucc 660435308459946705400127), (Int.negSucc 3359681042624111840034815), (Int.negSucc 8979518595882151035491111), (Int.negSucc 15126161338244228768886599), (Int.negSucc 19723878241967161162982483), (Int.negSucc 14363765952673239074166407), (Int.negSucc 181071787028233780024199), (Int.ofNat 1296846289309856561990712), (Int.ofNat 2383216725425875796956716), (Int.ofNat 162492899258237267195316), (Int.negSucc 76410407461005736249895), (Int.ofNat 282526212658126389696)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 14031256090566062326680), (Int.ofNat 200408001205410603451332), (Int.ofNat 1226198307699771071392548), (Int.ofNat 3991947427927633068795276), (Int.ofNat 7331112193006496331688788), (Int.ofNat 10545972964139300578471656), (Int.ofNat 11639037890468720643433128), (Int.ofNat 4355494078555753999933824), (Int.ofNat 344699105694686529914880), (Int.negSucc 691098847628264826507611), (Int.negSucc 545585759999752287980735), (Int.ofNat 27153012612991388243616), (Int.ofNat 3453653142187483374432)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2316094343780524925759), (Int.negSucc 47474194693811322556727), (Int.negSucc 357169592282256117938627), (Int.negSucc 1467815450205817300154327), (Int.negSucc 3094110672810756793759331), (Int.negSucc 4523114691675210248547803), (Int.negSucc 6138532028760313221851939), (Int.negSucc 4571349701963692641630443), (Int.negSucc 1075067230659029829972755), (Int.negSucc 285360994532718304161695), (Int.ofNat 300836014196292541812168), (Int.ofNat 43451117670207746731032), (Int.negSucc 2019313362066183022895)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 256935771797550213240), (Int.ofNat 8417125460343592070748), (Int.ofNat 80730700095813940799892), (Int.ofNat 429597771760825548928236), (Int.ofNat 1125151441115734392757488), (Int.ofNat 1674360105574593941344836), (Int.ofNat 2333055517406381175640488), (Int.ofNat 2657912477443439022214236), (Int.ofNat 1151329143353801816512944), (Int.ofNat 383752114562806603789392), (Int.ofNat 13506867673408794950352), (Int.negSucc 42669393616152286742447), (Int.negSucc 1958618052526011463583)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 16776135390778285679), (Int.negSucc 1048487495309348989967), (Int.negSucc 13625087896203989006843), (Int.negSucc 95784814743518238024311), (Int.negSucc 335379119657706493430903), (Int.negSucc 559847595438227215836179), (Int.negSucc 696632824612585081638899), (Int.negSucc 993409855902922100852663), (Int.negSucc 737395236390589548506567), (Int.negSucc 249127407744388919947511), (Int.negSucc 90081220054342513027967), (Int.ofNat 6455942332688829545712), (Int.ofNat 2166604967413817864352)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 466449169105576800), (Int.ofNat 81933795636049091736), (Int.ofNat 1619147810017374078276), (Int.ofNat 15437360872451944747008), (Int.ofNat 76638382338869818880400), (Int.ofNat 163583889124370074512444), (Int.ofNat 185696159525129893470480), (Int.ofNat 249673382828759122425504), (Int.ofNat 294067846924064279686944), (Int.ofNat 131977206235501642955376), (Int.ofNat 51253977067395164717616), (Int.ofNat 8971181732993862028896), (Int.negSucc 224228720356874828927)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3036407491591904159), (Int.negSucc 121673894585029114823), (Int.negSucc 1669380324522059200571), (Int.negSucc 12464620455223212244523), (Int.negSucc 37983760605583270101359), (Int.negSucc 48028375457321433455879), (Int.negSucc 45686703188976200786519), (Int.negSucc 71872181929842138053423), (Int.negSucc 52095027814876444277087), (Int.negSucc 18423973139127857440991), (Int.negSucc 5956541966441973305375), (Int.negSucc 506717417097501409727)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4400074704054612960), (Int.ofNat 106158826347844820328), (Int.ofNat 1307026167364238221080), (Int.ofNat 6297110338746166147728), (Int.ofNat 10924551244998924146928), (Int.ofNat 7869420061095514556016), (Int.ofNat 9998713395681715143936), (Int.ofNat 13042118280085554483072), (Int.ofNat 5400867558350903068224), (Int.ofNat 1789361509660891643520), (Int.ofNat 262014078229391614464)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2878018195388192351), (Int.negSucc 73355035705183900151), (Int.negSucc 659661565371279067367), (Int.negSucc 1816990018927804840031), (Int.negSucc 1566121533136822640015), (Int.negSucc 676101759320217706271), (Int.negSucc 1744444613036866548095), (Int.negSucc 1183250511424496277503), (Int.negSucc 342755141098414410431), (Int.negSucc 50301383704504182143)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1246353140108681280), (Int.ofNat 34910476158840879888), (Int.ofNat 186049585187006297904), (Int.ofNat 262185585943114669536), (Int.ofNat 38912899994699712768), (Int.ofNat 62655443665928198208), (Int.ofNat 150204977909875084608), (Int.ofNat 46657498384505985408), (Int.ofNat 3372077216818391040)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 378428477991695999), (Int.negSucc 9031359255933782303), (Int.negSucc 25207945089860137247), (Int.negSucc 10238968011571260479), (Int.ofNat 11185286967170094528), (Int.negSucc 7631116547458817663), (Int.negSucc 3372077216818391039)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 51992994478226688), (Int.ofNat 940400209660963392), (Int.ofNat 1128187810970476992), (Int.negSucc 1089281260877086079)]]

theorem h4n165_arithmetic_row0 :
    (BiPoly.mul h4p5 h4p164).getD 0 []=h4p165.getD 0 [] := by
  decide +kernel

theorem h4n165_arithmetic_row1 :
    (BiPoly.mul h4p5 h4p164).getD 1 []=h4p165.getD 1 [] := by
  decide +kernel

theorem h4n165_arithmetic_row2 :
    (BiPoly.mul h4p5 h4p164).getD 2 []=h4p165.getD 2 [] := by
  decide +kernel

theorem h4n165_arithmetic_row3 :
    (BiPoly.mul h4p5 h4p164).getD 3 []=h4p165.getD 3 [] := by
  decide +kernel

theorem h4n165_arithmetic_row4 :
    (BiPoly.mul h4p5 h4p164).getD 4 []=h4p165.getD 4 [] := by
  decide +kernel

theorem h4n165_arithmetic_row5 :
    (BiPoly.mul h4p5 h4p164).getD 5 []=h4p165.getD 5 [] := by
  decide +kernel

theorem h4n165_arithmetic_row6 :
    (BiPoly.mul h4p5 h4p164).getD 6 []=h4p165.getD 6 [] := by
  decide +kernel

theorem h4n165_arithmetic_row7 :
    (BiPoly.mul h4p5 h4p164).getD 7 []=h4p165.getD 7 [] := by
  decide +kernel

theorem h4n165_arithmetic_row8 :
    (BiPoly.mul h4p5 h4p164).getD 8 []=h4p165.getD 8 [] := by
  decide +kernel

theorem h4n165_arithmetic_row9 :
    (BiPoly.mul h4p5 h4p164).getD 9 []=h4p165.getD 9 [] := by
  decide +kernel

theorem h4n165_arithmetic_row10 :
    (BiPoly.mul h4p5 h4p164).getD 10 []=h4p165.getD 10 [] := by
  decide +kernel

theorem h4n165_arithmetic_row11 :
    (BiPoly.mul h4p5 h4p164).getD 11 []=h4p165.getD 11 [] := by
  decide +kernel

theorem h4n165_arithmetic_row12 :
    (BiPoly.mul h4p5 h4p164).getD 12 []=h4p165.getD 12 [] := by
  decide +kernel

theorem h4n165_arithmetic_row13 :
    (BiPoly.mul h4p5 h4p164).getD 13 []=h4p165.getD 13 [] := by
  decide +kernel

theorem h4n165_arithmetic_row14 :
    (BiPoly.mul h4p5 h4p164).getD 14 []=h4p165.getD 14 [] := by
  decide +kernel

theorem h4n165_arithmetic_row15 :
    (BiPoly.mul h4p5 h4p164).getD 15 []=h4p165.getD 15 [] := by
  decide +kernel

theorem h4n165_arithmetic_row16 :
    (BiPoly.mul h4p5 h4p164).getD 16 []=h4p165.getD 16 [] := by
  decide +kernel

theorem h4n165_arithmetic_row17 :
    (BiPoly.mul h4p5 h4p164).getD 17 []=h4p165.getD 17 [] := by
  decide +kernel

theorem h4n165_arithmetic_row18 :
    (BiPoly.mul h4p5 h4p164).getD 18 []=h4p165.getD 18 [] := by
  decide +kernel

theorem h4n165_arithmetic_row19 :
    (BiPoly.mul h4p5 h4p164).getD 19 []=h4p165.getD 19 [] := by
  decide +kernel

theorem h4n165_arithmetic_row20 :
    (BiPoly.mul h4p5 h4p164).getD 20 []=h4p165.getD 20 [] := by
  decide +kernel

theorem h4n165_arithmetic_row21 :
    (BiPoly.mul h4p5 h4p164).getD 21 []=h4p165.getD 21 [] := by
  decide +kernel

theorem h4n165_arithmetic_row22 :
    (BiPoly.mul h4p5 h4p164).getD 22 []=h4p165.getD 22 [] := by
  decide +kernel

theorem h4n165_arithmetic_row23 :
    (BiPoly.mul h4p5 h4p164).getD 23 []=h4p165.getD 23 [] := by
  decide +kernel

theorem h4n165_arithmetic_row24 :
    (BiPoly.mul h4p5 h4p164).getD 24 []=h4p165.getD 24 [] := by
  decide +kernel

theorem h4n165_arithmetic : BiPoly.mul h4p5 h4p164=h4p165 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<25 at hk
    have hf : ∀ j : Fin 25, (BiPoly.mul h4p5 h4p164).getD j.val []=h4p165.getD j.val [] :=
      (fun j => Fin.cases h4n165_arithmetic_row0 (fun j => Fin.cases h4n165_arithmetic_row1 (fun j => Fin.cases h4n165_arithmetic_row2 (fun j => Fin.cases h4n165_arithmetic_row3 (fun j => Fin.cases h4n165_arithmetic_row4 (fun j => Fin.cases h4n165_arithmetic_row5 (fun j => Fin.cases h4n165_arithmetic_row6 (fun j => Fin.cases h4n165_arithmetic_row7 (fun j => Fin.cases h4n165_arithmetic_row8 (fun j => Fin.cases h4n165_arithmetic_row9 (fun j => Fin.cases h4n165_arithmetic_row10 (fun j => Fin.cases h4n165_arithmetic_row11 (fun j => Fin.cases h4n165_arithmetic_row12 (fun j => Fin.cases h4n165_arithmetic_row13 (fun j => Fin.cases h4n165_arithmetic_row14 (fun j => Fin.cases h4n165_arithmetic_row15 (fun j => Fin.cases h4n165_arithmetic_row16 (fun j => Fin.cases h4n165_arithmetic_row17 (fun j => Fin.cases h4n165_arithmetic_row18 (fun j => Fin.cases h4n165_arithmetic_row19 (fun j => Fin.cases h4n165_arithmetic_row20 (fun j => Fin.cases h4n165_arithmetic_row21 (fun j => Fin.cases h4n165_arithmetic_row22 (fun j => Fin.cases h4n165_arithmetic_row23 (fun j => Fin.cases h4n165_arithmetic_row24 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n165 : h4e165.toBi mapPolyEnv=h4p165 := by
  change BiPoly.mul (h4e5.toBi mapPolyEnv) (h4e164.toBi mapPolyEnv)=h4p165
  rw [h4n5, h4n164]
  exact h4n165_arithmetic

#print axioms h4n165_arithmetic
end StackSorting.RationalLift
