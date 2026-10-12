import BivariateRowEquality
import Horner2Base
import Horner2Node045
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p100 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2880790413934021632), (Int.ofNat 28748775456692396928), (Int.negSucc 76443652588480368767), (Int.negSucc 529165381955120734463), (Int.ofNat 380138456011412355840), (Int.ofNat 888311583949221230976), (Int.negSucc 254368894555435019903), (Int.negSucc 335688278169361904639)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 34686349487175366143), (Int.negSucc 331159606075140571007), (Int.ofNat 984935472261232819968), (Int.ofNat 6242617279343151906048), (Int.negSucc 5065413731444032713215), (Int.negSucc 8255441368389450515327), (Int.ofNat 3031479049246240308480), (Int.ofNat 2398521860877340463616), (Int.negSucc 116792314826859988991)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 197172482996392780032), (Int.ofNat 1776137115008151757728), (Int.negSucc 6077166787426635428255), (Int.negSucc 33767828189005430486879), (Int.ofNat 29518073443638673181280), (Int.ofNat 33598280192794876954080), (Int.negSucc 12318769302423957932255), (Int.negSucc 7421774344535431512863), (Int.negSucc 353423647897318522079), (Int.ofNat 58239163381501986048)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 702480591584342085887), (Int.negSucc 5863933246225409381087), (Int.ofNat 23646180320609983857792), (Int.ofNat 110229258788901614972448), (Int.negSucc 96545770402119412948415), (Int.negSucc 79164060109463132638559), (Int.ofNat 16041125541777392567808), (Int.ofNat 15572167659614871705312), (Int.ofNat 5051798100206166339648), (Int.negSucc 708662212687308166847), (Int.ofNat 30383147113982986752)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1753647248718426499776), (Int.ofNat 13270772068142994653856), (Int.negSucc 64317527132231934232607), (Int.negSucc 241588740718287477017087), (Int.ofNat 185653763205266879670144), (Int.ofNat 128044772004436897951200), (Int.ofNat 32273211849899441868768), (Int.negSucc 30638536138875627546047), (Int.negSucc 15227408037004828213247), (Int.ofNat 1438272460549481171136), (Int.negSucc 89033374926581688959), (Int.ofNat 3377981141816540160)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3243679761965328034495), (Int.negSucc 21687791035798695618863), (Int.ofNat 128483514602939362727104), (Int.ofNat 376916573450328385159936), (Int.negSucc 180034809241539430653311), (Int.negSucc 180021827839908281897855), (Int.negSucc 153897565733383828349503), (Int.ofNat 44364650809727429761728), (Int.ofNat 21290543132359245069376), (Int.ofNat 2542145611124988042608), (Int.negSucc 382701890787008168063), (Int.ofNat 9846523274523029248), (Int.negSucc 17598899869337599)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4578041784198948216576), (Int.ofNat 26239559288735216748432), (Int.negSucc 193490147016451835067807), (Int.negSucc 439558036070013699441599), (Int.negSucc 40655977847068117262271), (Int.ofNat 253255863679089296187584), (Int.ofNat 256068005992301121696032), (Int.negSucc 3063086783891987154591), (Int.negSucc 18853769352943181611231), (Int.negSucc 12412844949342483392751), (Int.ofNat 1240777635724054413856), (Int.negSucc 50476830609316680191), (Int.ofNat 603485894307450880)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 4996167569064026207711), (Int.negSucc 23640495654107978353807), (Int.ofNat 222744796024877762672672), (Int.ofNat 410787041530265229828992), (Int.ofNat 396599977424318059169792), (Int.negSucc 277611030594714706512063), (Int.negSucc 231438931565667078041727), (Int.negSucc 123820878985186255136351), (Int.ofNat 17091541845711263638048), (Int.ofNat 15139587543190565963632), (Int.ofNat 404297193999427886816), (Int.negSucc 92248837228360761599), (Int.ofNat 2466480208769310720)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4219917436239048164000), (Int.ofNat 15603558811245777807664), (Int.negSucc 197277831889104416005999), (Int.negSucc 343459013142161739790303), (Int.negSucc 623428588506931378597791), (Int.ofNat 109915764518033353291680), (Int.ofNat 133892522377341701278176), (Int.ofNat 223863714576972288509472), (Int.ofNat 526008529555466701312), (Int.negSucc 4283468947071512106863), (Int.negSucc 4664607747843337861263), (Int.ofNat 298745486932717548096), (Int.negSucc 4126706059406726655)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2725433569164947706175), (Int.negSucc 7063456698407220590207), (Int.ofNat 134629693022058780283136), (Int.ofNat 282349231217979879711984), (Int.ofNat 574068270546006084723008), (Int.ofNat 214398472277294601173920), (Int.negSucc 66252129637973444030207), (Int.negSucc 167476087267171015222591), (Int.negSucc 53965688246182779238527), (Int.negSucc 4470077955196150013823), (Int.ofNat 4818570764034343072832), (Int.ofNat 131366031539700782544), (Int.negSucc 18256899122559945087)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1303144539619406074368), (Int.ofNat 1607287095078838302880), (Int.negSucc 70807270141200676412655), (Int.negSucc 221314438666169323973055), (Int.negSucc 369560902241011643897087), (Int.negSucc 433912847166034234898527), (Int.negSucc 3834092881033943912479), (Int.ofNat 27149422996283132575392), (Int.ofNat 89767003536379371116576), (Int.ofNat 6718555531535186562080), (Int.ofNat 454241615852607518896), (Int.negSucc 786244428729400645631), (Int.ofNat 12393553323608162688)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 425064940218125077311), (Int.ofNat 485326702434271864576), (Int.ofNat 28956236216124516667744), (Int.ofNat 147514134450085100692080), (Int.ofNat 196360088123376815434752), (Int.ofNat 394116030866375885991904), (Int.ofNat 112851251777224395541184), (Int.ofNat 47305749242376002147904), (Int.negSucc 53161114826837582131519), (Int.negSucc 13036355729650806640255), (Int.negSucc 3419370697633872656863), (Int.ofNat 442242624550783826672), (Int.ofNat 40508617013453678976)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 69142615385440778368), (Int.negSucc 722269805372313506303), (Int.negSucc 9655142796993055250559), (Int.negSucc 76405017032634518252287), (Int.negSucc 106877607827892605808159), (Int.negSucc 217774491056228541621887), (Int.negSucc 176242049993311397268799), (Int.negSucc 50598327853190446539839), (Int.negSucc 7869626013562566888959), (Int.ofNat 15354154792607446543424), (Int.ofNat 2308003470691211582016), (Int.ofNat 364546345974682490208), (Int.negSucc 32411217771618403391)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 11564307333700419648), (Int.ofNat 432586488518970332752), (Int.ofNat 3009993893944978278848), (Int.ofNat 29281395259320845049824), (Int.ofNat 60603927735861315857728), (Int.ofNat 81887920450416912656928), (Int.ofNat 139187027550187594556736), (Int.ofNat 46059472029872635879584), (Int.ofNat 28973457501023292422400), (Int.negSucc 5147295495881456293631), (Int.negSucc 1227744324774712242431), (Int.negSucc 468049166080075591775), (Int.negSucc 25438568499485421695)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 10707505845612199039), (Int.negSucc 179822854092891201967), (Int.negSucc 1028674243240157592575), (Int.negSucc 8117683559733689779135), (Int.negSucc 29056467351153536331007), (Int.negSucc 26988038154699780117855), (Int.negSucc 63945005275207371947903), (Int.negSucc 40690316601808793609183), (Int.negSucc 19310662596603843609119), (Int.negSucc 4723107063790652878751), (Int.ofNat 544772091601490492448), (Int.ofNat 145648684105418105856), (Int.ofNat 30541658555504649600)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3181919231162372896), (Int.ofNat 55942390784554557936), (Int.ofNat 361292368688959393248), (Int.ofNat 1676813649110509167584), (Int.ofNat 10041087830585280073728), (Int.ofNat 11205614471385927690144), (Int.ofNat 17417897431296705579456), (Int.ofNat 24504133429008472326912), (Int.ofNat 9333693920090965894848), (Int.ofNat 5412026675022078538080), (Int.ofNat 350529870054163579776), (Int.ofNat 31831398449534842560), (Int.negSucc 1768705368076712447)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 515437297858971359), (Int.negSucc 12850802574532422479), (Int.negSucc 106316722728643255919), (Int.negSucc 314892613191195144287), (Int.negSucc 2298627745089807311711), (Int.negSucc 4794286829166295883135), (Int.negSucc 3112250648518492596863), (Int.negSucc 8664234135161043099167), (Int.negSucc 4667313520487364425567), (Int.negSucc 2466360286649648636543), (Int.negSucc 622054017628125192575), (Int.negSucc 63333697323858970751), (Int.negSucc 7492248595105839359)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 44068431426293952), (Int.ofNat 2055692577688411104), (Int.ofNat 22952533415321132928), (Int.ofNat 71674173899250436656), (Int.ofNat 324934729462415755008), (Int.ofNat 1449277071662702454912), (Int.ofNat 770114682611230831488), (Int.ofNat 1595060533102454320608), (Int.ofNat 1903165626636595003392), (Int.ofNat 753102411836308748352), (Int.ofNat 334663770073303749888), (Int.ofNat 45565828277375871360), (Int.ofNat 3155669387130926592)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1467940469973119), (Int.negSucc 204243510152528927), (Int.negSucc 3365493685553408975), (Int.negSucc 16227619980834531167), (Int.negSucc 28929926615029033247), (Int.negSucc 260743847415521952095), (Int.negSucc 308899898675253755423), (Int.negSucc 100504576043833494527), (Int.negSucc 460795935362104969343), (Int.negSucc 210316446534219093503), (Int.negSucc 94612233609190834559), (Int.negSucc 17614417446781406207), (Int.negSucc 462334907409412607)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 9518181177340800), (Int.ofNat 304686509161100832), (Int.ofNat 2505382842586306320), (Int.ofNat 3460074705348812352), (Int.ofNat 22733377014684237984), (Int.ofNat 81680652773894678400), (Int.negSucc 256224903346676159), (Int.ofNat 48387589681446434304), (Int.ofNat 48080074248731112192), (Int.ofNat 17660988453016194048), (Int.ofNat 3252293101082944512), (Int.ofNat 22333850350903296)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 13265778671910143), (Int.negSucc 208776217572411839), (Int.negSucc 695173453783948511), (Int.negSucc 237963452525898623), (Int.negSucc 10701965667301156223), (Int.negSucc 4389932432857749119), (Int.ofNat 1692125565292173312), (Int.negSucc 6160255985397206015), (Int.negSucc 2505334693487099903), (Int.negSucc 217050030234648575)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 6587274048330240), (Int.ofNat 69486010356827520), (Int.negSucc 26500755876238655), (Int.ofNat 422990615099720448), (Int.ofNat 1305721429581965184), (Int.negSucc 849693562852428287), (Int.ofNat 284545922493570048), (Int.ofNat 194716179883745280)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1060923863356415), (Int.negSucc 9072797191269119), (Int.ofNat 26657742529977984), (Int.negSucc 113241110668738559), (Int.ofNat 62899118940418560)]]

theorem h2n100_arithmetic_row0 :
    (BiPoly.mul h2p99 h2p45).getD 0 []=h2p100.getD 0 [] := by
  decide +kernel

theorem h2n100_arithmetic_row1 :
    (BiPoly.mul h2p99 h2p45).getD 1 []=h2p100.getD 1 [] := by
  decide +kernel

theorem h2n100_arithmetic_row2 :
    (BiPoly.mul h2p99 h2p45).getD 2 []=h2p100.getD 2 [] := by
  decide +kernel

theorem h2n100_arithmetic_row3 :
    (BiPoly.mul h2p99 h2p45).getD 3 []=h2p100.getD 3 [] := by
  decide +kernel

theorem h2n100_arithmetic_row4 :
    (BiPoly.mul h2p99 h2p45).getD 4 []=h2p100.getD 4 [] := by
  decide +kernel

theorem h2n100_arithmetic_row5 :
    (BiPoly.mul h2p99 h2p45).getD 5 []=h2p100.getD 5 [] := by
  decide +kernel

theorem h2n100_arithmetic_row6 :
    (BiPoly.mul h2p99 h2p45).getD 6 []=h2p100.getD 6 [] := by
  decide +kernel

theorem h2n100_arithmetic_row7 :
    (BiPoly.mul h2p99 h2p45).getD 7 []=h2p100.getD 7 [] := by
  decide +kernel

theorem h2n100_arithmetic_row8 :
    (BiPoly.mul h2p99 h2p45).getD 8 []=h2p100.getD 8 [] := by
  decide +kernel

theorem h2n100_arithmetic_row9 :
    (BiPoly.mul h2p99 h2p45).getD 9 []=h2p100.getD 9 [] := by
  decide +kernel

theorem h2n100_arithmetic_row10 :
    (BiPoly.mul h2p99 h2p45).getD 10 []=h2p100.getD 10 [] := by
  decide +kernel

theorem h2n100_arithmetic_row11 :
    (BiPoly.mul h2p99 h2p45).getD 11 []=h2p100.getD 11 [] := by
  decide +kernel

theorem h2n100_arithmetic_row12 :
    (BiPoly.mul h2p99 h2p45).getD 12 []=h2p100.getD 12 [] := by
  decide +kernel

theorem h2n100_arithmetic_row13 :
    (BiPoly.mul h2p99 h2p45).getD 13 []=h2p100.getD 13 [] := by
  decide +kernel

theorem h2n100_arithmetic_row14 :
    (BiPoly.mul h2p99 h2p45).getD 14 []=h2p100.getD 14 [] := by
  decide +kernel

theorem h2n100_arithmetic_row15 :
    (BiPoly.mul h2p99 h2p45).getD 15 []=h2p100.getD 15 [] := by
  decide +kernel

theorem h2n100_arithmetic_row16 :
    (BiPoly.mul h2p99 h2p45).getD 16 []=h2p100.getD 16 [] := by
  decide +kernel

theorem h2n100_arithmetic_row17 :
    (BiPoly.mul h2p99 h2p45).getD 17 []=h2p100.getD 17 [] := by
  decide +kernel

theorem h2n100_arithmetic_row18 :
    (BiPoly.mul h2p99 h2p45).getD 18 []=h2p100.getD 18 [] := by
  decide +kernel

theorem h2n100_arithmetic_row19 :
    (BiPoly.mul h2p99 h2p45).getD 19 []=h2p100.getD 19 [] := by
  decide +kernel

theorem h2n100_arithmetic_row20 :
    (BiPoly.mul h2p99 h2p45).getD 20 []=h2p100.getD 20 [] := by
  decide +kernel

theorem h2n100_arithmetic_row21 :
    (BiPoly.mul h2p99 h2p45).getD 21 []=h2p100.getD 21 [] := by
  decide +kernel

theorem h2n100_arithmetic_row22 :
    (BiPoly.mul h2p99 h2p45).getD 22 []=h2p100.getD 22 [] := by
  decide +kernel

theorem h2n100_arithmetic : BiPoly.mul h2p99 h2p45=h2p100 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<23 at hk
    have hf : ∀ j : Fin 23, (BiPoly.mul h2p99 h2p45).getD j.val []=h2p100.getD j.val [] :=
      (fun j => Fin.cases h2n100_arithmetic_row0 (fun j => Fin.cases h2n100_arithmetic_row1 (fun j => Fin.cases h2n100_arithmetic_row2 (fun j => Fin.cases h2n100_arithmetic_row3 (fun j => Fin.cases h2n100_arithmetic_row4 (fun j => Fin.cases h2n100_arithmetic_row5 (fun j => Fin.cases h2n100_arithmetic_row6 (fun j => Fin.cases h2n100_arithmetic_row7 (fun j => Fin.cases h2n100_arithmetic_row8 (fun j => Fin.cases h2n100_arithmetic_row9 (fun j => Fin.cases h2n100_arithmetic_row10 (fun j => Fin.cases h2n100_arithmetic_row11 (fun j => Fin.cases h2n100_arithmetic_row12 (fun j => Fin.cases h2n100_arithmetic_row13 (fun j => Fin.cases h2n100_arithmetic_row14 (fun j => Fin.cases h2n100_arithmetic_row15 (fun j => Fin.cases h2n100_arithmetic_row16 (fun j => Fin.cases h2n100_arithmetic_row17 (fun j => Fin.cases h2n100_arithmetic_row18 (fun j => Fin.cases h2n100_arithmetic_row19 (fun j => Fin.cases h2n100_arithmetic_row20 (fun j => Fin.cases h2n100_arithmetic_row21 (fun j => Fin.cases h2n100_arithmetic_row22 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h2n100 : h2e100.toBi mapPolyEnv=h2p100 := by
  change BiPoly.mul (h2e99.toBi mapPolyEnv) (h2e45.toBi mapPolyEnv)=h2p100
  rw [h2n99, h2n45]
  exact h2n100_arithmetic

#print axioms h2n100_arithmetic
end StackSorting.RationalLift
