import BivariateRowEquality
import Horner0Base
import Horner0Node054
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p55 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 20567887067146284000), (Int.ofNat 134959735099171481040), (Int.ofNat 92231686015685164800), (Int.negSucc 530445231935444386079), (Int.negSucc 126183626453120358239), (Int.ofNat 382101443465983995600)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 258876620845742198159), (Int.negSucc 1675852957522145828231), (Int.negSucc 1084216503130934265863), (Int.ofNat 6304007480352166033488), (Int.ofNat 570707719554338436672), (Int.negSucc 3796187588989915516487), (Int.ofNat 198955407529494538200)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1547880101868708197640), (Int.ofNat 9755626950760812401628), (Int.ofNat 5952060354029333782212), (Int.negSucc 34205421413256989337719), (Int.ofNat 388079609765061035088), (Int.ofNat 15486391956540729389868), (Int.negSucc 214838344955253086171), (Int.negSucc 43379003592518477903)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 5843324186574199747739), (Int.negSucc 35325292288322682005669), (Int.negSucc 20777716808336067635879), (Int.ofNat 110211293430342145746666), (Int.negSucc 5461497671230778244299), (Int.negSucc 32227299877506720933185), (Int.negSucc 7482367772497904094575), (Int.ofNat 1124679125572771486590), (Int.negSucc 46040964651719870975)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 15596219753753126355720), (Int.ofNat 89149031792726563034100), (Int.ofNat 53497557476402538559536), (Int.negSucc 229387834316768855847299), (Int.negSucc 3796441019793714789791), (Int.ofNat 31632187711804184287188), (Int.ofNat 40656065029955267232456), (Int.negSucc 5024240796398074448147), (Int.ofNat 311800243144524003648), (Int.negSucc 9809357384998372607)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 31204319038288681731119), (Int.negSucc 166814221251450620052935), (Int.negSucc 111397634221534955289953), (Int.ofNat 309151420649007617863530), (Int.ofNat 90507078808737597724806), (Int.ofNat 466022494252531089828), (Int.negSucc 93352538120711983025381), (Int.ofNat 3585802322061233653842), (Int.ofNat 139441523107876734186), (Int.ofNat 5061455938407298608), (Int.negSucc 642221924656042367)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 48385319592401707827870), (Int.ofNat 240978316193877414635901), (Int.ofNat 196346149720384708632957), (Int.negSucc 233799368224216733040086), (Int.negSucc 293909410398296691738446), (Int.negSucc 42487840080126124723712), (Int.ofNat 97912441375109491940763), (Int.ofNat 28082063828400890642307), (Int.negSucc 4081454537621030153690), (Int.ofNat 212848849401491387316), (Int.negSucc 3890884676162430143), (Int.ofNat 3450465190698240)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 59276606135439599059319), (Int.negSucc 277128672034703408652065), (Int.negSucc 294326712213551224290932), (Int.negSucc 9951567923698835467949), (Int.ofNat 492093464581957563561495), (Int.ofNat 93023688509421604433424), (Int.negSucc 1850722488357013088174), (Int.negSucc 86350920970775966060423), (Int.ofNat 6929203684164784348017), (Int.negSucc 243417047687392947047), (Int.ofNat 8068702636195689336), (Int.negSucc 111959428237237151)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 57971760549978917610550), (Int.ofNat 260442893493937950494367), (Int.ofNat 369818846544039220863959), (Int.ofNat 284117115437483055112353), (Int.negSucc 453666670092457215862991), (Int.negSucc 196860915159877937407217), (Int.negSucc 117132247710506904164116), (Int.ofNat 95236830421274858247861), (Int.ofNat 8332723435759950015620), (Int.negSucc 1362086171901081622378), (Int.ofNat 54761202795729944724), (Int.negSucc 716057464357854927)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 45441449883610728982699), (Int.negSucc 204592731856069302267171), (Int.negSucc 384297474310414308030422), (Int.negSucc 431503339339789015556767), (Int.ofNat 129457318249511453362252), (Int.ofNat 313882890388051928245960), (Int.ofNat 147483541028262257276693), (Int.negSucc 3963534003209998621265), (Int.negSucc 38536885671953798443723), (Int.ofNat 2780483499760323545844), (Int.negSucc 63661763733846439537), (Int.ofNat 411921436319776880)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 28517582066119478983180), (Int.ofNat 136530554810215004867684), (Int.ofNat 328439625244919192323859), (Int.ofNat 418558487555754170069516), (Int.ofNat 235698941945974469520548), (Int.negSucc 287598759785171030335149), (Int.negSucc 114096632267682347409434), (Int.negSucc 98481011289005804447836), (Int.ofNat 40587676040971212600817), (Int.ofNat 1728975366088821605783), (Int.negSucc 263679106231157137556), (Int.ofNat 7011314127433264104)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 14244611487202926107099), (Int.negSucc 77772079939588956883281), (Int.negSucc 230876566406163783160755), (Int.negSucc 319033284572398198765588), (Int.negSucc 384997438344992161401500), (Int.ofNat 77746414023202980922973), (Int.ofNat 91932527639520849154372), (Int.ofNat 103346396777863032738671), (Int.ofNat 2524937823750357748852), (Int.negSucc 9246616484739218734654), (Int.ofNat 390404651809936599461), (Int.ofNat 525406755146723038)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5600842701933802391860), (Int.ofNat 37465884709695088131866), (Int.ofNat 133596038081609996165682), (Int.ofNat 209762959174667934542324), (Int.ofNat 312575638638359819321436), (Int.ofNat 137662888977996050312893), (Int.negSucc 62013876054765956919838), (Int.negSucc 42651716338364485601321), (Int.negSucc 39549043706521249950459), (Int.ofNat 7557852722185950105573), (Int.ofNat 408808715391096824348), (Int.negSucc 26772839293185639376)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1703090518726604683159), (Int.negSucc 14939244197545310228127), (Int.negSucc 63445985011134708433599), (Int.negSucc 122539102085568111896441), (Int.negSucc 175092944113425686453965), (Int.negSucc 197699618494458659397136), (Int.negSucc 3594261696450433265903), (Int.ofNat 2158751531005483753358), (Int.ofNat 31706004974373936993026), (Int.ofNat 2788454646415342596079), (Int.negSucc 1063217646768538881176), (Int.ofNat 3923975175807310968)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 389757113626835064630), (Int.ofNat 4787374695118846633277), (Int.ofNat 24486314712533725383239), (Int.ofNat 61914799128477912255613), (Int.ofNat 79812407104335740257907), (Int.ofNat 133318879239642424441732), (Int.ofNat 56668849589290724545234), (Int.ofNat 7648247447967273129916), (Int.negSucc 5721519737748809317751), (Int.negSucc 7754150736398626545262), (Int.ofNat 353141472804133979950), (Int.ofNat 47967404752603935756)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 64335953993903470159), (Int.negSucc 1190055722395840908477), (Int.negSucc 7541266118604321459116), (Int.negSucc 25690119157397393197163), (Int.negSucc 34567280374392902321208), (Int.negSucc 56507514019970035595020), (Int.negSucc 57499750536735296083622), (Int.negSucc 11982435092187536766932), (Int.negSucc 5898108445042421743154), (Int.ofNat 3869522597509335037374), (Int.ofNat 617510754878344975590), (Int.negSucc 28046018917585875317)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7137104772154172590), (Int.ofNat 219534831020791434563), (Int.ofNat 1803449785064359930871), (Int.ofNat 8326371867671989830709), (Int.ofNat 14601462962315309026290), (Int.ofNat 17307077007996991429221), (Int.ofNat 30192943689738827576016), (Int.ofNat 13445014771728984353919), (Int.ofNat 5091335549703192861966), (Int.ofNat 477109860671575492440), (Int.negSucc 579028952637351125147), (Int.negSucc 27203028507305714771)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 466003760854952379), (Int.negSucc 28192645125772011627), (Int.negSucc 322089373531900115822), (Int.negSucc 2016510551367261935695), (Int.negSucc 5283065554423989835021), (Int.negSucc 4985190986658331880960), (Int.negSucc 9380529821477366283602), (Int.negSucc 8833658576570881345367), (Int.negSucc 2815883857707946990001), (Int.negSucc 1288438055261576018537), (Int.ofNat 74619997902526675188), (Int.ofNat 30091735658525248116)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 12956921364043800), (Int.ofNat 2250024924939942726), (Int.ofNat 40476278206158283389), (Int.ofNat 347863023378015231750), (Int.ofNat 1433117907101464505400), (Int.ofNat 1677761105918461947879), (Int.ofNat 1802704441638906478422), (Int.ofNat 3329962861965495999420), (Int.ofNat 1508625579515237992464), (Int.ofNat 648782347511236319388), (Int.ofNat 126156890182948603380), (Int.negSucc 3114287782734372623)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 84344652544219559), (Int.negSucc 3211141100051258513), (Int.negSucc 39949393481065794098), (Int.negSucc 266340670127402085260), (Int.negSucc 522423121011397776737), (Int.negSucc 289275298458355375853), (Int.negSucc 690524491665961492361), (Int.negSucc 615400514719247516759), (Int.negSucc 216283076530295085287), (Int.negSucc 79210878581850313895), (Int.negSucc 7037741904131964023)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 122224297334850360), (Int.ofNat 2704407692770433178), (Int.ofNat 30897467041243528674), (Int.ofNat 113124797549350891200), (Int.ofNat 77210161706823888348), (Int.ofNat 64174678283449849860), (Int.ofNat 149392682202036832056), (Int.ofNat 63495698931636182640), (Int.ofNat 23032700979808275504), (Int.ofNat 3639084419852661312)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 79944949871894231), (Int.negSucc 1877749980955764317), (Int.negSucc 14568432409512889901), (Int.negSucc 21335080151191021307), (Int.negSucc 833215618085252939), (Int.negSucc 17114173189391097071), (Int.negSucc 14228448427797432191), (Int.negSucc 4411172906196698879), (Int.negSucc 698630329229224751)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 34620920558574480), (Int.ofNat 900493607739542148), (Int.ofNat 3367056817493312868), (Int.ofNat 548819307877670640), (Int.negSucc 16724727013682591), (Int.ofNat 1773878444747592912), (Int.ofNat 624603608001344304), (Int.ofNat 46834405789144320)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 10511902166435999), (Int.negSucc 229847286109733063), (Int.negSucc 240526124721093239), (Int.ofNat 196636471342984800), (Int.negSucc 82570526931244751), (Int.negSucc 46834405789144319)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1444249846617408), (Int.ofNat 23233728352903056), (Int.negSucc 15128906401070639)]]

theorem h0n55_arithmetic_row0 :
    (BiPoly.mul h0p4 h0p54).getD 0 []=h0p55.getD 0 [] := by
  decide +kernel

theorem h0n55_arithmetic_row1 :
    (BiPoly.mul h0p4 h0p54).getD 1 []=h0p55.getD 1 [] := by
  decide +kernel

theorem h0n55_arithmetic_row2 :
    (BiPoly.mul h0p4 h0p54).getD 2 []=h0p55.getD 2 [] := by
  decide +kernel

theorem h0n55_arithmetic_row3 :
    (BiPoly.mul h0p4 h0p54).getD 3 []=h0p55.getD 3 [] := by
  decide +kernel

theorem h0n55_arithmetic_row4 :
    (BiPoly.mul h0p4 h0p54).getD 4 []=h0p55.getD 4 [] := by
  decide +kernel

theorem h0n55_arithmetic_row5 :
    (BiPoly.mul h0p4 h0p54).getD 5 []=h0p55.getD 5 [] := by
  decide +kernel

theorem h0n55_arithmetic_row6 :
    (BiPoly.mul h0p4 h0p54).getD 6 []=h0p55.getD 6 [] := by
  decide +kernel

theorem h0n55_arithmetic_row7 :
    (BiPoly.mul h0p4 h0p54).getD 7 []=h0p55.getD 7 [] := by
  decide +kernel

theorem h0n55_arithmetic_row8 :
    (BiPoly.mul h0p4 h0p54).getD 8 []=h0p55.getD 8 [] := by
  decide +kernel

theorem h0n55_arithmetic_row9 :
    (BiPoly.mul h0p4 h0p54).getD 9 []=h0p55.getD 9 [] := by
  decide +kernel

theorem h0n55_arithmetic_row10 :
    (BiPoly.mul h0p4 h0p54).getD 10 []=h0p55.getD 10 [] := by
  decide +kernel

theorem h0n55_arithmetic_row11 :
    (BiPoly.mul h0p4 h0p54).getD 11 []=h0p55.getD 11 [] := by
  decide +kernel

theorem h0n55_arithmetic_row12 :
    (BiPoly.mul h0p4 h0p54).getD 12 []=h0p55.getD 12 [] := by
  decide +kernel

theorem h0n55_arithmetic_row13 :
    (BiPoly.mul h0p4 h0p54).getD 13 []=h0p55.getD 13 [] := by
  decide +kernel

theorem h0n55_arithmetic_row14 :
    (BiPoly.mul h0p4 h0p54).getD 14 []=h0p55.getD 14 [] := by
  decide +kernel

theorem h0n55_arithmetic_row15 :
    (BiPoly.mul h0p4 h0p54).getD 15 []=h0p55.getD 15 [] := by
  decide +kernel

theorem h0n55_arithmetic_row16 :
    (BiPoly.mul h0p4 h0p54).getD 16 []=h0p55.getD 16 [] := by
  decide +kernel

theorem h0n55_arithmetic_row17 :
    (BiPoly.mul h0p4 h0p54).getD 17 []=h0p55.getD 17 [] := by
  decide +kernel

theorem h0n55_arithmetic_row18 :
    (BiPoly.mul h0p4 h0p54).getD 18 []=h0p55.getD 18 [] := by
  decide +kernel

theorem h0n55_arithmetic_row19 :
    (BiPoly.mul h0p4 h0p54).getD 19 []=h0p55.getD 19 [] := by
  decide +kernel

theorem h0n55_arithmetic_row20 :
    (BiPoly.mul h0p4 h0p54).getD 20 []=h0p55.getD 20 [] := by
  decide +kernel

theorem h0n55_arithmetic_row21 :
    (BiPoly.mul h0p4 h0p54).getD 21 []=h0p55.getD 21 [] := by
  decide +kernel

theorem h0n55_arithmetic_row22 :
    (BiPoly.mul h0p4 h0p54).getD 22 []=h0p55.getD 22 [] := by
  decide +kernel

theorem h0n55_arithmetic_row23 :
    (BiPoly.mul h0p4 h0p54).getD 23 []=h0p55.getD 23 [] := by
  decide +kernel

theorem h0n55_arithmetic_row24 :
    (BiPoly.mul h0p4 h0p54).getD 24 []=h0p55.getD 24 [] := by
  decide +kernel

theorem h0n55_arithmetic : BiPoly.mul h0p4 h0p54=h0p55 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<25 at hk
    have hf : ∀ j : Fin 25, (BiPoly.mul h0p4 h0p54).getD j.val []=h0p55.getD j.val [] :=
      (fun j => Fin.cases h0n55_arithmetic_row0 (fun j => Fin.cases h0n55_arithmetic_row1 (fun j => Fin.cases h0n55_arithmetic_row2 (fun j => Fin.cases h0n55_arithmetic_row3 (fun j => Fin.cases h0n55_arithmetic_row4 (fun j => Fin.cases h0n55_arithmetic_row5 (fun j => Fin.cases h0n55_arithmetic_row6 (fun j => Fin.cases h0n55_arithmetic_row7 (fun j => Fin.cases h0n55_arithmetic_row8 (fun j => Fin.cases h0n55_arithmetic_row9 (fun j => Fin.cases h0n55_arithmetic_row10 (fun j => Fin.cases h0n55_arithmetic_row11 (fun j => Fin.cases h0n55_arithmetic_row12 (fun j => Fin.cases h0n55_arithmetic_row13 (fun j => Fin.cases h0n55_arithmetic_row14 (fun j => Fin.cases h0n55_arithmetic_row15 (fun j => Fin.cases h0n55_arithmetic_row16 (fun j => Fin.cases h0n55_arithmetic_row17 (fun j => Fin.cases h0n55_arithmetic_row18 (fun j => Fin.cases h0n55_arithmetic_row19 (fun j => Fin.cases h0n55_arithmetic_row20 (fun j => Fin.cases h0n55_arithmetic_row21 (fun j => Fin.cases h0n55_arithmetic_row22 (fun j => Fin.cases h0n55_arithmetic_row23 (fun j => Fin.cases h0n55_arithmetic_row24 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n55 : h0e55.toBi mapPolyEnv=h0p55 := by
  change BiPoly.mul (h0e4.toBi mapPolyEnv) (h0e54.toBi mapPolyEnv)=h0p55
  rw [h0n4, h0n54]
  exact h0n55_arithmetic

#print axioms h0n55_arithmetic
end StackSorting.RationalLift
