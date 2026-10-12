import BivariateRowEquality
import Horner4Base
import Horner4Node245
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p246 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 1015698126772655999), (Int.negSucc 7680376403274951359), (Int.negSucc 10203631310998042559), (Int.ofNat 27289155256878242880), (Int.ofNat 31331787475171590720), (Int.negSucc 37738414169479900799)], [(Int.ofNat 0), (Int.ofNat 9379561011903613440), (Int.ofNat 71435120068225116288), (Int.ofNat 99845271040557824064), (Int.negSucc 231928363258131993983), (Int.negSucc 268428420037389371327), (Int.ofNat 333134126805893652864), (Int.negSucc 27337371531263884799)], [(Int.ofNat 0), (Int.negSucc 40830246488778933599), (Int.negSucc 304856149930584951599), (Int.negSucc 435350519055887410367), (Int.ofNat 866546010738596979072), (Int.ofNat 1054563450800980110336), (Int.negSucc 1204453868726657293199), (Int.ofNat 125349153837823378656), (Int.negSucc 6409347622098582527)], [(Int.ofNat 0), (Int.ofNat 111011623024858500960), (Int.ofNat 790176353972441975280), (Int.ofNat 1140858203997299694912), (Int.negSucc 1767796105078148698943), (Int.negSucc 2475021076875710119583), (Int.ofNat 2135769236270394297552), (Int.negSucc 42667014198292775423), (Int.ofNat 1586296308475758528), (Int.negSucc 470834634503337983)], [(Int.ofNat 0), (Int.negSucc 209869417537618952159), (Int.negSucc 1391920920470241028943), (Int.negSucc 2053507072838650165823), (Int.ofNat 1897664049246443469792), (Int.ofNat 3808117656780881085120), (Int.negSucc 1283908497339105620975), (Int.negSucc 831173479754603948351), (Int.ofNat 81748158805150173312), (Int.negSucc 2563688864209696127), (Int.ofNat 2509429229598720)], [(Int.ofNat 0), (Int.ofNat 290082109762307882640), (Int.ofNat 1772970066320283018168), (Int.ofNat 2765802590238388888296), (Int.negSucc 361979489594119076159), (Int.negSucc 3828760777239378527039), (Int.negSucc 2080366696093785021575), (Int.ofNat 2111244800047882858632), (Int.negSucc 126559325665883691023), (Int.ofNat 3538965451415075328), (Int.negSucc 81995363542899455)], [(Int.ofNat 0), (Int.negSucc 300048061841466861999), (Int.negSucc 1703040250560587118391), (Int.negSucc 2969058417416554973679), (Int.negSucc 2016965582918193802143), (Int.ofNat 1993133721540463111248), (Int.ofNat 5133791046202704490520), (Int.negSucc 1747102360445233813871), (Int.negSucc 224156850265050110895), (Int.ofNat 20031821988201594272), (Int.negSucc 489130349083496703)], [(Int.ofNat 0), (Int.ofNat 234086211693955108560), (Int.ofNat 1274558001293150171048), (Int.ofNat 2645585057706476061976), (Int.ofNat 3403636715581376718032), (Int.ofNat 696413051800085610064), (Int.negSucc 4576543017388081515159), (Int.negSucc 852584667931589158647), (Int.ofNat 749667244470873322544), (Int.negSucc 29002726487696793855), (Int.negSucc 16193020158609151)], [(Int.ofNat 0), (Int.negSucc 137365073323750436879), (Int.negSucc 761967781606914781879), (Int.negSucc 1979789972851203574431), (Int.negSucc 3147618810307894744975), (Int.negSucc 2434137640251483863919), (Int.ofNat 1232417400513607049896), (Int.ofNat 2844621444637522238688), (Int.negSucc 545041476037770219855), (Int.negSucc 45370564494342241215), (Int.ofNat 2635320358544492608)], [(Int.ofNat 0), (Int.ofNat 59894584940662038480), (Int.ofNat 368568424835177251624), (Int.ofNat 1225437227854307259376), (Int.ofNat 2093105254826733551040), (Int.ofNat 2455704855462237429912), (Int.ofNat 1421103853459221044240), (Int.negSucc 2075199231172695810071), (Int.negSucc 332188808031124384255), (Int.ofNat 109152387694861305560), (Int.ofNat 99465830683936496)], [(Int.ofNat 0), (Int.negSucc 18956242253065589679), (Int.negSucc 143494213060504818503), (Int.negSucc 608186960514447028727), (Int.negSucc 1140707956597029561479), (Int.negSucc 1549594783895873417615), (Int.negSucc 1827245374810705344831), (Int.ofNat 136637874069405075320), (Int.ofNat 717286548727635191224), (Int.negSucc 32487629082531361887), (Int.negSucc 5824761936702854111)], [(Int.ofNat 0), (Int.ofNat 4183574188719466320), (Int.ofNat 43864609373628943592), (Int.ofNat 233198046337768277816), (Int.ofNat 539117134745020934400), (Int.ofNat 732187157490394563088), (Int.ofNat 1052620770181174824576), (Int.ofNat 752861292872314557328), (Int.negSucc 319585194305836312399), (Int.negSucc 72627138608828309487), (Int.ofNat 2536852306390869984)], [(Int.ofNat 0), (Int.negSucc 600122360322851599), (Int.negSucc 10095434034270604087), (Int.negSucc 66322486430992144591), (Int.negSucc 212493006294450373647), (Int.negSucc 299173155403048600895), (Int.negSucc 381886610366787681551), (Int.negSucc 552651705760800302911), (Int.negSucc 93850653418490651855), (Int.ofNat 62884112482641153264), (Int.ofNat 4044589489694199840)], [(Int.ofNat 0), (Int.ofNat 48792007383707680), (Int.ofNat 1644215981008551712), (Int.ofNat 13328253160233380664), (Int.ofNat 63826058333522446784), (Int.ofNat 111061100011608851000), (Int.ofNat 106302289914895878288), (Int.ofNat 189308198214620792256), (Int.ofNat 147602255955655412448), (Int.negSucc 2895559633932147359), (Int.negSucc 3405107833665202367)], [(Int.ofNat 0), (Int.negSucc 1594698014036159), (Int.negSucc 170206621679865935), (Int.negSucc 1768733942880779687), (Int.negSucc 13318240431186588359), (Int.negSucc 33738904995938365535), (Int.negSucc 29962983589596925535), (Int.negSucc 34344193571126035871), (Int.negSucc 59975696474899999007), (Int.negSucc 16882639616780245631), (Int.negSucc 127411665384650111)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 8540844143092992), (Int.ofNat 137890588178027808), (Int.ofNat 1737707625985325808), (Int.ofNat 7233387065006316048), (Int.ofNat 8574931059281707968), (Int.ofNat 3534432267551495712), (Int.ofNat 10628794762962205248), (Int.ofNat 8339988624028096320), (Int.ofNat 959996591409025152)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 4746561595295039), (Int.negSucc 116590207920274511), (Int.negSucc 953167334793541775), (Int.negSucc 1815919725551308991), (Int.negSucc 534947271148702655), (Int.negSucc 426243683464721855), (Int.negSucc 1595157630686328383), (Int.negSucc 357344378575979903)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1997419765420800), (Int.ofNat 61412062515281856), (Int.ofNat 221573279719041408), (Int.ofNat 133688134481196096), (Int.negSucc 116157095668333439), (Int.ofNat 107659232201677824), (Int.ofNat 41630582923683840)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 641888820718847), (Int.negSucc 11609879131616831), (Int.negSucc 13928244579882431), (Int.ofNat 13447916800951680)]]

theorem h4n246_arithmetic_row0 :
    (BiPoly.mul h4p13 h4p245).getD 0 []=h4p246.getD 0 [] := by
  decide +kernel

theorem h4n246_arithmetic_row1 :
    (BiPoly.mul h4p13 h4p245).getD 1 []=h4p246.getD 1 [] := by
  decide +kernel

theorem h4n246_arithmetic_row2 :
    (BiPoly.mul h4p13 h4p245).getD 2 []=h4p246.getD 2 [] := by
  decide +kernel

theorem h4n246_arithmetic_row3 :
    (BiPoly.mul h4p13 h4p245).getD 3 []=h4p246.getD 3 [] := by
  decide +kernel

theorem h4n246_arithmetic_row4 :
    (BiPoly.mul h4p13 h4p245).getD 4 []=h4p246.getD 4 [] := by
  decide +kernel

theorem h4n246_arithmetic_row5 :
    (BiPoly.mul h4p13 h4p245).getD 5 []=h4p246.getD 5 [] := by
  decide +kernel

theorem h4n246_arithmetic_row6 :
    (BiPoly.mul h4p13 h4p245).getD 6 []=h4p246.getD 6 [] := by
  decide +kernel

theorem h4n246_arithmetic_row7 :
    (BiPoly.mul h4p13 h4p245).getD 7 []=h4p246.getD 7 [] := by
  decide +kernel

theorem h4n246_arithmetic_row8 :
    (BiPoly.mul h4p13 h4p245).getD 8 []=h4p246.getD 8 [] := by
  decide +kernel

theorem h4n246_arithmetic_row9 :
    (BiPoly.mul h4p13 h4p245).getD 9 []=h4p246.getD 9 [] := by
  decide +kernel

theorem h4n246_arithmetic_row10 :
    (BiPoly.mul h4p13 h4p245).getD 10 []=h4p246.getD 10 [] := by
  decide +kernel

theorem h4n246_arithmetic_row11 :
    (BiPoly.mul h4p13 h4p245).getD 11 []=h4p246.getD 11 [] := by
  decide +kernel

theorem h4n246_arithmetic_row12 :
    (BiPoly.mul h4p13 h4p245).getD 12 []=h4p246.getD 12 [] := by
  decide +kernel

theorem h4n246_arithmetic_row13 :
    (BiPoly.mul h4p13 h4p245).getD 13 []=h4p246.getD 13 [] := by
  decide +kernel

theorem h4n246_arithmetic_row14 :
    (BiPoly.mul h4p13 h4p245).getD 14 []=h4p246.getD 14 [] := by
  decide +kernel

theorem h4n246_arithmetic_row15 :
    (BiPoly.mul h4p13 h4p245).getD 15 []=h4p246.getD 15 [] := by
  decide +kernel

theorem h4n246_arithmetic_row16 :
    (BiPoly.mul h4p13 h4p245).getD 16 []=h4p246.getD 16 [] := by
  decide +kernel

theorem h4n246_arithmetic_row17 :
    (BiPoly.mul h4p13 h4p245).getD 17 []=h4p246.getD 17 [] := by
  decide +kernel

theorem h4n246_arithmetic_row18 :
    (BiPoly.mul h4p13 h4p245).getD 18 []=h4p246.getD 18 [] := by
  decide +kernel

theorem h4n246_arithmetic : BiPoly.mul h4p13 h4p245=h4p246 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h4p13 h4p245).getD j.val []=h4p246.getD j.val [] :=
      (fun j => Fin.cases h4n246_arithmetic_row0 (fun j => Fin.cases h4n246_arithmetic_row1 (fun j => Fin.cases h4n246_arithmetic_row2 (fun j => Fin.cases h4n246_arithmetic_row3 (fun j => Fin.cases h4n246_arithmetic_row4 (fun j => Fin.cases h4n246_arithmetic_row5 (fun j => Fin.cases h4n246_arithmetic_row6 (fun j => Fin.cases h4n246_arithmetic_row7 (fun j => Fin.cases h4n246_arithmetic_row8 (fun j => Fin.cases h4n246_arithmetic_row9 (fun j => Fin.cases h4n246_arithmetic_row10 (fun j => Fin.cases h4n246_arithmetic_row11 (fun j => Fin.cases h4n246_arithmetic_row12 (fun j => Fin.cases h4n246_arithmetic_row13 (fun j => Fin.cases h4n246_arithmetic_row14 (fun j => Fin.cases h4n246_arithmetic_row15 (fun j => Fin.cases h4n246_arithmetic_row16 (fun j => Fin.cases h4n246_arithmetic_row17 (fun j => Fin.cases h4n246_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n246 : h4e246.toBi mapPolyEnv=h4p246 := by
  change BiPoly.mul (h4e13.toBi mapPolyEnv) (h4e245.toBi mapPolyEnv)=h4p246
  rw [h4n13, h4n245]
  exact h4n246_arithmetic

#print axioms h4n246_arithmetic
end StackSorting.RationalLift
