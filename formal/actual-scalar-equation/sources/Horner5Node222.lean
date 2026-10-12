import BivariateRowEquality
import Horner5Base
import Horner5Node221
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p222 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 6271476191999), (Int.negSucc 31261277531519), (Int.negSucc 33794281226879), (Int.negSucc 23784332538239), (Int.ofNat 29933742637440), (Int.ofNat 44913595288320)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 54580425022080), (Int.ofNat 248742115240896), (Int.ofNat 203708339928576), (Int.ofNat 140953563116928), (Int.negSucc 246547527155711), (Int.negSucc 240180545618495), (Int.ofNat 11086585064064)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 213717713924159), (Int.negSucc 901976703105311), (Int.negSucc 588510441051839), (Int.negSucc 515786713391807), (Int.ofNat 761287647183552), (Int.ofNat 529943562375264), (Int.ofNat 84790173622464), (Int.negSucc 8072510886143)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 496630414067040), (Int.ofNat 1984151871161424), (Int.ofNat 1229784957378000), (Int.ofNat 1404153656329536), (Int.negSucc 1155142952004095), (Int.negSucc 750026140459055), (Int.negSucc 548008789365935), (Int.ofNat 67209796389024), (Int.negSucc 3185799040511)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 760397562014399), (Int.negSucc 2974376048003135), (Int.negSucc 2266935885216719), (Int.negSucc 2675051880544223), (Int.ofNat 564525349341408), (Int.ofNat 928055905764480), (Int.ofNat 1050634703401776), (Int.negSucc 32469278555231), (Int.ofNat 2719596898944), (Int.negSucc 291831800831)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 804857051802240), (Int.ofNat 3230060177197440), (Int.ofNat 3591896219833104), (Int.ofNat 3582516250866240), (Int.ofNat 1325694940822080), (Int.negSucc 917449250166431), (Int.negSucc 869611280003855), (Int.negSucc 379077161795423), (Int.ofNat 42992681712192), (Int.negSucc 1119954625919)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 600512523122879), (Int.negSucc 2623227522941663), (Int.negSucc 4409927088508799), (Int.negSucc 3717546646676687), (Int.negSucc 3387014107820351), (Int.ofNat 215893054837152), (Int.ofNat 227714349424608), (Int.ofNat 724421097754416), (Int.negSucc 43289465517215), (Int.ofNat 2188075466880)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 315622367559360), (Int.ofNat 1607610645256032), (Int.ofNat 3958744434006384), (Int.ofNat 3425429013289344), (Int.ofNat 3967772941597680), (Int.ofNat 1131963843083184), (Int.ofNat 172654455439008), (Int.negSucc 392412902997311), (Int.negSucc 125069018632847), (Int.ofNat 8831937309984)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 114463253643839), (Int.negSucc 734032474589663), (Int.negSucc 2538850762017215), (Int.negSucc 2888626553788175), (Int.negSucc 2971216970198783), (Int.negSucc 2079273381740639), (Int.negSucc 362510233028783), (Int.negSucc 139278566104847), (Int.ofNat 205263205123104), (Int.negSucc 7628531160383)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 27271984032000), (Int.ofNat 241005628161216), (Int.ofNat 1140975384742224), (Int.ofNat 1989827587922688), (Int.ofNat 1696024621910016), (Int.ofNat 1848560314638528), (Int.ofNat 565006991765184), (Int.ofNat 266673672240768), (Int.negSucc 48891526972127), (Int.negSucc 18442965532607)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3842337795839), (Int.negSucc 53337765680639), (Int.negSucc 347086477209599), (Int.negSucc 987475089272399), (Int.negSucc 893240840129759), (Int.negSucc 981038858579999), (Int.negSucc 584023177416959), (Int.negSucc 171537558229151), (Int.negSucc 72082597946975), (Int.ofNat 18241798933440)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 242624210400), (Int.ofNat 7059853577808), (Int.ofNat 66769480663488), (Int.ofNat 321866420023872), (Int.ofNat 433340882661168), (Int.ofNat 351279840108960), (Int.ofNat 350577930717504), (Int.ofNat 108496007915904), (Int.ofNat 54100181664000), (Int.ofNat 2528664628608)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 418498742879), (Int.negSucc 7060180175279), (Int.negSucc 62152081043471), (Int.negSucc 155160305280287), (Int.negSucc 111513070579967), (Int.negSucc 118434764672063), (Int.negSucc 63073462406399), (Int.negSucc 17865003973247), (Int.negSucc 6892927020287)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 286298854560), (Int.ofNat 5803946346816), (Int.ofNat 32817524197536), (Int.ofNat 36500718802752), (Int.ofNat 23193080687232), (Int.ofNat 21953914880256), (Int.ofNat 5556991547520), (Int.ofNat 2157489706752)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 127140640415), (Int.negSucc 3114905639903), (Int.negSucc 8493684929855), (Int.negSucc 3915983314943), (Int.negSucc 3629094067583), (Int.negSucc 1570487025023), (Int.negSucc 188939070719)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 39957878016), (Int.ofNat 864587654784), (Int.ofNat 838130467968), (Int.ofNat 200243446272), (Int.ofNat 188939070720)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 5652187775), (Int.negSucc 94469535359)]]

theorem h5n222_arithmetic_row0 :
    (BiPoly.mul h5p5 h5p221).getD 0 []=h5p222.getD 0 [] := by
  decide +kernel

theorem h5n222_arithmetic_row1 :
    (BiPoly.mul h5p5 h5p221).getD 1 []=h5p222.getD 1 [] := by
  decide +kernel

theorem h5n222_arithmetic_row2 :
    (BiPoly.mul h5p5 h5p221).getD 2 []=h5p222.getD 2 [] := by
  decide +kernel

theorem h5n222_arithmetic_row3 :
    (BiPoly.mul h5p5 h5p221).getD 3 []=h5p222.getD 3 [] := by
  decide +kernel

theorem h5n222_arithmetic_row4 :
    (BiPoly.mul h5p5 h5p221).getD 4 []=h5p222.getD 4 [] := by
  decide +kernel

theorem h5n222_arithmetic_row5 :
    (BiPoly.mul h5p5 h5p221).getD 5 []=h5p222.getD 5 [] := by
  decide +kernel

theorem h5n222_arithmetic_row6 :
    (BiPoly.mul h5p5 h5p221).getD 6 []=h5p222.getD 6 [] := by
  decide +kernel

theorem h5n222_arithmetic_row7 :
    (BiPoly.mul h5p5 h5p221).getD 7 []=h5p222.getD 7 [] := by
  decide +kernel

theorem h5n222_arithmetic_row8 :
    (BiPoly.mul h5p5 h5p221).getD 8 []=h5p222.getD 8 [] := by
  decide +kernel

theorem h5n222_arithmetic_row9 :
    (BiPoly.mul h5p5 h5p221).getD 9 []=h5p222.getD 9 [] := by
  decide +kernel

theorem h5n222_arithmetic_row10 :
    (BiPoly.mul h5p5 h5p221).getD 10 []=h5p222.getD 10 [] := by
  decide +kernel

theorem h5n222_arithmetic_row11 :
    (BiPoly.mul h5p5 h5p221).getD 11 []=h5p222.getD 11 [] := by
  decide +kernel

theorem h5n222_arithmetic_row12 :
    (BiPoly.mul h5p5 h5p221).getD 12 []=h5p222.getD 12 [] := by
  decide +kernel

theorem h5n222_arithmetic_row13 :
    (BiPoly.mul h5p5 h5p221).getD 13 []=h5p222.getD 13 [] := by
  decide +kernel

theorem h5n222_arithmetic_row14 :
    (BiPoly.mul h5p5 h5p221).getD 14 []=h5p222.getD 14 [] := by
  decide +kernel

theorem h5n222_arithmetic_row15 :
    (BiPoly.mul h5p5 h5p221).getD 15 []=h5p222.getD 15 [] := by
  decide +kernel

theorem h5n222_arithmetic_row16 :
    (BiPoly.mul h5p5 h5p221).getD 16 []=h5p222.getD 16 [] := by
  decide +kernel

theorem h5n222_arithmetic : BiPoly.mul h5p5 h5p221=h5p222 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p5 h5p221).getD j.val []=h5p222.getD j.val [] :=
      (fun j => Fin.cases h5n222_arithmetic_row0 (fun j => Fin.cases h5n222_arithmetic_row1 (fun j => Fin.cases h5n222_arithmetic_row2 (fun j => Fin.cases h5n222_arithmetic_row3 (fun j => Fin.cases h5n222_arithmetic_row4 (fun j => Fin.cases h5n222_arithmetic_row5 (fun j => Fin.cases h5n222_arithmetic_row6 (fun j => Fin.cases h5n222_arithmetic_row7 (fun j => Fin.cases h5n222_arithmetic_row8 (fun j => Fin.cases h5n222_arithmetic_row9 (fun j => Fin.cases h5n222_arithmetic_row10 (fun j => Fin.cases h5n222_arithmetic_row11 (fun j => Fin.cases h5n222_arithmetic_row12 (fun j => Fin.cases h5n222_arithmetic_row13 (fun j => Fin.cases h5n222_arithmetic_row14 (fun j => Fin.cases h5n222_arithmetic_row15 (fun j => Fin.cases h5n222_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n222 : h5e222.toBi mapPolyEnv=h5p222 := by
  change BiPoly.mul (h5e5.toBi mapPolyEnv) (h5e221.toBi mapPolyEnv)=h5p222
  rw [h5n5, h5n221]
  exact h5n222_arithmetic

#print axioms h5n222_arithmetic
end StackSorting.RationalLift
