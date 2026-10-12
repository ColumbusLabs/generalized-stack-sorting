import BivariateRowEquality
import Horner5Base
import Horner5Node238
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p239 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 6271476192000), (Int.ofNat 31261277531520), (Int.ofNat 33794281226880), (Int.ofNat 23784332538240), (Int.negSucc 29933742637439), (Int.negSucc 44913595288319)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 54580425022079), (Int.negSucc 248742115240895), (Int.negSucc 203708339928575), (Int.negSucc 140953563116927), (Int.ofNat 246547527155712), (Int.ofNat 240180545618496), (Int.negSucc 11086585064063)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 213717713924160), (Int.ofNat 901976703105312), (Int.ofNat 588510441051840), (Int.ofNat 515786713391808), (Int.negSucc 761287647183551), (Int.negSucc 529943562375263), (Int.negSucc 84790173622463), (Int.ofNat 8072510886144)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 496630414067039), (Int.negSucc 1984151871161423), (Int.negSucc 1229784957377999), (Int.negSucc 1404153656329535), (Int.ofNat 1155142952004096), (Int.ofNat 750026140459056), (Int.ofNat 548008789365936), (Int.negSucc 67209796389023), (Int.ofNat 3185799040512)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 760397562014400), (Int.ofNat 2974376048003136), (Int.ofNat 2266935885216720), (Int.ofNat 2675051880544224), (Int.negSucc 564525349341407), (Int.negSucc 928055905764479), (Int.negSucc 1050634703401775), (Int.ofNat 32469278555232), (Int.negSucc 2719596898943), (Int.ofNat 291831800832)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 804857051802239), (Int.negSucc 3230060177197439), (Int.negSucc 3591896219833103), (Int.negSucc 3582516250866239), (Int.negSucc 1325694940822079), (Int.ofNat 917449250166432), (Int.ofNat 869611280003856), (Int.ofNat 379077161795424), (Int.negSucc 42992681712191), (Int.ofNat 1119954625920)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 600512523122880), (Int.ofNat 2623227522941664), (Int.ofNat 4409927088508800), (Int.ofNat 3717546646676688), (Int.ofNat 3387014107820352), (Int.negSucc 215893054837151), (Int.negSucc 227714349424607), (Int.negSucc 724421097754415), (Int.ofNat 43289465517216), (Int.negSucc 2188075466879)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 315622367559359), (Int.negSucc 1607610645256031), (Int.negSucc 3958744434006383), (Int.negSucc 3425429013289343), (Int.negSucc 3967772941597679), (Int.negSucc 1131963843083183), (Int.negSucc 172654455439007), (Int.ofNat 392412902997312), (Int.ofNat 125069018632848), (Int.negSucc 8831937309983)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 114463253643840), (Int.ofNat 734032474589664), (Int.ofNat 2538850762017216), (Int.ofNat 2888626553788176), (Int.ofNat 2971216970198784), (Int.ofNat 2079273381740640), (Int.ofNat 362510233028784), (Int.ofNat 139278566104848), (Int.negSucc 205263205123103), (Int.ofNat 7628531160384)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 27271984031999), (Int.negSucc 241005628161215), (Int.negSucc 1140975384742223), (Int.negSucc 1989827587922687), (Int.negSucc 1696024621910015), (Int.negSucc 1848560314638527), (Int.negSucc 565006991765183), (Int.negSucc 266673672240767), (Int.ofNat 48891526972128), (Int.ofNat 18442965532608)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3842337795840), (Int.ofNat 53337765680640), (Int.ofNat 347086477209600), (Int.ofNat 987475089272400), (Int.ofNat 893240840129760), (Int.ofNat 981038858580000), (Int.ofNat 584023177416960), (Int.ofNat 171537558229152), (Int.ofNat 72082597946976), (Int.negSucc 18241798933439)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 242624210399), (Int.negSucc 7059853577807), (Int.negSucc 66769480663487), (Int.negSucc 321866420023871), (Int.negSucc 433340882661167), (Int.negSucc 351279840108959), (Int.negSucc 350577930717503), (Int.negSucc 108496007915903), (Int.negSucc 54100181663999), (Int.negSucc 2528664628607)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 418498742880), (Int.ofNat 7060180175280), (Int.ofNat 62152081043472), (Int.ofNat 155160305280288), (Int.ofNat 111513070579968), (Int.ofNat 118434764672064), (Int.ofNat 63073462406400), (Int.ofNat 17865003973248), (Int.ofNat 6892927020288)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 286298854559), (Int.negSucc 5803946346815), (Int.negSucc 32817524197535), (Int.negSucc 36500718802751), (Int.negSucc 23193080687231), (Int.negSucc 21953914880255), (Int.negSucc 5556991547519), (Int.negSucc 2157489706751)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 127140640416), (Int.ofNat 3114905639904), (Int.ofNat 8493684929856), (Int.ofNat 3915983314944), (Int.ofNat 3629094067584), (Int.ofNat 1570487025024), (Int.ofNat 188939070720)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 39957878015), (Int.negSucc 864587654783), (Int.negSucc 838130467967), (Int.negSucc 200243446271), (Int.negSucc 188939070719)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5652187776), (Int.ofNat 94469535360)]]

theorem h5n239_arithmetic_row0 :
    (BiPoly.mul h5p5 h5p238).getD 0 []=h5p239.getD 0 [] := by
  decide +kernel

theorem h5n239_arithmetic_row1 :
    (BiPoly.mul h5p5 h5p238).getD 1 []=h5p239.getD 1 [] := by
  decide +kernel

theorem h5n239_arithmetic_row2 :
    (BiPoly.mul h5p5 h5p238).getD 2 []=h5p239.getD 2 [] := by
  decide +kernel

theorem h5n239_arithmetic_row3 :
    (BiPoly.mul h5p5 h5p238).getD 3 []=h5p239.getD 3 [] := by
  decide +kernel

theorem h5n239_arithmetic_row4 :
    (BiPoly.mul h5p5 h5p238).getD 4 []=h5p239.getD 4 [] := by
  decide +kernel

theorem h5n239_arithmetic_row5 :
    (BiPoly.mul h5p5 h5p238).getD 5 []=h5p239.getD 5 [] := by
  decide +kernel

theorem h5n239_arithmetic_row6 :
    (BiPoly.mul h5p5 h5p238).getD 6 []=h5p239.getD 6 [] := by
  decide +kernel

theorem h5n239_arithmetic_row7 :
    (BiPoly.mul h5p5 h5p238).getD 7 []=h5p239.getD 7 [] := by
  decide +kernel

theorem h5n239_arithmetic_row8 :
    (BiPoly.mul h5p5 h5p238).getD 8 []=h5p239.getD 8 [] := by
  decide +kernel

theorem h5n239_arithmetic_row9 :
    (BiPoly.mul h5p5 h5p238).getD 9 []=h5p239.getD 9 [] := by
  decide +kernel

theorem h5n239_arithmetic_row10 :
    (BiPoly.mul h5p5 h5p238).getD 10 []=h5p239.getD 10 [] := by
  decide +kernel

theorem h5n239_arithmetic_row11 :
    (BiPoly.mul h5p5 h5p238).getD 11 []=h5p239.getD 11 [] := by
  decide +kernel

theorem h5n239_arithmetic_row12 :
    (BiPoly.mul h5p5 h5p238).getD 12 []=h5p239.getD 12 [] := by
  decide +kernel

theorem h5n239_arithmetic_row13 :
    (BiPoly.mul h5p5 h5p238).getD 13 []=h5p239.getD 13 [] := by
  decide +kernel

theorem h5n239_arithmetic_row14 :
    (BiPoly.mul h5p5 h5p238).getD 14 []=h5p239.getD 14 [] := by
  decide +kernel

theorem h5n239_arithmetic_row15 :
    (BiPoly.mul h5p5 h5p238).getD 15 []=h5p239.getD 15 [] := by
  decide +kernel

theorem h5n239_arithmetic_row16 :
    (BiPoly.mul h5p5 h5p238).getD 16 []=h5p239.getD 16 [] := by
  decide +kernel

theorem h5n239_arithmetic : BiPoly.mul h5p5 h5p238=h5p239 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p5 h5p238).getD j.val []=h5p239.getD j.val [] :=
      (fun j => Fin.cases h5n239_arithmetic_row0 (fun j => Fin.cases h5n239_arithmetic_row1 (fun j => Fin.cases h5n239_arithmetic_row2 (fun j => Fin.cases h5n239_arithmetic_row3 (fun j => Fin.cases h5n239_arithmetic_row4 (fun j => Fin.cases h5n239_arithmetic_row5 (fun j => Fin.cases h5n239_arithmetic_row6 (fun j => Fin.cases h5n239_arithmetic_row7 (fun j => Fin.cases h5n239_arithmetic_row8 (fun j => Fin.cases h5n239_arithmetic_row9 (fun j => Fin.cases h5n239_arithmetic_row10 (fun j => Fin.cases h5n239_arithmetic_row11 (fun j => Fin.cases h5n239_arithmetic_row12 (fun j => Fin.cases h5n239_arithmetic_row13 (fun j => Fin.cases h5n239_arithmetic_row14 (fun j => Fin.cases h5n239_arithmetic_row15 (fun j => Fin.cases h5n239_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n239 : h5e239.toBi mapPolyEnv=h5p239 := by
  change BiPoly.mul (h5e5.toBi mapPolyEnv) (h5e238.toBi mapPolyEnv)=h5p239
  rw [h5n5, h5n238]
  exact h5n239_arithmetic

#print axioms h5n239_arithmetic
end StackSorting.RationalLift
